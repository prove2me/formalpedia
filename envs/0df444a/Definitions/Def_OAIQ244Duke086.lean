-- Prove2me | Definitions.Def_OAIQ244Duke086
-- name    : OAIQ244Duke086
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T01:30:56.703329+00:00
-- url     : https://prove2.me/theorems/800c4441-6640-42ce-87cf-81f1c3478486
-- title:
--   Definitions bundle OAIQ244Duke086 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 12 definitions and 21 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.includedRelativeIdeleClassNormAdditiveValue`, `GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeFixedFieldIdeleClassEquivFixed`, `GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalFinitePlaceCharacter`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalHeightOneArtinInput`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalHeightOneCharacter`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalHeightOneCharacterFinprod`, `GlobalClassFieldTheory.Reciprocity.rationalNormQuotientIdeleClassCommGroup`, `GlobalClassFieldTheory.Reciprocity.rationalOrdinaryNormQuotientAdditiveType`, `GlobalClassFieldTheory.Reciprocity.rationalPrincipalFinitePlaceInput`, `GlobalClassFieldTheory.Reciprocity.rationalRelativeFixedFieldIdeleClassAdditiveType`, `GlobalClassFieldTheory.Reciprocity.relativeIdeleClassNormAdditiveValue`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Construction`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Core`, `GlobalClassFieldTheory_Reciprocity_GlobalArtin`, `GlobalClassFieldTheory_Reciprocity_GlobalArtinFiniteSupportApproximation`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitAbstractFixedField`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtension`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionAction`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionNorm`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitNormQuotient`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalAwayProduct`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke080`, `OAIQ244Duke081` and `OAIQ244Duke082` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke090`, `OAIQ244Duke091` and `OAIQ244Duke092`.
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
import Mathlib.Combinatorics.Hall.Finite
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
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.NumberTheory.Cyclotomic.Gal
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
import Definitions.Def_OAIQ244Duke080
import Definitions.Def_OAIQ244Duke081
import Definitions.Def_OAIQ244Duke082

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Construction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Construction of finite-place Artin homomorphisms

This module constructs the local Artin map for a chosen extension of a finite place and transports it through the actual decomposition group into the global Galois group.
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
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]

/-- Evaluation of the localized finite-place Artin homomorphism with all
canonical completion data hidden behind named opaque terms.  This is the
normalization API for clients that must not unfold the construction's
dependent instance tower. -/
theorem finitePlaceLocalArtinMonoidHom_apply_normalized
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ) :
    finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x =
      @LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion
          (NumberField.HeightOneSpectrum.adicAbv K v) w)
        (inferInstance : Field
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
        (inferInstance : Field
          (AlgebraicNumberTheory.Valuations.LocalizedCompletion
            (NumberField.HeightOneSpectrum.adicAbv K v) w))
        (finitePlaceLocalArtinLocalizedAlgebra v w)
        (finitePlaceLocalArtinCompletionValuativeRel v)
        (inferInstance : TopologicalSpace
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
        (finitePlaceLocalArtinInput v x) := by
  rfl

/-- Elementwise evaluation of the normalized localized finite-place Artin
map.  This form lets clients transport an action without asking the
elaborator to rewrite an equality of automorphisms carrying a dependent
instance tower. -/
theorem finitePlaceLocalArtinMonoidHom_apply_normalized_at
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : (v.adicCompletion K)ˣ)
    (z : AlgebraicNumberTheory.Valuations.LocalizedCompletion
      (NumberField.HeightOneSpectrum.adicAbv K v) w) :
    finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x z =
      (@LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion
        (AlgebraicNumberTheory.Valuations.LocalizedCompletion
          (NumberField.HeightOneSpectrum.adicAbv K v) w)
        (inferInstance : Field
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
        (inferInstance : Field
          (AlgebraicNumberTheory.Valuations.LocalizedCompletion
            (NumberField.HeightOneSpectrum.adicAbv K v) w))
        (finitePlaceLocalArtinLocalizedAlgebra v w)
        (finitePlaceLocalArtinCompletionValuativeRel v)
        (inferInstance : TopologicalSpace
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
        (finitePlaceLocalArtinInput v x)) z := by
  exact
    congrArg (fun sigma => sigma z)
      (finitePlaceLocalArtinMonoidHom_apply_normalized
        (K := K) (L := L) v w x)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Core
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instLocallyCompactSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Image and kernel of finite-place Artin homomorphisms

This module identifies the image with the chosen decomposition group and the kernel with the chosen local norm subgroup.
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

/-- The image of the chosen finite-place Artin homomorphism is exactly
the chosen decomposition group. -/
theorem chosenFinitePlaceArtinMonoidHom_range
    (v : HeightOneSpectrum (𝓞 K)) :
    (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v).range =
      finitePlaceDecompositionGroup
        (K := K) (L := L) v := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w :=
    chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
  let :=
    LocalClassFieldTheory.localizedCompletionIsScalarTower vK w
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite vK hvK w
  let : IsAbelianGalois vK.Completion E :=
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK hvK w
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField
      vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let : IsUltrametricDist vK.Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
        vK
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
          K v))
  let : Valued vK.Completion ℝ≥0 :=
    NormedField.toValued
  let vC : Valuation vK.Completion ℝ≥0 :=
    Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vK.Completion)).IsNontrivial)
  let : ValuativeRel vK.Completion :=
    ValuativeRel.ofValuation vC
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vK.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  let : IsValuativeTopology vK.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vK.Completion ℝ≥0
  let : IsNonarchimedeanLocalField vK.Completion :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let eD :
      absoluteValueDecompositionGroup K w.1 ≃*
        (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let eK :
      vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  have hsurjective :
      Function.Surjective
        (eD.symm.toMonoidHom.comp
          ((LocalClassFieldTheory.abelianLocalArtinMonoidHom
            vK.Completion E).comp
              eK.symm.toMonoidHom)) :=
    eD.symm.surjective.comp
      ((LocalClassFieldTheory.abelianLocalArtinMonoidHom_surjective
          vK.Completion E).comp
        eK.symm.surjective)
  change
    MonoidHom.range
        ((absoluteValueDecompositionGroup K w.1).subtype.comp
          (eD.symm.toMonoidHom.comp
            ((LocalClassFieldTheory.abelianLocalArtinMonoidHom
              vK.Completion E).comp
                eK.symm.toMonoidHom))) =
      absoluteValueDecompositionGroup K w.1
  rw [
    MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr hsurjective,
    ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalArtin
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The preliminary global Artin homomorphism

For a finite abelian extension `L / K`, the global norm-residue symbol
on ideles is the product of its archimedean and finite-place local
Artin factors.
-/

open scoped BigOperators Classical IsMulCommutative NumberField
  NumberField.LiesOver
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- Every chosen finite-place decomposition group is contained in the
image of the global Artin homomorphism. -/
theorem finitePlaceDecompositionGroup_le_globalArtinMonoidHom_range
    (v : HeightOneSpectrum (𝓞 K)) :
    finitePlaceDecompositionGroup
        (K := K) (L := L) v ≤
      (globalArtinMonoidHom
        (K := K) (L := L)).range := by
  rw [← chosenFinitePlaceArtinMonoidHom_range
    (K := K) (L := L) v]
  intro σ hσ
  rcases hσ with ⟨x, rfl⟩
  exact
    ⟨finitePlaceIdele v x,
      globalArtinMonoidHom_finitePlaceIdele
        (K := K) (L := L) v x⟩

/-- The actual global Artin homomorphism of a finite abelian extension
of number fields is surjective. -/
theorem globalArtinMonoidHom_surjective :
    Function.Surjective
      (globalArtinMonoidHom
        (K := K) (L := L)) := by
  let H : Subgroup (L ≃ₐ[K] L) :=
    (globalArtinMonoidHom
      (K := K) (L := L)).range
  let : H.Normal :=
    H.normal_of_isMulCommutative
  let E : IntermediateField K L :=
    IntermediateField.fixedField H
  let : IsGalois K E := by
    dsimp only [E]
    infer_instance
  have hsplit :
      ∀ v : HeightOneSpectrum (𝓞 K),
        FinitePlaceSplitsCompletely
          (K := K) (L := E) v := by
    intro v
    apply
      _root_.finitePlaceSplitsCompletely_of_decompositionGroup_le_restrictNormalHom_ker
          (K := K) (E := E) (N := L) v
    rw [IntermediateField.restrictNormalHom_ker]
    change
      finitePlaceDecompositionGroup
          (K := K) (L := L) v ≤
        (IntermediateField.fixedField H).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_fixedField]
    simpa only [H] using
      finitePlaceDecompositionGroup_le_globalArtinMonoidHom_range
        (K := K) (L := L) v
  have hfinite :
      {v : HeightOneSpectrum (𝓞 K) |
        ¬ FinitePlaceSplitsCompletelyInExtension
          (K := K) (E := E) v}.Finite := by
    apply Set.finite_empty.subset
    intro v hv
    exact
      (hv
        ((_root_.finitePlaceSplitsCompletely_iff_inExtension
          (K := K) (E := E) v).mp
            (hsplit v))).elim
  have hdegree :
      Module.finrank K E = 1 :=
    Cohomology.finrank_eq_one_of_finite_nonSplittingPlaces
      K E hfinite
  have hEbot :
      E = (⊥ : IntermediateField K L) :=
    IntermediateField.finrank_eq_one_iff.mp hdegree
  have hHtop :
      H = (⊤ : Subgroup (L ≃ₐ[K] L)) := by
    calc
      H =
          (IntermediateField.fixedField H).fixingSubgroup :=
        (IntermediateField.fixingSubgroup_fixedField H).symm
      _ = E.fixingSubgroup := rfl
      _ = (⊥ : IntermediateField K L).fixingSubgroup :=
        congrArg
          (fun F : IntermediateField K L =>
            F.fixingSubgroup)
          hEbot
      _ = ⊤ := by
        rw [IntermediateField.fixingSubgroup_bot]
  apply MonoidHom.range_eq_top.mp
  simpa only [H] using hHtop

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalArtinFiniteSupportApproximation
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Finite-support reduction for the global Artin map

For a finite abelian extension `L / K`, only finitely many finite local
Artin factors of an idele are nontrivial.  Keeping precisely those finite
components, together with every infinite component, gives an idele with
finite one-place support.  The quotient of the original idele by this
approximation is an actual relative-idele norm: outside the retained
finite set this follows from the local Artin kernel theorem, and at the
retained and infinite places it follows because the quotient component is
one.

Consequently both the preliminary global Artin map and the canonical
idele-class norm quotient may be evaluated on this finite-support
approximation.
-/

open scoped NumberField TensorProduct Classical BigOperators
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- Supply the canonical commutativity used by the finite-support norm quotient. -/
theorem artinFiniteSupportIdeleClassIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] artinFiniteSupportIdeleClassIsMulCommutative

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitAbstractFixedField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeEquiv_unramifiedFrobenius _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedRestriction_frobenius _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteAbelianSubextension.normSubgroupMap_val _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.mem_normFilterBasis_iff _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_ideleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom_mk _root_.LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField_apply_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_refl _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Abstract fixed fields in the rational idele-class representation

Fixed-point comparisons for finite-index closed subgroups and their actual
abstract fixed fields.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open CyclicCohomology

/-- The closed-subgroup fixed-field endpoint has the same underlying
direct-limit class as the intermediate-field comparison from which it is
transported. -/
@[simp]
theorem rationalAbstractFixedFieldIdeleClassEquivFixed_coe
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    (c : Additive
      (IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) K))) :
    (rationalAbstractFixedFieldIdeleClassEquivFixed K c).1 =
      (rationalIdeleClassEquivFixed
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) K) c).1 := by
  let : FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K) :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hfinite
  rfl

/-- The relative abstract fixed-field idele class group, identified with
the fixed part at the upper closed subgroup when finite dimensionality is
already available. -/
noncomputable def
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK)]
    [NumberField
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK)] :
    Additive
        (IdeleClassGroup
          (LocalClassFieldTheory.abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) hLK)) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation L := by
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  let hclosed :
      RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) (E.restrictScalars ℚ) =
        L := by
    change
      RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) L) =
        L
    exact
      LocalClassFieldTheory.closedFixingSubgroup_abstractFixedField_eq
        ℚ (SeparableClosure ℚ) L
  exact
    (rationalIdeleClassEquivFixed
      (E.restrictScalars ℚ)).trans
      (AddEquiv.addSubgroupCongr
        (congrArg
          (KummerTheory.ambientFixedAddSubgroup
            rationalIdeleClassRepresentation)
          hclosed))

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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.finiteUnramifiedNormQuotient _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

/-- In the direct-limit fixed-part comparison, one absolute left-coset
action is the idele-class embedding selected by the corresponding
embedding into the canonical normal closure. -/
theorem rationalIdeleClassEquivFixed_relativeCosetAction_coe
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : RelativeIdeleGroup.ClassGroup ℚ K)
    (q :
      (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ))).toSubgroup ⧸
        extensionSubgroup
          (RamificationTheory.closedFixingSubgroup
            ℚ (SeparableClosure ℚ)
            (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
          (RamificationTheory.closedFixingSubgroup
            ℚ (SeparableClosure ℚ) K)
          (LocalClassFieldTheory.fixingSubgroupLeBase
            ℚ (SeparableClosure ℚ) K)) :
    (relativeCosetAction rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
        (LocalClassFieldTheory.fixingSubgroupLeBase
          ℚ (SeparableClosure ℚ) K)
        (rationalIdeleClassEquivFixed K
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c))) q :
      rationalIdeleClassRepresentation.V) =
    Additive.ofMul
      (rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding
          (rationalBaseFixingCosetEquivNormalClosure K q) c)) := by
  let hKN :
      K ≤ (rationalNormalClosure K :
        IntermediateField ℚ (SeparableClosure ℚ)) :=
    IntermediateField.le_normalClosure K
  refine Quotient.inductionOn' q ?_
  intro σ
  have hembedding :
      rationalBaseFixingCosetEquivNormalClosure K
          (QuotientGroup.mk σ) =
        (AlgEquiv.restrictNormalHom
            (rationalNormalClosure K) σ.1).toAlgHom.comp
          (IntermediateField.inclusion
            hKN) := by
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    change
      σ.1 (x : SeparableClosure ℚ) =
        (((AlgEquiv.restrictNormalHom
          (rationalNormalClosure K) σ.1)
            (IntermediateField.inclusion
              hKN x) :
            rationalNormalClosure K) :
          SeparableClosure ℚ)
    exact
      (AlgEquiv.restrictNormal_commutes σ.1
        (rationalNormalClosure K)
        (IntermediateField.inclusion
          hKN x)).symm
  rw [hembedding]
  change
    Additive.ofMul
        (σ.1 •
          rationalIntermediateIdeleClassToDirectLimit K
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c)) =
      Additive.ofMul
        (rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
          (RelativeIdeleGroup.classEmbedding
            ((AlgEquiv.restrictNormalHom
                (rationalNormalClosure K) σ.1).toAlgHom.comp
              (IntermediateField.inclusion
                hKN)) c))
  rw [show
      rationalIntermediateIdeleClassToDirectLimit K
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K) c) =
        (⟦⟨rationalNormalClosure K,
          rationalIntermediateIdeleClassToNormalClosure K
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c)⟩⟧ :
          rationalIdeleClassDirectLimit)
    from rfl,
    DirectLimit.smul_def]
  apply congrArg Additive.ofMul
  apply congrArg
    (fun d :
        RelativeIdeleGroup.ClassGroup ℚ (rationalNormalClosure K) =>
      (⟦⟨rationalNormalClosure K, d⟩⟧ :
        rationalIdeleClassDirectLimit))
  change
    (AlgEquiv.restrictNormalHom
        (rationalNormalClosure K) σ.1) •
      RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hKN)
        ((_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K)).symm
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K) c)) =
      RelativeIdeleGroup.classEmbedding
        ((AlgEquiv.restrictNormalHom
            (rationalNormalClosure K) σ.1).toAlgHom.comp
          (IntermediateField.inclusion
            hKN)) c
  rw [(_root_.relativeIdeleClassBaseChangeMulEquiv
    (K := ℚ) (L := K)).symm_apply_apply]
  exact
    rationalRelativeIdeleClassEmbedding_smul_eq_classEmbedding
      hKN σ.1 c

/-- The abstract class-formation norm in the rational idele-class
direct limit is the ordinary relative idele-class norm, embedded at the
canonical normal closure. -/
theorem rationalIdeleClassEquivFixed_relativeNorm_coe
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : RelativeIdeleGroup.ClassGroup ℚ K) :
    (relativeNorm rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
        (LocalClassFieldTheory.fixingSubgroupLeBase
          ℚ (SeparableClosure ℚ) K)
        (rationalIdeleClassEquivFixed K
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c))) :
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))).1 =
      Additive.ofMul
        (rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
          (RelativeIdeleGroup.classInclusion
            ℚ (rationalNormalClosure K)
            (RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ K c))) := by
  classical
  let : Algebra K (rationalNormalClosure K) :=
    (IntermediateField.inclusion
      (IntermediateField.le_normalClosure K)).toRingHom.toAlgebra
  let : IsScalarTower ℚ K (rationalNormalClosure K) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let Q :=
    (RamificationTheory.closedFixingSubgroup
        ℚ (SeparableClosure ℚ)
        (⊥ : IntermediateField ℚ (SeparableClosure ℚ))).toSubgroup ⧸
      extensionSubgroup
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
        (LocalClassFieldTheory.fixingSubgroupLeBase
          ℚ (SeparableClosure ℚ) K)
  let := Fintype.ofFinite Q
  let term : Q → Additive rationalIdeleClassDirectLimit :=
    fun q =>
      (relativeCosetAction rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
        (LocalClassFieldTheory.fixingSubgroupLeBase
          ℚ (SeparableClosure ℚ) K)
        (rationalIdeleClassEquivFixed K
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c))) q :
        Additive rationalIdeleClassDirectLimit)
  have hterm (q : Q) :
      Additive.toMul (term q) =
        rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
          (RelativeIdeleGroup.classEmbedding
            (rationalBaseFixingCosetEquivNormalClosure K q) c) := by
    have h :=
      congrArg Additive.toMul
        (rationalIdeleClassEquivFixed_relativeCosetAction_coe
          K c q)
    exact h.trans (toMul_ofMul _)
  apply Additive.toMul.injective
  change
    Additive.toMul (∑ q : Q, term q) =
      rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classInclusion
          ℚ (rationalNormalClosure K)
          (RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ K c))
  rw [toMul_sum]
  calc
    ∏ q : Q,
        Additive.toMul (term q) =
        ∏ q : Q,
          rationalRelativeIdeleClassToDirectLimit
            (rationalNormalClosure K)
            (RelativeIdeleGroup.classEmbedding
              (rationalBaseFixingCosetEquivNormalClosure K q) c) := by
      apply Finset.prod_congr rfl
      intro q _
      exact hterm q
    _ =
        rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
          (∏ q : Q,
            RelativeIdeleGroup.classEmbedding
              (rationalBaseFixingCosetEquivNormalClosure K q) c) := by
      let g :=
        rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
      let f := fun q : Q =>
        RelativeIdeleGroup.classEmbedding
          (rationalBaseFixingCosetEquivNormalClosure K q) c
      have hmap (s : Finset Q) :
          g (s.prod f) =
            s.prod (fun q => g (f q)) := by
        induction s using Finset.induction_on with
        | empty =>
            exact g.map_one
        | @insert q s hqs ih =>
            rw [Finset.prod_insert hqs, Finset.prod_insert hqs,
              g.map_mul, ih]
      change
        (∏ q : Q, g (f q)) =
          g (∏ q : Q, f q)
      exact (hmap Finset.univ).symm
    _ =
        rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
          (∏ f : K →ₐ[ℚ] rationalNormalClosure K,
            RelativeIdeleGroup.classEmbedding f c) := by
      apply congrArg
        (rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K))
      exact
        Fintype.prod_equiv
          (rationalBaseFixingCosetEquivNormalClosure K)
          (fun q : Q =>
            RelativeIdeleGroup.classEmbedding
              (rationalBaseFixingCosetEquivNormalClosure K q) c)
          (fun f : K →ₐ[ℚ] rationalNormalClosure K =>
            RelativeIdeleGroup.classEmbedding f c)
          (fun _ => rfl)
    _ =
        rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
          (RelativeIdeleGroup.classInclusion
            ℚ (rationalNormalClosure K)
            (RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ K c)) := by
      apply congrArg
        (rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K))
      have hnorm :
          RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ K c =
            RelativeIdeleGroup.classNorm ℚ K c := by
        refine QuotientGroup.induction_on c ?_
        intro a
        rfl
      calc
        (∏ f : K →ₐ[ℚ] rationalNormalClosure K,
            RelativeIdeleGroup.classEmbedding f c) =
            RelativeIdeleGroup.classInclusion
              ℚ (rationalNormalClosure K)
              (RelativeIdeleGroup.classNorm ℚ K c) :=
          (RelativeIdeleGroup.classInclusion_ideleClassNorm_eq_prod_embeddings
            c).symm
        _ =
            RelativeIdeleGroup.classInclusion
              ℚ (rationalNormalClosure K)
              (RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ K c) := by
          rw [hnorm]

/-- For a finite abstract rational field, the abstract norm to the base
has the ordinary relative idele-class norm as its underlying direct-limit
class.  The two closed-subgroup indices are transported through their
actual fixed fields; no new norm is introduced. -/
theorem
    rationalAbstractFixedFieldIdeleClassEquivFixed_normToBase_coe
    (H : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H (le_baseField H))]
    (c : RelativeIdeleGroup.ClassGroup ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H)) :
    (normToBase rationalIdeleClassRepresentation H
        (rationalAbstractFixedFieldIdeleClassEquivFixed H
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ)
              (L := LocalClassFieldTheory.abstractFixedField
                ℚ (SeparableClosure ℚ) H) c))) :
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))).1 =
      Additive.ofMul
        (rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure
            (LocalClassFieldTheory.abstractFixedField
              ℚ (SeparableClosure ℚ) H))
          (RelativeIdeleGroup.classInclusion
            ℚ
            (rationalNormalClosure
              (LocalClassFieldTheory.abstractFixedField
                ℚ (SeparableClosure ℚ) H))
            (RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ
              (LocalClassFieldTheory.abstractFixedField
                ℚ (SeparableClosure ℚ) H) c))) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H hfinite
  let x :
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) F) :=
    rationalIdeleClassEquivFixed F
      (Additive.ofMul
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c))
  let x' :
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H :=
    rationalAbstractFixedFieldIdeleClassEquivFixed H
      (Additive.ofMul
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c))
  have hx : x.1 = x'.1 := by
    simpa only [x, x', F] using
      (rationalAbstractFixedFieldIdeleClassEquivFixed_coe H
        (Additive.ofMul
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) c))).symm
  have htransport :=
    LocalClassFieldTheory.relativeNorm_coe_eq_of_closedSubgroup_eq
      rationalIdeleClassRepresentation
      (RamificationTheory.closedFixingSubgroup
        ℚ (SeparableClosure ℚ)
        (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
      (baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
      (RamificationTheory.closedFixingSubgroup
        ℚ (SeparableClosure ℚ) F)
      H
      (LocalClassFieldTheory.fixingSubgroupLeBase
        ℚ (SeparableClosure ℚ) F)
      (le_baseField H)
      (LocalClassFieldTheory.closedFixingSubgroup_bot_eq_baseField
        ℚ (SeparableClosure ℚ))
      (LocalClassFieldTheory.closedFixingSubgroup_abstractFixedField_eq
        ℚ (SeparableClosure ℚ) H)
      x x' hx
  exact htransport.symm.trans
    (rationalIdeleClassEquivFixed_relativeNorm_coe F c)

section AbstractFixedFieldOrdinaryNorm

variable
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))

local instance rationalFiniteAbstractField_quotient_finite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H.field (le_baseField H.field)) :=
  H.finite

/-- Pulling the abstract base norm of an actual fixed-field idele class
back through the distinguished rational fixed-part equivalence is the
ordinary idele-class norm of that class. -/
theorem
    rationalAbstractFixedFieldNormToBase_eq_ordinaryIdeleClassNorm
    (c : Additive
      (IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))) :
    rationalIdeleClassEquivBaseFixed.symm
        (normToBase rationalIdeleClassRepresentation H.field
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            H.field c)) =
      Additive.ofMul
        (_root_.ideleClassNorm ℚ
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field)
          (Additive.toMul c)) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let d : RelativeIdeleGroup.ClassGroup ℚ F :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := F)).symm (Additive.toMul c)
  have hc :
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) d =
        Additive.toMul c := by
    simpa only [d] using
      ((_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := F)).apply_symm_apply
        (Additive.toMul c))
  have hcoe :
      (normToBase rationalIdeleClassRepresentation H.field
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            H.field c) :
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))).1 =
        Additive.ofMul
          (rationalRelativeIdeleClassToDirectLimit
            (rationalNormalClosure F)
            (RelativeIdeleGroup.classInclusion ℚ
              (rationalNormalClosure F)
              (RelativeIdeleGroup.Cohomology.ideleClassNorm
                ℚ F d))) := by
    have h :=
      rationalAbstractFixedFieldIdeleClassEquivFixed_normToBase_coe
        H.field d
    have hcAdd :
        Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := F) d) =
          c := by
      simpa only [ofMul_toMul] using congrArg Additive.ofMul hc
    rw [hcAdd] at h
    exact h
  have hordinary :
      _root_.ideleClassNorm ℚ F (Additive.toMul c) =
        RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ F d := by
    rw [← hc]
    exact
      ordinaryIdeleClassNorm_relativeIdeleClassBaseChange d
  have hbase :=
    rationalIdeleClassEquivBaseFixed_coe
      (rationalNormalClosure F)
      (_root_.ideleClassNorm ℚ F (Additive.toMul c))
  have hcoe' := hcoe.trans
    (congrArg
      (fun x : IdeleClassGroup ℚ =>
        Additive.ofMul
          (rationalRelativeIdeleClassToDirectLimit
            (rationalNormalClosure F)
            (RelativeIdeleGroup.classInclusion ℚ
              (rationalNormalClosure F) x)))
      hordinary.symm)
  apply rationalIdeleClassEquivBaseFixed.injective
  calc
    rationalIdeleClassEquivBaseFixed
        (rationalIdeleClassEquivBaseFixed.symm
          (normToBase rationalIdeleClassRepresentation H.field
            (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c))) =
      normToBase rationalIdeleClassRepresentation H.field
        (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c) :=
      rationalIdeleClassEquivBaseFixed.apply_symm_apply _
    _ = rationalIdeleClassEquivBaseFixed
        (Additive.ofMul
          (_root_.ideleClassNorm ℚ F (Additive.toMul c))) := by
      apply Subtype.ext
      exact hcoe'.trans hbase.symm

end AbstractFixedFieldOrdinaryNorm

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

theorem relativeIdeleClassBaseChangeAddEquiv_apply
    (E : Type) [Field E] [NumberField E]
    (c : Additive (RelativeIdeleGroup.ClassGroup ℚ E)) :
    (MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))) c =
      Additive.ofMul
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) (Additive.toMul c)) := by
  rfl

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms on rational fixed-field idele classes

Compatibility of fixed-field inclusion and relative norm with the actual
idele-class extension attached to the abstract subgroup tower.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

noncomputable def relativeIdeleClassNormAdditiveValue
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (c : Additive (RelativeIdeleGroup.ClassGroup F E)) :
    Additive (IdeleClassGroup F) :=
  Additive.ofMul
    (RelativeIdeleGroup.Cohomology.ideleClassNorm F E
      (Additive.toMul c))

noncomputable def includedRelativeIdeleClassNormAdditiveValue
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (c : Additive (RelativeIdeleGroup.ClassGroup F E)) :
    Additive (RelativeIdeleGroup.ClassGroup F E) :=
  Additive.ofMul
    (RelativeIdeleGroup.classInclusion F E
      (RelativeIdeleGroup.Cohomology.ideleClassNorm F E
        (Additive.toMul c)))

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitNormQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

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

local instance
    rationalNormQuotientIdeleClassGroupIsMulCommutative_r85442a_1
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
local instance
    rationalNormQuotientIdeleClassSubgroupNormal_r85442a_1
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative
@[instance_reducible]
noncomputable def rationalNormQuotientIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  open scoped IsMulCommutative in
    inferInstance

noncomputable abbrev rationalRelativeFixedFieldIdeleClassAdditiveType
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] : Type :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField E :=
    NumberField.of_module_finite ℚ E
  Additive (IdeleClassGroup E)

noncomputable abbrev rationalOrdinaryNormQuotientAdditiveType
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] : Type :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  letI :=
    rationalNormQuotientNumberFieldOfFiniteDimensional F
  letI :=
    rationalNormQuotientNumberFieldOfFiniteDimensional E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  Additive
    (IdeleClassGroup F ⧸ (_root_.ideleClassNorm F E).range)

/-- The ordinary idele class group of the upper fixed field, identified
directly with the corresponding fixed part of the rational absolute
idele-class representation.  Unlike
`rationalAbstractExtensionIdeleClassEquiv`, this comparison does not
package a Galois action and therefore does not require normality. -/
noncomputable def
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    rationalRelativeFixedFieldIdeleClassAdditiveType
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation L := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K
  let E :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField E :=
    NumberField.of_module_finite ℚ E
  change Additive (IdeleClassGroup E) ≃+
    KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L
  exact
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.relativeUnrestrictedSPlaceFactorCommGroup
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
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseLocallyCompactSpace
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsUltrametricDist
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValued
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRel
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationCompatible
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRelIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionRatAlgebra
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_r85442a_1
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsNonarchimedeanLocalField
/-- The source unit in the absolute-value completion represented by the
finite component of a rational principal idele. -/
noncomputable def rationalPrincipalFinitePlaceInput
    (x : ℚˣ) (q : Nat.Primes) :
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completionˣ :=
  (finitePlaceCompletionUnitsContinuousMulEquiv
      (RayClass.rationalPrime q)).symm
    (IdeleGroup.finiteComponent
      (RayClass.rationalPrime q)
      (IdeleGroup.principalIdele ℚ x))

/-- The source unit represented by a principal finite component is the
ordinary image of the rational field unit in the absolute-value
completion. -/
theorem rationalPrincipalFinitePlaceInput_eq_algebraMap
    (x : ℚˣ) (q : Nat.Primes) :
    rationalPrincipalFinitePlaceInput x q =
      Units.map
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion).toMonoidHom
        x := by
  apply Units.ext
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    RayClass.rationalPrime q
  let vQ := HeightOneSpectrum.adicAbv ℚ v
  let component : (v.adicCompletion ℚ)ˣ :=
    IdeleGroup.finiteComponent v
      (IdeleGroup.principalIdele ℚ x)
  apply (finitePlaceCompletionRingEquiv v).injective
  change
    finitePlaceCompletionRingEquiv v
        (rationalPrincipalFinitePlaceInput x q : vQ.Completion) =
      finitePlaceCompletionRingEquiv v
        (algebraMap ℚ vQ.Completion (x : ℚ))
  have hCompletion :
      finitePlaceCompletionRingEquiv v
          (rationalPrincipalFinitePlaceInput x q :
            vQ.Completion) =
        (component : v.adicCompletion ℚ) := by
    have hUnits :=
      congrArg Units.val
        ((finitePlaceCompletionUnitsContinuousMulEquiv v).apply_symm_apply
          component)
    exact hUnits
  have hComponent :
      (component : v.adicCompletion ℚ) =
        algebraMap ℚ (v.adicCompletion ℚ) (x : ℚ) := by
    apply (Padic.adicCompletionEquiv (𝓞 ℚ) q).symm.injective
    calc
      (Padic.adicCompletionEquiv (𝓞 ℚ) q).symm
          (component : v.adicCompletion ℚ) =
        algebraMap ℚ ℚ_[q.1] (x : ℚ) := by
          dsimp only [component]
          rw [IdeleGroup.finiteComponent_principalIdele]
          exact
            (Padic.adicCompletionEquiv
              (𝓞 ℚ) q).symm.commutes (x : ℚ)
      _ = (Padic.adicCompletionEquiv (𝓞 ℚ) q).symm
          (algebraMap ℚ (v.adicCompletion ℚ) (x : ℚ)) := by
        symm
        exact
          (Padic.adicCompletionEquiv
            (𝓞 ℚ) q).symm.commutes (x : ℚ)
  calc
    finitePlaceCompletionRingEquiv v
        (rationalPrincipalFinitePlaceInput x q :
          vQ.Completion) =
      (component : v.adicCompletion ℚ) := hCompletion
    _ = algebraMap ℚ (v.adicCompletion ℚ) (x : ℚ) := hComponent
    _ = finitePlaceCompletionRingEquiv v
        (algebraMap ℚ vQ.Completion (x : ℚ)) := by
      symm
      exact
        (finitePlaceCompletionAlgEquiv (K := ℚ) v).commutes (x : ℚ)

/-- The normalized local exponent of a rational principal finite
component is the negative of the usual `q`-adic exponent.  The minus sign
records the inverse-standard local reciprocity convention in which a
prime element has normalized value `-1`. -/
theorem rationalPrincipalFiniteComponent_valuationMap
    (x : ℚˣ) (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          ((finitePlaceCompletionUnitsContinuousMulEquiv
            (RayClass.rationalPrime q)).symm
            (IdeleGroup.finiteComponent
              (RayClass.rationalPrime q)
              (IdeleGroup.principalIdele ℚ x)))) =
      -padicValRat q.1 (x : ℚ) := by
  let F :=
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion
  let embed : ℚˣ →* Fˣ :=
    Units.map (algebraMap ℚ F).toMonoidHom
  let primeUnit : Fˣ :=
    rationalPrimeFinitePlaceFieldUnit q
  let integralUnit : 𝒪[F]ˣ :=
    rationalPrimeUnitFinitePlaceIntegerUnit x q
  let unitPart : Fˣ :=
    IsNonarchimedeanLocalField.integerUnitsToFieldUnits
      F integralUnit
  have hInput :
      rationalPrincipalFinitePlaceInput x q =
        embed x := by
    exact rationalPrincipalFinitePlaceInput_eq_algebraMap x q
  have hPrime :
      embed (rationalPrimeGeneratorUnit q) =
        primeUnit := by
    apply Units.ext
    exact
      (rationalPrimeFinitePlaceInteger_coe q).symm
  have hUnit :
      embed (rationalPrimeUnit x q) =
        unitPart := by
    apply Units.ext
    exact
      (rationalPrimeUnitFinitePlaceIntegerUnit_coe
        x q).symm
  change
    IsNonarchimedeanLocalField.valuationMap F
        (Additive.ofMul
          (rationalPrincipalFinitePlaceInput x q)) =
      -padicValRat q.1 (x : ℚ)
  rw [hInput]
  conv_lhs =>
    rw [← rationalPrimeGeneratorUnit_zpow_mul_rationalPrimeUnit
      x q]
  rw [map_mul, map_zpow, hPrime, hUnit,
    IsNonarchimedeanLocalField.valuationMap_ofMul_mul,
    IsNonarchimedeanLocalField.valuationMap_ofMul_zpow,
    rationalPrimeFinitePlaceFieldUnit_valuationMap,
    rationalPrimeUnitFinitePlaceField_valuationMap]
  ring

section RationalCyclotomicPrincipalPrime

/-! ## Ramified prime-power transport

This section reuses the canonical finite-place Artin tower above.  In
particular, it introduces no parallel completion/localization instance tower. -/

/-! ## The ramified principal finite-place factor -/

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
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_r85442a_2
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
    rationalCyclotomicArtinLocalizedIsUltrametricDist_r85442a_1
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
    rationalCyclotomicPrincipalPrimeLevelIsCyclotomicExtension_r85442a_1
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
/-- The chosen finite-place Artin map factors through any extension identified
with the chosen one. -/
theorem chosenFinitePlaceArtinMonoidHom_apply_factor_of_extension_eq
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (hw : chosenFinitePlaceExtension (L := L) v = w)
    (x : (v.adicCompletion K)ˣ) :
    chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x =
      finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w x) := by
  subst w
  exact
    congrArg
      (fun f : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) => f x)
      (finitePlaceArtinMonoidHomOfExtension_factor
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v))

end RationalCyclotomicPrincipalPrime

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalAwayProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_isCyclotomic _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Away-from-p factors of a rational cyclotomic principal idele

For the cyclotomic level `p ^ k`, this file reindexes the actual chosen
finite-place Artin characters over rational primes.  Away from `p`, the
unramified formula makes the multiplicative support lie in the ordinary
finite prime factorization support of the principal rational number.

The final theorem separates the genuine `p`-factor from the explicit
away-from-`p` finite product.  The construction also applies to `k = 0`.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open Function

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_3
local instance instNeZeroNatVal_solutions_1_r85442a_1 (m : ℕ+) : NeZero (m : ℕ) :=
  ⟨m.ne_zero⟩
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalPrimePowerNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalPrimePowerFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalPrimePowerIsGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalPrimePowerIsAbelianGalois
noncomputable local instance
    rationalCyclotomicPrincipalLevelFiniteDimensional_r85442a_1
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional m
noncomputable local instance
    rationalCyclotomicPrincipalLevelIsAbelianGalois_r85442a_1
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelIsAbelianGalois m
noncomputable def rationalCyclotomicPrincipalHeightOneArtinInput
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩ ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩ :=
  chosenFinitePlaceArtinMonoidHom
    (K := ℚ)
    (L :=
      KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
    v
    (IdeleGroup.finiteComponent v
      (IdeleGroup.principalIdele ℚ x))

theorem rationalCyclotomicPrincipalHeightOneArtinInput_spec
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    rationalCyclotomicPrincipalHeightOneArtinInput p k x v =
      chosenFinitePlaceArtinMonoidHom
        (K := ℚ)
        (L :=
          KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        v
        (IdeleGroup.finiteComponent v
          (IdeleGroup.principalIdele ℚ x)) := by
  rfl

noncomputable def rationalCyclotomicPrincipalHeightOneCharacter
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (ZMod (p.1 ^ k))ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod
    (p.1 ^ k)
    (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
    (hK :=
      KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
    (rationalCyclotomicPrincipalHeightOneArtinInput p k x v)

/-- The named height-one character is the cyclotomic coordinate of the
chosen finite-place Artin symbol. -/
theorem rationalCyclotomicPrincipalHeightOneCharacter_spec
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    rationalCyclotomicPrincipalHeightOneCharacter p k x v =
      IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ k)
        (KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L :=
            KummerTheory.rationalCyclotomicLevel
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          v
          (IdeleGroup.finiteComponent v
            (IdeleGroup.principalIdele ℚ x))) := by
  rw [rationalCyclotomicPrincipalHeightOneCharacter,
    rationalCyclotomicPrincipalHeightOneArtinInput_spec]

/-- The genuine chosen finite-place Artin character of the rational
principal idele at the prime `q`, evaluated in the `p ^ k` cyclotomic
coordinate. -/
noncomputable def rationalCyclotomicPrincipalFinitePlaceCharacter
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) (q : Nat.Primes) :
    (ZMod (p.1 ^ k))ˣ :=
  rationalCyclotomicPrincipalHeightOneCharacter p k x
    ((Rat.HeightOneSpectrum.primesEquiv
      (R := 𝓞 ℚ)).symm q)

theorem rationalCyclotomicPrincipalFinitePlaceCharacter_spec
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) (q : Nat.Primes) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x q =
      rationalCyclotomicPrincipalHeightOneCharacter p k x
        ((Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ)).symm q) := by
  rfl

noncomputable def rationalCyclotomicPrincipalHeightOneCharacterFinprod
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    (ZMod (p.1 ^ k))ˣ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
    rationalCyclotomicPrincipalHeightOneCharacter p k x v

theorem
    rationalCyclotomicPrincipalHeightOneCharacterFinprod_eq_finprod
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalHeightOneCharacterFinprod p k x =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        rationalCyclotomicPrincipalHeightOneCharacter p k x v := by
  rfl

theorem rationalCyclotomicPrincipalHeightOneCharacterFinprod_spec
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalHeightOneCharacterFinprod p k x =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        IsCyclotomicExtension.Rat.galEquivZMod
          (p.1 ^ k)
          (KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (hK :=
            KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (chosenFinitePlaceArtinMonoidHom
            (K := ℚ)
            (L :=
              KummerTheory.rationalCyclotomicLevel
                ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
            v
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele ℚ x))) := by
  calc
    rationalCyclotomicPrincipalHeightOneCharacterFinprod p k x =
        ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
          rationalCyclotomicPrincipalHeightOneCharacter p k x v :=
      rationalCyclotomicPrincipalHeightOneCharacterFinprod_eq_finprod p k x
    _ = _ := by
      apply finprod_congr
      intro v
      exact rationalCyclotomicPrincipalHeightOneCharacter_spec p k x v

end Reciprocity
end GlobalClassFieldTheory
end
end


