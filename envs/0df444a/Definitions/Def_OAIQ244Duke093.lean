-- Prove2me | Definitions.Def_OAIQ244Duke093
-- name    : OAIQ244Duke093
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T01:52:28.665391+00:00
-- url     : https://prove2.me/theorems/b5e0df93-166b-4b7a-bcc3-1a0717bef31e
-- title:
--   Definitions bundle OAIQ244Duke093 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 3 definitions, 14 instances and 17 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.compRestrictNormalHomInfiniteGlobalArtinRationalCyclotomicDataOfNumberField`, `GlobalClassFieldTheory.Reciprocity.rationalComplexificationCharacter`, `LubinTate.padicCompletedStandardChangedCompositumResidueEmbedding`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification`, `GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionAction`, `GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin`, `LubinTate_Padic_CompletedChangedStandardResidue`, `LubinTate_Padic_CompletedResidueFrobenius`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke088`, `OAIQ244Duke089` and `OAIQ244Duke090` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke095` and `OAIQ244Duke118`.
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
import Definitions.Def_OAIQ244Duke088
import Definitions.Def_OAIQ244Duke089
import Definitions.Def_OAIQ244Duke090

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedChangedStandardResidue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional_over_extension _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_finiteDimensional_over_K _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsNonarchimedeanLocalField _root_.chosenFinitePlaceBaseNontriviallyNormedField _root_.chosenFinitePlaceBaseValuativeRel _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuativeRel _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Residue embedding for the completed standard/changed compositum

The finite standard/changed compositum is realized inside the completed
Lubin--Tate level.  Uniqueness of the finite extension of the p-adic
valuation therefore gives a canonical injection from its residue field into
the residue field of the ambient completed level.

This injection is the faithful comparison map used to identify the finite
relative Artin candidate with inverse arithmetic Frobenius.
-/

noncomputable section

namespace LubinTate

open scoped ValuativeRel

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The actual finite changed-uniformizer Lubin--Tate level is totally
ramified, hence its residue field is still `𝔽_p`. -/
theorem padicChangedUniformizerLevelResidueField_card
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let hπ :=
      standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u
    Nat.card
        (standardLubinTateLevelCompleteDVF hπ n).residueField =
      p := by
  let F := padicLocalField p
  have h₀ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      h₀ u
  let base := F.toCompleteDVF
  let target := standardLubinTateLevelCompleteDVF hπ n
  let d := degree base.toDVF target.toDVF
  let f := residueDegree base.toDVF target.toDVF
  have hbaseCard : Nat.card base.residueField = p := by
    change Nat.card (padicCompleteDVF p).residueField = p
    exact padicCompleteDVF_residueField_card p
  have hd : 0 < d := by
    rw [show d =
        Module.finrank ℚ_[p]
          (standardLubinTateLevelField hπ n) by
      rfl,
      standardLubinTateLevelField_finrank hπ n,
      hbaseCard]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
      (Nat.pow_pos (Fact.out : p.Prime).pos)
  have hf : f = 1 := by
    have hfund :=
      standardLubinTateLevelCompleteDVF_fundamentalIdentity hπ n
    rw [standardLubinTateLevel_ramificationIndex_eq_degree hπ n]
      at hfund
    apply Nat.eq_of_mul_eq_mul_left hd
    simpa only [mul_one, d, f] using hfund.symm
  let : FiniteDimensional base.residueField target.residueField :=
    residueField_finiteDimensional_of_moduleFinite base target
  have hfinrank :
      f = Module.finrank base.residueField target.residueField := by
    exact residueDegree_eq_finrank_quotient base target
  calc
    Nat.card target.residueField =
        Nat.card base.residueField ^
          Module.finrank base.residueField target.residueField :=
      Module.natCard_eq_pow_finrank
    _ = Nat.card base.residueField ^ f := by
      rw [← hfinrank]
    _ = p := by rw [hf, pow_one, hbaseCard]

/-- The completed changed-uniformizer fixed field has residue field
cardinality `p`.  The proof transports the residue field in both directions
along the genuine equivalence with the finite changed Lubin--Tate level and
uses uniqueness of finite extensions of the p-adic valuation. -/
theorem padicCompletedChangedUniformizerFixedField_residueField_card
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    letI : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    Nat.card (localCompleteDVF D).residueField = p := by
  let F := padicLocalField p
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let L := standardLubinTateLevelField hπ n
  let D := padicCompletedChangedUniformizerFixedField p u n
  let padicBase := F.toCompleteDVF
  let targetL := standardLubinTateLevelCompleteDVF hπ n
  let e : L ≃ₐ[ℚ_[p]] D :=
    padicChangedUniformizerLevelEquivCompletedFixedField p u n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  let : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  let : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let targetD := localCompleteDVF D
  let :
      Valuation.HasExtension (ValuativeRel.valuation ℚ_[p])
        (ValuativeRel.valuation D) :=
    finiteExtensionSpectralValuation_hasExtension ℚ_[p] D
  let :
      (localCompleteDVF ℚ_[p]).valuation.HasExtension
        targetD.valuation :=
    localCompleteDVFValuation_hasExtension ℚ_[p] D
  let : padicBase.valuation.HasExtension targetD.valuation :=
    padicLocalFieldValuation_hasExtension_of_localCompleteDVF
      p targetD.valuation
  let inclusionLD : L →+* D := e.toRingHom
  have inclusionLD_comp :
      inclusionLD.comp (algebraMap ℚ_[p] L) =
        algebraMap ℚ_[p] D := by
    apply RingHom.ext
    intro x
    exact e.commutes x
  let :
      padicBase.valuation.HasExtension
        (targetD.valuation.comap inclusionLD) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusionLD inclusionLD_comp
  have hEquivLD :
      targetL.valuation.IsEquiv
        (targetD.valuation.comap inclusionLD) :=
    valuation_isEquiv_of_finite_separable
      padicBase targetL (targetD.valuation.comap inclusionLD)
  let residueLD : targetL.residueField →+* targetD.residueField :=
    residueFieldMapOfIsEquivComap
      targetL.valuation targetD.valuation inclusionLD hEquivLD
  let inclusionDL : D →+* L := e.symm.toRingHom
  have inclusionDL_comp :
      inclusionDL.comp (algebraMap ℚ_[p] D) =
        algebraMap ℚ_[p] L := by
    apply RingHom.ext
    intro x
    exact e.symm.commutes x
  let :
      padicBase.valuation.HasExtension
        (targetL.valuation.comap inclusionDL) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusionDL inclusionDL_comp
  have hEquivDL :
      targetD.valuation.IsEquiv
        (targetL.valuation.comap inclusionDL) :=
    valuation_isEquiv_of_finite_separable
      padicBase targetD (targetL.valuation.comap inclusionDL)
  let residueDL : targetD.residueField →+* targetL.residueField :=
    residueFieldMapOfIsEquivComap
      targetD.valuation targetL.valuation inclusionDL hEquivDL
  let : FiniteDimensional padicBase.residueField targetL.residueField :=
    residueField_finiteDimensional_of_moduleFinite
      padicBase targetL
  let : Finite padicBase.residueField := by
    change Finite (padicCompleteDVF p).residueField
    exact padicCompleteDVF_residueField_finite p
  let : Finite targetL.residueField :=
    Module.finite_of_finite padicBase.residueField
  let : Finite targetD.residueField := by
    change Finite 𝓀[D]
    infer_instance
  have hLD :
      Nat.card targetL.residueField ≤ Nat.card targetD.residueField :=
    Nat.card_le_card_of_injective residueLD residueLD.injective
  have hDL :
      Nat.card targetD.residueField ≤ Nat.card targetL.residueField :=
    Nat.card_le_card_of_injective residueDL residueDL.injective
  calc
    Nat.card targetD.residueField =
        Nat.card targetL.residueField :=
      le_antisymm hDL hLD
    _ = p :=
      padicChangedUniformizerLevelResidueField_card p u n

/-- Relative residue arithmetic Frobenius for the finite
standard/changed compositum is the `p`-power map. -/
theorem
    padicCompletedStandardChangedCompositum_residueArithmeticFrobenius_apply
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
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
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
    let :
        Valuation.HasExtension (ValuativeRel.valuation D)
          (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower
        ℚ_[p] D M
    ∀ x : IsLocalRing.ResidueField
        (localCompleteDVF M).valuation.valuationSubring,
      residueExtensionArithmeticFrobeniusOfValuationExtension
          D M x =
        x ^ p := by
  dsimp only
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
    finiteExtensionSpectralValuation_hasExtension_of_tower
      ℚ_[p] D M
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
  have hcard :=
    padicCompletedChangedUniformizerFixedField_residueField_card p u n
  dsimp only at hcard
  have hcardRaw : Nat.card 𝓀[D] = p := by
    rw [← hD]
    exact hcard
  cases hM
  cases hD
  intro x
  exact
    (residueExtensionArithmeticFrobeniusOfValuationExtension_apply D M
      (show 𝓀[M] from x)).trans
      (congrArg (fun k : ℕ => (show 𝓀[M] from x) ^ k) hcardRaw)

/-- The residue field of the finite standard/changed compositum embeds into
the residue field of the ambient completed Lubin--Tate level. -/
noncomputable def
    padicCompletedStandardChangedCompositumResidueEmbedding
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let M := padicCompletedStandardChangedCompositum p u n
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField ℚ_[p] M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel ℚ_[p] M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
    IsLocalRing.ResidueField
        (localCompleteDVF M).valuationSubring →+*
      IsLocalRing.ResidueField
        (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let M := padicCompletedStandardChangedCompositum p u n
  let E := padicCompletedLevelField p n
  let padicBase := (padicLocalField p).toCompleteDVF
  let canonicalBase := localCompleteDVF ℚ_[p]
  let coefficient := padicCompletedUnramifiedCompleteDVF p
  let ambient := padicCompletedLevelCompleteDVF p n
  letI : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField ℚ_[p] M
  letI : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel ℚ_[p] M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
  let :
      Valuation.HasExtension (ValuativeRel.valuation ℚ_[p])
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension ℚ_[p] M
  let :
      canonicalBase.valuation.HasExtension
        (localCompleteDVF M).valuation :=
    localCompleteDVFValuation_hasExtension ℚ_[p] M
  let : padicBase.valuation.HasExtension coefficient.valuation :=
    padicCompletedUnramifiedValuation_hasExtension p
  let : coefficient.valuation.HasExtension ambient.valuation :=
    padicCompletedLevelCompleteDVF_hasExtension p n
  let : padicBase.valuation.HasExtension ambient.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.hasExtension_trans
      padicBase.valuation coefficient.valuation
      ambient.valuation
  let :
      canonicalBase.valuation.HasExtension ambient.valuation :=
    localCompleteDVFValuation_hasExtension_of_padicLocalField
      p ambient.valuation
  let inclusion : M →+* E := M.val.toRingHom
  have inclusion_comp :
      inclusion.comp (algebraMap ℚ_[p] M) =
        algebraMap ℚ_[p] E := by
    ext x
    exact M.val.commutes x
  let :
      canonicalBase.valuation.HasExtension
        (ambient.valuation.comap inclusion) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusion inclusion_comp
  have hEquiv :
      (localCompleteDVF M).valuation.IsEquiv
        (ambient.valuation.comap inclusion) :=
    valuation_isEquiv_of_finite_separable
      canonicalBase (localCompleteDVF M)
        (ambient.valuation.comap inclusion)
  exact
    residueFieldMapOfIsEquivComap
      (localCompleteDVF M).valuation ambient.valuation
      inclusion hEquiv

/-- The finite standard/changed compositum is finite-dimensional over its
changed-uniformizer fixed subfield. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_finiteDimensional_over_changedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    FiniteDimensional
      (padicCompletedChangedUniformizerFixedField p u n)
      (padicCompletedStandardChangedCompositum p u n) :=
  FiniteDimensional.right ℚ_[p]
    (padicCompletedChangedUniformizerFixedField p u n)
    (padicCompletedStandardChangedCompositum p u n)

/-- The finite standard/changed compositum is Galois over its changed fixed
subfield. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_isGalois_over_changedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsGalois
      (padicCompletedChangedUniformizerFixedField p u n)
      (padicCompletedStandardChangedCompositum p u n) :=
  IsGalois.tower_top_of_isGalois ℚ_[p]
    (padicCompletedChangedUniformizerFixedField p u n)
    (padicCompletedStandardChangedCompositum p u n)

/-- The standard/changed compositum carries its canonical finite-extension
spectral norm. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_nontriviallyNormedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    NontriviallyNormedField
      (padicCompletedStandardChangedCompositum p u n) :=
  finiteExtensionSpectralNormedField ℚ_[p]
    (padicCompletedStandardChangedCompositum p u n)

/-- The standard/changed compositum has the canonical valuative relation
induced by its finite p-adic spectral norm. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_valuativeRel
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    ValuativeRel
      (padicCompletedStandardChangedCompositum p u n) :=
  finiteExtensionSpectralValuativeRel ℚ_[p]
    (padicCompletedStandardChangedCompositum p u n)

/-- The changed fixed field is a nonarchimedean local field for its canonical
finite p-adic spectral topology. -/
noncomputable instance
    padicCompletedChangedUniformizerFixedField_isNonarchimedeanLocalField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsNonarchimedeanLocalField
      (padicCompletedChangedUniformizerFixedField p u n) :=
  finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p]
    (padicCompletedChangedUniformizerFixedField p u n)

/-- The standard/changed compositum is a nonarchimedean local field for its
canonical finite p-adic spectral topology. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_isNonarchimedeanLocalField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsNonarchimedeanLocalField
      (padicCompletedStandardChangedCompositum p u n) :=
  finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p]
    (padicCompletedStandardChangedCompositum p u n)

/-- The canonical spectral valuation of the standard/changed compositum
extends that of the changed fixed field. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_valuation_hasExtension
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Valuation.HasExtension
      (ValuativeRel.valuation
        (padicCompletedChangedUniformizerFixedField p u n))
      (ValuativeRel.valuation
        (padicCompletedStandardChangedCompositum p u n)) :=
  finiteExtensionSpectralValuation_hasExtension_of_tower ℚ_[p]
    (padicCompletedChangedUniformizerFixedField p u n)
    (padicCompletedStandardChangedCompositum p u n)

/-- The canonical complete-DVF valuation of the standard/changed compositum
extends the one on the changed fixed field. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_localCompleteDVFValuation_hasExtension
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (localCompleteDVF
      (padicCompletedChangedUniformizerFixedField p u n)).valuation.HasExtension
      (localCompleteDVF
        (padicCompletedStandardChangedCompositum p u n)).valuation :=
  localCompleteDVFValuation_hasExtension
    (padicCompletedChangedUniformizerFixedField p u n)
    (padicCompletedStandardChangedCompositum p u n)

/-- The canonical valuation ring of the standard/changed compositum is the
integral closure of that of the changed fixed field. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_valuationSubring_isIntegralClosure
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsIntegralClosure
      (localCompleteDVF
        (padicCompletedStandardChangedCompositum p u n)).valuationSubring
      (localCompleteDVF
        (padicCompletedChangedUniformizerFixedField p u n)).valuationSubring
      (padicCompletedStandardChangedCompositum p u n) :=
  target_valuationSubring_isIntegralClosure_of_finite_separable
    (localCompleteDVF
      (padicCompletedChangedUniformizerFixedField p u n))
    (localCompleteDVF
      (padicCompletedStandardChangedCompositum p u n))

/-- The actual valuative integer ring of the standard/changed compositum is
the integral closure of the actual valuative integer ring of the changed
fixed field. -/
noncomputable instance
    padicCompletedStandardChangedCompositum_integerRing_isIntegralClosure
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsIntegralClosure
      𝒪[padicCompletedStandardChangedCompositum p u n]
      𝒪[padicCompletedChangedUniformizerFixedField p u n]
      (padicCompletedStandardChangedCompositum p u n) := by
  have h :=
    padicCompletedStandardChangedCompositum_valuationSubring_isIntegralClosure
      p u n
  change IsIntegralClosure
    (localCompleteDVF
      (padicCompletedStandardChangedCompositum p u n)).valuation.valuationSubring
    (localCompleteDVF
      (padicCompletedChangedUniformizerFixedField p u n)).valuation.valuationSubring
    (padicCompletedStandardChangedCompositum p u n) at h
  rw [localCompleteDVF_valuation_eq,
    localCompleteDVF_valuation_eq] at h
  exact h

/-- Under the ambient residue embedding, the residue action of the finite
relative Artin candidate is the residue action of inverse completed
Frobenius. -/
theorem
    padicCompletedStandardChangedCompositumResidueEmbedding_artinCandidate
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (a : IsLocalRing.ResidueField
      (localCompleteDVF
        (padicCompletedStandardChangedCompositum p u n)).valuationSubring) :
    padicCompletedStandardChangedCompositumResidueEmbedding p u n
        (galoisGroupResidueFieldEquivOfIsIntegralClosure
          (padicCompletedChangedUniformizerFixedField p u n)
          (padicCompletedStandardChangedCompositum p u n)
          (padicCompletedChangedUniformizerRelativeArtinCandidate
            p u n) a) =
      IsLocalRing.ResidueField.mapEquiv
          (padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹).symm
        (padicCompletedStandardChangedCompositumResidueEmbedding
          p u n a) := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let E := padicCompletedLevelField p n
  let padicBase := (padicLocalField p).toCompleteDVF
  let canonicalBase := localCompleteDVF ℚ_[p]
  let coefficient := padicCompletedUnramifiedCompleteDVF p
  let ambient := padicCompletedLevelCompleteDVF p n
  let :
      Valuation.HasExtension (ValuativeRel.valuation ℚ_[p])
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension ℚ_[p] M
  let :
      canonicalBase.valuation.HasExtension
        (localCompleteDVF M).valuation :=
    localCompleteDVFValuation_hasExtension ℚ_[p] M
  let : padicBase.valuation.HasExtension coefficient.valuation :=
    padicCompletedUnramifiedValuation_hasExtension p
  let : coefficient.valuation.HasExtension ambient.valuation :=
    padicCompletedLevelCompleteDVF_hasExtension p n
  let : padicBase.valuation.HasExtension ambient.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.hasExtension_trans
      padicBase.valuation coefficient.valuation
      ambient.valuation
  let :
      canonicalBase.valuation.HasExtension ambient.valuation :=
    localCompleteDVFValuation_hasExtension_of_padicLocalField
      p ambient.valuation
  let inclusion : M →+* E := M.val.toRingHom
  have inclusion_comp :
      inclusion.comp (algebraMap ℚ_[p] M) =
        algebraMap ℚ_[p] E := by
    ext x
    exact M.val.commutes x
  let :
      canonicalBase.valuation.HasExtension
        (ambient.valuation.comap inclusion) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusion inclusion_comp
  have hEquiv :
      (localCompleteDVF M).valuation.IsEquiv
        (ambient.valuation.comap inclusion) :=
    valuation_isEquiv_of_finite_separable
      canonicalBase (localCompleteDVF M)
        (ambient.valuation.comap inclusion)
  let τ :=
    padicCompletedChangedUniformizerRelativeArtinCandidate p u n
  let σM :
      (localCompleteDVF M).valuationSubring ≃+*
        (localCompleteDVF M).valuationSubring :=
    galoisGroupIntegerRingEquivOfIsIntegralClosure D M τ
  let σE :
      ambient.valuationSubring ≃+* ambient.valuationSubring :=
    (padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹).symm
  have hcompat :
      ∀ b : (localCompleteDVF M).valuationSubring,
        valuationSubringMapOfIsEquivComap
            (localCompleteDVF M).valuation ambient.valuation
            inclusion hEquiv (σM b) =
          σE
            (valuationSubringMapOfIsEquivComap
              (localCompleteDVF M).valuation ambient.valuation
              inclusion hEquiv b) := by
    intro b
    apply Subtype.ext
    change
      M.val (τ (b : M)) =
        (padicCompletedUnitFrobeniusLiftEquiv p n u⁻¹).symm
          (M.val (b : M))
    rfl
  change
    residueFieldMapOfIsEquivComap
        (localCompleteDVF M).valuation ambient.valuation
        inclusion hEquiv
        (IsLocalRing.ResidueField.mapEquiv σM a) =
      IsLocalRing.ResidueField.mapEquiv σE
        (residueFieldMapOfIsEquivComap
          (localCompleteDVF M).valuation ambient.valuation
          inclusion hEquiv a)
  exact
    residueFieldMapOfIsEquivComap_mapEquiv
      (localCompleteDVF M).valuation ambient.valuation
      inclusion hEquiv σM σE hcompat a

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedResidueFrobenius
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSelectedResidueIsAlgClosed _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.padicCompletedChangedUniformizerFixedField_finiteDimensional _root_.LubinTate.padicCompletedChangedUniformizerFixedField_isAbelianGalois _root_.LubinTate.padicCompletedChangedUniformizerFixedField_isNonarchimedeanLocalField _root_.LubinTate.padicCompletedChangedUniformizerFixedField_nontriviallyNormedField _root_.LubinTate.padicCompletedChangedUniformizerFixedField_valuativeRel _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_finiteDimensional _root_.LubinTate.padicCompletedStandardChangedCompositum_finiteDimensional_over_changedField _root_.LubinTate.padicCompletedStandardChangedCompositum_integerRing_isIntegralClosure _root_.LubinTate.padicCompletedStandardChangedCompositum_isAbelianGalois _root_.LubinTate.padicCompletedStandardChangedCompositum_isGalois_over_changedField _root_.LubinTate.padicCompletedStandardChangedCompositum_isNonarchimedeanLocalField _root_.LubinTate.padicCompletedStandardChangedCompositum_localCompleteDVFValuation_hasExtension _root_.LubinTate.padicCompletedStandardChangedCompositum_nontriviallyNormedField _root_.LubinTate.padicCompletedStandardChangedCompositum_valuationSubring_isIntegralClosure _root_.LubinTate.padicCompletedStandardChangedCompositum_valuation_hasExtension _root_.LubinTate.padicCompletedStandardChangedCompositum_valuativeRel _root_.LubinTate.padicCompletedStandardLevelField_finiteDimensional _root_.LubinTate.padicCompletedStandardLevelField_isAbelianGalois _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Residue Frobenius on completed p-adic Lubin--Tate levels

The completed multiplicative Lubin--Tate level is totally ramified over its
completed-unramified coefficient field.  Hence the canonical residue map is
an isomorphism.  Under this identification, every unit-indexed completed
Frobenius lift induces the arithmetic Frobenius `x ↦ x ^ p` on the residue
field.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ResidueField
open ValuationTheory.DiscreteValuationField.ValuedExtension

theorem
    padicCompletedUnramifiedWitt_residue_frobenius_eq_pow
    (p : ℕ) [Fact p.Prime]
    (a : padicCompletedUnramifiedWittRing p) :
    IsLocalRing.residue (padicCompletedUnramifiedWittRing p)
        (WittVector.frobenius a) =
      IsLocalRing.residue (padicCompletedUnramifiedWittRing p) a ^ p := by
  calc
    IsLocalRing.residue (padicCompletedUnramifiedWittRing p)
        (WittVector.frobenius a) =
        IsLocalRing.residue (padicCompletedUnramifiedWittRing p)
          (a ^ p) := by
      rw [residue_eq_residue_iff_sub_mem_maximalIdeal,
        padicCompletedUnramifiedWittRing_maximalIdeal,
        ← WittVector.ker_constantCoeff]
      change
        WittVector.constantCoeff
          (WittVector.frobenius a - a ^ p) = 0
      rw [map_sub, map_pow, WittVector.constantCoeff_apply,
        WittVector.coeff_frobenius_charP]
      exact sub_self _
    _ =
        IsLocalRing.residue (padicCompletedUnramifiedWittRing p) a ^ p := by
      rw [map_pow]

/-- The actual residue action induced by every unit-indexed completed
Frobenius lift is the arithmetic Frobenius `x ↦ x ^ p`. -/
theorem
    padicCompletedUnitFrobeniusIntegerEquiv_residue_apply_eq_pow
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicLocalField
      p).valuationSubringˣ)
    (x : (padicCompletedLevelCompleteDVF p n).residueField) :
    IsLocalRing.ResidueField.mapEquiv
        (padicCompletedUnitFrobeniusIntegerEquiv p n u) x =
      x ^ p := by
  let W := padicCompletedUnramifiedWittRing p
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let wittIntegerEquiv : W ≃+* base.valuationSubring :=
    padicCompletedUnramifiedWittRingEquivValuationSubring p
  let coefficientResidueEquiv :
      IsLocalRing.ResidueField W ≃+* target.residueField :=
    (IsLocalRing.ResidueField.mapEquiv wittIntegerEquiv).trans
      (padicCompletedLevelResidueFieldEquiv p n)
  have hcoefficient (a : W) :
      coefficientResidueEquiv (IsLocalRing.residue W a) =
        target.residueMap
          (padicCompletedLevelWittCoefficientHom p n a) := by
    simp only [coefficientResidueEquiv, RingEquiv.trans_apply,
      IsLocalRing.ResidueField.mapEquiv_apply]
    rfl
  obtain ⟨z, rfl⟩ := coefficientResidueEquiv.surjective x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
  calc
    IsLocalRing.ResidueField.mapEquiv
        (padicCompletedUnitFrobeniusIntegerEquiv p n u)
        (coefficientResidueEquiv (IsLocalRing.residue W a)) =
        target.residueMap
          (padicCompletedUnitFrobeniusIntegerEquiv p n u
            (padicCompletedLevelWittCoefficientHom p n a)) := by
      rw [hcoefficient]
      rfl
    _ =
        target.residueMap
          (padicCompletedLevelWittCoefficientHom p n
            (WittVector.frobenius a)) := by
      rw [padicCompletedUnitFrobeniusIntegerEquiv_wittCoefficientHom]
    _ =
        coefficientResidueEquiv
          (IsLocalRing.residue W (WittVector.frobenius a)) :=
      (hcoefficient (WittVector.frobenius a)).symm
    _ =
        coefficientResidueEquiv
          (IsLocalRing.residue W a ^ p) := by
      rw [padicCompletedUnramifiedWitt_residue_frobenius_eq_pow]
    _ = coefficientResidueEquiv (IsLocalRing.residue W a) ^ p := by
      rw [map_pow]

end LubinTate
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional_over_extension _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedStandardChangedCompositum_finiteDimensional_over_changedField _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instSMulCommClass _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Base change of the rational cyclotomic `ZHat`-extension

The rational cyclotomic `ZHat`-extension lives inside the fixed separable
closure of `ℚ`.  To form its compositum with an arbitrary number field, we first
embed that number field into the same separable closure.  The
intersection degree below is the normalization integer

`f_K = [K ∩ ℚ̃ : ℚ]`.

All fields in this file are the actual mathlib intermediate fields in
`SeparableClosure ℚ`; no abstract copy of the compositum or of its
Galois group is introduced.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped Topology
open AlgebraicNumberTheory
open ClassFormation
open KummerTheory

variable (K : Type*) [Field K] [NumberField K]

noncomputable instance
    numberFieldCyclotomicZHatIntersection_numberField :
    NumberField (numberFieldCyclotomicZHatIntersection K) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

/-- For an abstract fixed field, the intersection degree computed
using `numberFieldSeparableClosureEmbedding` is the degree of the
canonical intersection already present in the rational absolute
Galois correspondence. -/
theorem
    cyclotomicZHatIntersectionDegree_abstractFixedField_eq_intersection_finrank
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    cyclotomicZHatIntersectionDegree F =
      Module.finrank ℚ
        ((F ⊓ rationalCyclotomicZHatField :
          IntermediateField ℚ (SeparableClosure ℚ))) := by
  dsimp only
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  change
    Module.finrank ℚ
        (numberFieldCyclotomicZHatIntersection F) =
      Module.finrank ℚ
        ((F ⊓ rationalCyclotomicZHatField :
          IntermediateField ℚ (SeparableClosure ℚ)))
  change
    Module.finrank ℚ
        (((numberFieldSeparableClosureEmbedding F).fieldRange ⊓
          rationalCyclotomicZHatField :
          IntermediateField ℚ (SeparableClosure ℚ))) =
      Module.finrank ℚ
        ((LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field ⊓ rationalCyclotomicZHatField :
          IntermediateField ℚ (SeparableClosure ℚ)))
  exact
    abstractFixedFieldCyclotomicZHatIntersection_finrank_eq_of_embedding
      H (numberFieldSeparableClosureEmbedding F)

/-- The concrete intersection degree of an abstract fixed field,
formed using the arbitrary chosen number-field embedding, is exactly
the residue degree supplied by `rationalCyclotomicDegreeData`. -/
theorem
    cyclotomicZHatIntersectionDegree_abstractFixedField_eq_residueDegree
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    cyclotomicZHatIntersectionDegree F =
      (H.residueDegree rationalCyclotomicDegreeData : ℕ) := by
  exact
    (cyclotomicZHatIntersectionDegree_abstractFixedField_eq_intersection_finrank
      H).trans
      (rationalCyclotomicDegreeData_residueDegree_eq_intersection_finrank
        H).symm

instance
    rationalCyclotomicZHatFiniteLayerCompositum_scalarTower
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ E
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  IsScalarTower.of_algebraMap_eq'
    ((rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E).comp_algebraMap.symm)

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositum_finiteDimensional_over_layer
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional E
      (numberFieldCyclotomicZHatFiniteCompositum K E) := by
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : Algebra E
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
    ((rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E).toRingHom).toAlgebra
  let : Module E
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
    Algebra.toModule
  let : IsScalarTower ℚ E
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
    rationalCyclotomicZHatFiniteLayerCompositum_scalarTower K E
  exact
    FiniteDimensional.right ℚ E
      (numberFieldCyclotomicZHatFiniteCompositum K E)

/-- Restriction from the actual finite compositum over `K` has image
exactly the subgroup of `Gal(E/ℚ)` fixing the actual intersection
`K ∩ E`. -/
theorem
    numberFieldCyclotomicZHatFiniteCompositum_restriction_range
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    letI : Normal ℚ E := E.isGalois.to_normal
    let C :=
      numberFieldCyclotomicZHatFiniteCompositum K E
    (IntermediateField.restrictRestrictAlgEquivMapHom
        ℚ E K C).range =
      (numberFieldCyclotomicZHatFiniteIntersection K E).fixingSubgroup := by
  let : Normal ℚ E := E.isGalois.to_normal
  let C :=
    numberFieldCyclotomicZHatFiniteCompositum K E
  let : Algebra ℚ C := C.algebra'
  let : Algebra K C :=
    numberFieldCyclotomicZHatFiniteCompositum_algebra K E
  let : IsScalarTower ℚ K C :=
    numberFieldCyclotomicZHatFiniteCompositum_scalarTower K E
  let : Algebra E C :=
    rationalCyclotomicZHatFiniteLayerCompositum_algebra K E
  let : IsScalarTower ℚ E C :=
    rationalCyclotomicZHatFiniteLayerCompositum_scalarTower K E
  let eK : K →ₐ[ℚ] C :=
    numberFieldCyclotomicZHatFiniteCompositumEmbedding K E
  let eE : E →ₐ[ℚ] C :=
    rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E
  let r :
      (C ≃ₐ[K] C) →* (E ≃ₐ[ℚ] E) :=
    IntermediateField.restrictRestrictAlgEquivMapHom
      ℚ E K C
  let J : IntermediateField ℚ E :=
    numberFieldCyclotomicZHatFiniteIntersection K E
  have restriction_commutes
      (τ : C ≃ₐ[K] C) (x : E) :
      eE (r τ x) = τ (eE x) := by
    change algebraMap E C (r τ x) = τ (algebraMap E C x)
    change
      algebraMap E C
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ C τ) E) x) =
        (MulSemiringAction.toAlgEquiv ℚ C τ) (algebraMap E C x)
    exact AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv ℚ C τ) E x
  have hfixedField :
      IntermediateField.fixedField r.range = J := by
    ext x
    rw [IntermediateField.mem_fixedField_iff]
    change
      (∀ σ, σ ∈ r.range → σ x = x) ↔
        eE x ∈ eK.fieldRange
    constructor
    · intro hx
      have hfixed :
          ∀ τ : C ≃ₐ[K] C, τ (eE x) = eE x := by
        intro τ
        have hxτ :
            r τ x = x :=
          hx (r τ) ⟨τ, rfl⟩
        have hrestrict :
            eE (r τ x) = τ (eE x) := by
          exact restriction_commutes τ x
        exact hrestrict.symm.trans (congrArg eE hxτ)
      have hmem :
          eE x ∈ Set.range (algebraMap K C) :=
        (IsGalois.mem_range_algebraMap_iff_fixed
          (eE x)).2 hfixed
      rw [AlgHom.mem_fieldRange]
      obtain ⟨k, hk⟩ := hmem
      refine ⟨k, ?_⟩
      change algebraMap K C k = eE x
      exact hk
    · intro hx σ hσ
      obtain ⟨τ, rfl⟩ := hσ
      rw [AlgHom.mem_fieldRange] at hx
      obtain ⟨k, hk⟩ := hx
      apply eE.injective
      change eE (r τ x) = eE x
      have hrestrict :
          eE (r τ x) = τ (eE x) := by
        exact restriction_commutes τ x
      rw [hrestrict, ← hk]
      change τ (algebraMap K C k) = algebraMap K C k
      exact τ.commutes k
  calc
    r.range =
        (IntermediateField.fixedField r.range).fixingSubgroup :=
      (IntermediateField.fixingSubgroup_fixedField
        r.range).symm
    _ = J.fixingSubgroup := by rw [hfixedField]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractFixedFieldIdeleClassEquivFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The infinite global Artin homomorphism

This file assembles the finite global Artin homomorphisms in the
`FiniteGaloisIntermediateField` inverse limit supplied by mathlib.  The
first target is the actual `ZHat`-extension of `ℚ` constructed in
`CyclotomicZHatBaseChange`.

The positive archimedean section below is the cyclotomic normalization device:
multiplying an idele by the section of its absolute
norm produces a norm-one idele without changing its Artin symbol.
-/

open scoped Classical IsMulCommutative NNReal NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp

/-!
## Assembly in the finite-Galois inverse limit

The following construction is the global analogue of LCFT's
`residueFrobeniusToLimit`: its coordinates are the actual finite global
Artin homomorphisms, and compatibility is restriction in a finite
abelian tower.
-/

/-- Rational cyclotomic projection with caller-supplied finite-layer
structures. -/
theorem restrictNormalHom_rationalCyclotomicZHatGlobalArtin_of_structures
    (a : IdeleGroup ℚ)
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois ℚ E) :
    letI : NumberField E := hE
    letI : IsAbelianGalois ℚ E := hAbelian
    AlgEquiv.restrictNormalHom E
        (rationalCyclotomicZHatGlobalArtin a) =
      globalArtinMonoidHom
        (K := ℚ) (L := E) a := by
  let : NumberField E := hE
  let : IsAbelianGalois ℚ E := hAbelian
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_structures
      ℚ rationalCyclotomicZHatField a E hE hAbelian

/-- A mapped relative infinite Artin projection, the corresponding rational
finite Artin value, and the rational infinite projection, packaged with both
comparison steps.  The common finite value is generated only once in this
generic provider, so concrete dependent towers never compare separately
elaborated finite-field structures. -/
noncomputable def
    compRestrictNormalHomInfiniteGlobalArtinRationalCyclotomicDataOfNumberField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E' : FiniteGaloisIntermediateField K Ω)
    (hE' : NumberField E')
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois ℚ E)
    (f : (E' ≃ₐ[K] E') →* Gal(E / ℚ))
    (hnat :
      letI : NumberField E' := hE'
      letI : NumberField E := hE
      letI : IsAbelianGalois ℚ E := hAbelian
      f.comp (globalArtinMonoidHomOfNumberField K E' hE') =
        (globalArtinMonoidHom (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ K)) :
    letI : NumberField E' := hE'
    letI : NumberField E := hE
    letI : IsAbelianGalois ℚ E := hAbelian
    {x : Gal(E / ℚ) × Gal(E / ℚ) × Gal(E / ℚ) //
      x.1 = x.2.1 ∧ x.2.1 = x.2.2} := by
  letI : NumberField E' := hE'
  letI : NumberField E := hE
  letI : IsAbelianGalois ℚ E := hAbelian
  let relativeData :=
    compRestrictNormalHomInfiniteGlobalArtinNaturalityDataOfNumberField
      K Ω a E' hE' f
      ((globalArtinMonoidHom (K := ℚ) (L := E)).comp
        (IdeleGroup.norm ℚ K))
      hnat
  have hcomp :
      ((globalArtinMonoidHom (K := ℚ) (L := E)).comp
        (IdeleGroup.norm ℚ K)) a =
        globalArtinMonoidHom (K := ℚ) (L := E)
          (IdeleGroup.norm ℚ K a) :=
    rfl
  exact
    ⟨(relativeData.1,
        ((globalArtinMonoidHom (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ K)) a,
        AlgEquiv.restrictNormalHom E
          (rationalCyclotomicZHatGlobalArtin
            (IdeleGroup.norm ℚ K a))),
      relativeData.2,
      hcomp.trans
        (restrictNormalHom_rationalCyclotomicZHatGlobalArtin_of_structures
          (IdeleGroup.norm ℚ K a) E hE hAbelian).symm⟩

/-- Every rational idele has the same infinite Artin symbol as a
norm-one idele. -/
theorem
    exists_normOneIdele_same_rationalCyclotomicZHatGlobalArtin
    (a : IdeleGroup ℚ) :
    ∃ b : IdeleGroup.normOneSubgroup (K := ℚ),
      rationalCyclotomicZHatGlobalArtin b =
        rationalCyclotomicZHatGlobalArtin a := by
  let r := IdeleGroup.absoluteNorm a
  refine
    ⟨⟨a * rationalPositiveArchimedeanIdele r, ?_⟩,
      ?_⟩
  · change
      IdeleGroup.absoluteNorm
          (a * rationalPositiveArchimedeanIdele r) =
        1
    rw [map_mul,
      rationalPositiveArchimedeanIdele_absoluteNorm]
    simp [r]
  · change
      rationalCyclotomicZHatGlobalArtin
          (a * rationalPositiveArchimedeanIdele r) =
        rationalCyclotomicZHatGlobalArtin a
    rw [map_mul,
      rationalCyclotomicZHatGlobalArtin_rationalPositiveArchimedeanIdele,
      mul_one]

/-- The norm-one rational ideles already have dense Artin image. -/
theorem rationalCyclotomicZHatGlobalArtin_normOne_denseRange :
    DenseRange
      (fun b : IdeleGroup.normOneSubgroup (K := ℚ) =>
        rationalCyclotomicZHatGlobalArtin b) := by
  apply rationalCyclotomicZHatGlobalArtin_denseRange.mono
  rintro σ ⟨a, rfl⟩
  obtain ⟨b, hb⟩ :=
    exists_normOneIdele_same_rationalCyclotomicZHatGlobalArtin a
  exact ⟨b, hb⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

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

local instance rationalComplexificationPrimeFact_re77c1b_1 :
    Fact rationalComplexificationPrime.1.Prime :=
  ⟨rationalComplexificationPrime.2⟩
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationPrimeSquareNeZero
noncomputable instance
    rationalComplexificationCyclotomicField_isCMField :
    NumberField.IsCMField rationalComplexificationCyclotomicField := by
  apply IsCyclotomicExtension.Rat.isCMField
    rationalComplexificationCyclotomicField
    (S := {4})
  exact
    ⟨4, Set.mem_singleton 4, by norm_num⟩

attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_finiteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_numberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isAbelianGalois
/-- The chosen infinite place of the rational complexification is
ramified over the unique real place of `ℚ`. -/
theorem rationalComplexification_chosenInfinitePlace_isRamified :
    (chosenInfinitePlaceAbove
      (L := rationalComplexificationCyclotomicField)
      Rat.infinitePlace).IsRamified ℚ := by
  rw [InfinitePlace.isRamified_iff,
    chosenInfinitePlaceAbove_comap
      (L := rationalComplexificationCyclotomicField)
      Rat.infinitePlace]
  exact
    ⟨IsTotallyComplex.isComplex _, Rat.isReal_infinitePlace⟩

/-- The cyclotomic character of the rational fourth-root field. -/
noncomputable def rationalComplexificationCharacter :
    (rationalComplexificationCyclotomicField ≃ₐ[ℚ]
        rationalComplexificationCyclotomicField) ≃*
      (ZMod (rationalComplexificationPrime.1 ^ 2))ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod
    (rationalComplexificationPrime.1 ^ 2)
    rationalComplexificationCyclotomicField
    (hK :=
      KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
        rationalComplexificationCyclotomicOrder)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

theorem
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_action_baseChange_coe
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)]
    [FiniteDimensional ℚ
      ((abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK).restrictScalars ℚ)]
    [NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)]
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ₀ :
      abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK ≃ₐ[ℚ]
        abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)
    (hστ : ∀ y : abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK,
      ((τ₀ y : abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK) : SeparableClosure ℚ) =
        σ (y : SeparableClosure ℚ))
    (c : Additive
      (RelativeIdeleGroup.ClassGroup ℚ
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK))) :
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    let eFixed :=
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
        K L hLK
    let eRelative :=
      MulEquiv.toAdditive
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E))
    rationalIdeleClassRepresentation.ρ σ
        (eFixed (eRelative c)).1 =
      (eFixed
        (eRelative
          (Additive.ofMul
            (τ₀ • Additive.toMul c)))).1 := by
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let eFixed :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK
  let eRelative :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))
  let E₀ := E.restrictScalars ℚ
  let τQ : E₀ ≃ₐ[ℚ] E₀ := τ₀
  let cRelQ : RelativeIdeleGroup.ClassGroup ℚ E₀ :=
    Additive.toMul c
  let cQ : IdeleClassGroup E₀ :=
    _root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := E₀) cRelQ
  let cτRelQ : RelativeIdeleGroup.ClassGroup ℚ E₀ :=
    τQ • cRelQ
  let cτQ : IdeleClassGroup E₀ :=
    _root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := E₀) cτRelQ
  have hστQ : ∀ y : E₀,
      ((τQ y : E₀) : SeparableClosure ℚ) =
        σ (y : SeparableClosure ℚ) := by
    exact hστ
  have hAction :=
    rationalIdeleClassEquivFixed_ambientAlgEquiv
      (E := E₀) (F := E₀)
      σ τQ hστQ cQ
  have hLeft :
      (eFixed (eRelative c)).1 =
        (rationalIdeleClassEquivFixed
          E₀ (Additive.ofMul cQ)).1 := by
    exact
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_baseChange_coe
        K L hLK c
  have hCongr :
      ideleClassCongr τQ cQ = cτQ := by
    exact
      (_root_.relativeIdeleClassBaseChangeMulEquiv_smul_congr
        τQ cRelQ).symm
  have hcτRaw :
      cτQ =
        _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E)
          (τ₀ • Additive.toMul c) := by
    rfl
  have hRight :
      (rationalIdeleClassEquivFixed
        E₀ (Additive.ofMul (ideleClassCongr τQ cQ))).1 =
        (eFixed
          (eRelative
            (Additive.ofMul
              (τ₀ • Additive.toMul c)))).1 := by
    calc
      _ = (rationalIdeleClassEquivFixed
            E₀ (Additive.ofMul cτQ)).1 :=
        congrArg
          (fun d =>
            (rationalIdeleClassEquivFixed
              E₀ (Additive.ofMul d)).1)
          hCongr
      _ = (rationalIdeleClassEquivFixed
            E₀
            (Additive.ofMul
              (_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := E)
                (τ₀ • Additive.toMul c)))).1 :=
        congrArg
          (fun d =>
            (rationalIdeleClassEquivFixed
              E₀ (Additive.ofMul d)).1)
          hcτRaw
      _ = _ :=
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_baseChange_coe
          K L hLK
          (Additive.ofMul
            (τ₀ • Additive.toMul c))).symm
  calc
    rationalIdeleClassRepresentation.ρ σ
        (eFixed (eRelative c)).1 =
        rationalIdeleClassRepresentation.ρ σ
          (rationalIdeleClassEquivFixed
            E₀ (Additive.ofMul cQ)).1 :=
      congrArg (rationalIdeleClassRepresentation.ρ σ) hLeft
    _ = (rationalIdeleClassEquivFixed
          E₀
          (Additive.ofMul
            (ideleClassCongr τQ cQ))).1 :=
      hAction
    _ = _ := hRight

theorem
    rationalAbstractExtensionIdeleClassEquiv_action_fixed_mk
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
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (σ : K.toSubgroup)
    (x : (extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal).V) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    letI := hnormal
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
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    let M :=
      extensionFixedRepresentation rationalIdeleClassRepresentation
        K L hLK hnormal
    let eAmbient :=
      extensionFixedRepresentationEquiv
        rationalIdeleClassRepresentation K L hLK hnormal
    let eFixed :=
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK
    let eRelative :=
      MulEquiv.toAdditive
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E))
    let eQ :=
      abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ) K L hLK hnormal
    let τ : E ≃ₐ[F] E :=
      eQ (QuotientGroup.mk' (extensionSubgroup K L hLK) σ)
    let τ₀ : E ≃ₐ[ℚ] E := τ.restrictScalars ℚ
    let c : Additive (RelativeIdeleGroup.ClassGroup ℚ E) :=
      eRelative.symm (eFixed.symm (eAmbient x))
    eAmbient
        (M.ρ
          (QuotientGroup.mk' (extensionSubgroup K L hLK) σ) x) =
      eFixed
        (eRelative
          (Additive.ofMul (τ₀ • Additive.toMul c))) := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let := hnormal
  let : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let : NumberField F := NumberField.of_module_finite ℚ F
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let eFixed :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK
  let eRelative :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))
  let eQ :=
    abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let τ : E ≃ₐ[F] E :=
    eQ (QuotientGroup.mk' (extensionSubgroup K L hLK) σ)
  let τ₀ : E ≃ₐ[ℚ] E := τ.restrictScalars ℚ
  let c : Additive (RelativeIdeleGroup.ClassGroup ℚ E) :=
    eRelative.symm (eFixed.symm (eAmbient x))
  have hc :
      eFixed (eRelative c) = eAmbient x := by
    calc
      eFixed (eRelative c) =
          eFixed (eFixed.symm (eAmbient x)) :=
        congrArg eFixed
          (eRelative.apply_symm_apply
            (eFixed.symm (eAmbient x)))
      _ = eAmbient x :=
        eFixed.apply_symm_apply (eAmbient x)
  have hστ : ∀ y : E,
      ((τ₀ y : E) : SeparableClosure ℚ) =
        σ.1 (y : SeparableClosure ℚ) := by
    intro y
    change
      ((τ y : E) : SeparableClosure ℚ) =
        σ.1 (y : SeparableClosure ℚ)
    simpa only [τ, eQ] using
      (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
        ℚ (SeparableClosure ℚ) K L hLK hnormal σ y).symm
  apply Subtype.ext
  calc
    (eAmbient
        (M.ρ
          (QuotientGroup.mk' (extensionSubgroup K L hLK) σ) x)).1 =
        relativeCosetAction rationalIdeleClassRepresentation
          K L hLK (eAmbient x)
          (QuotientGroup.mk'
            (extensionSubgroup K L hLK) σ) :=
      extensionFixedRepresentation_action_coe
        rationalIdeleClassRepresentation K L hLK hnormal
          (QuotientGroup.mk'
            (extensionSubgroup K L hLK) σ) x
    _ =
        rationalIdeleClassRepresentation.ρ σ.1
          (eAmbient x).1 := by
      change
        relativeCosetAction rationalIdeleClassRepresentation
            K L hLK (eAmbient x) (QuotientGroup.mk σ) =
          rationalIdeleClassRepresentation.ρ σ.1
            (eAmbient x).1
      exact
        relativeCosetAction_mk
          rationalIdeleClassRepresentation K L hLK
          (eAmbient x) σ
    _ =
        rationalIdeleClassRepresentation.ρ σ.1
          (eFixed (eRelative c)).1 := by
      rw [hc]
    _ =
        (eFixed
          (eRelative
            (Additive.ofMul
              (τ₀ • Additive.toMul c)))).1 := by
      exact
        rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_action_baseChange_coe
          K L hLK σ.1 τ₀ hστ c

theorem rationalAbstractExtensionIdeleClassEquiv_action_mk
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
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (σ : K.toSubgroup)
    (x : (extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal).V) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    letI := hnormal
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
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    letI : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        ℚ (SeparableClosure ℚ) K L hLK hnormal
    letI : MulDistribMulAction (E ≃ₐ[F] E)
        (RelativeIdeleGroup.ClassGroup F E) :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
    rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
        ((extensionFixedRepresentation rationalIdeleClassRepresentation
          K L hLK hnormal).ρ
            (QuotientGroup.mk'
              (extensionSubgroup K L hLK) σ) x) =
      (Rep.ofMulDistribMulAction (E ≃ₐ[F] E)
        (RelativeIdeleGroup.ClassGroup F E)).ρ
          (abstractExtensionQuotientEquivGaloisGroup
            ℚ (SeparableClosure ℚ) K L hLK hnormal
            (QuotientGroup.mk'
              (extensionSubgroup K L hLK) σ))
          (rationalAbstractExtensionIdeleClassEquiv
            K L hLK hnormal x) := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let := hnormal
  let : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let : NumberField F := NumberField.of_module_finite ℚ F
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let : MulDistribMulAction (E ≃ₐ[F] E)
      (RelativeIdeleGroup.ClassGroup F E) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let eFixed :
      Additive (IdeleClassGroup E) ≃+
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation L :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK
  let eRelative :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (IdeleClassGroup E) :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))
  let eTower :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (RelativeIdeleGroup.ClassGroup F E) :=
    (MulEquiv.toAdditive
      (TowerRelativeIdeleGroup.classGroupEquiv
        ℚ F E).symm).trans
      (MulEquiv.toAdditive
        (towerRelativeIdeleClassBaseChangeMulEquiv
          ℚ F E))
  let eQ :=
    abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let τ : E ≃ₐ[F] E :=
    eQ (QuotientGroup.mk' (extensionSubgroup K L hLK) σ)
  let τ₀ : E ≃ₐ[ℚ] E := τ.restrictScalars ℚ
  let c : Additive (RelativeIdeleGroup.ClassGroup ℚ E) :=
    eRelative.symm (eFixed.symm (eAmbient x))
  change
    (((eAmbient.trans eFixed.symm).trans eRelative.symm).trans eTower)
        (M.ρ
          (QuotientGroup.mk'
            (extensionSubgroup K L hLK) σ) x) =
      Additive.ofMul
        (τ • Additive.toMul
          (eTower
            (eRelative.symm
              (eFixed.symm (eAmbient x)))))
  apply addEquiv_trans_symm_trans_symm_trans_apply_eq_p0
      eAmbient eFixed eRelative eTower
      (z := Additive.ofMul (τ₀ • Additive.toMul c))
  · exact
      rationalAbstractExtensionIdeleClassEquiv_action_fixed_mk
        K L hLK hnormal σ x
  · simpa only [eTower, τ₀, c] using
      (rationalTowerRelativeIdeleClassBaseChangeAddEquiv_smul
        F E τ c)

/-- The abstract quotient action on the rational absolute idele-class
representation becomes the ordinary Galois action on the relative idele
class group of the two concrete fixed fields. -/
theorem rationalAbstractExtensionIdeleClassEquiv_action
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
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (x : (extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal).V) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    letI := hnormal
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
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    letI : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        ℚ (SeparableClosure ℚ) K L hLK hnormal
    letI : MulDistribMulAction (E ≃ₐ[F] E)
        (RelativeIdeleGroup.ClassGroup F E) :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
    rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
        ((extensionFixedRepresentation rationalIdeleClassRepresentation
          K L hLK hnormal).ρ q x) =
      (Rep.ofMulDistribMulAction (E ≃ₐ[F] E)
        (RelativeIdeleGroup.ClassGroup F E)).ρ
          (abstractExtensionQuotientEquivGaloisGroup
            ℚ (SeparableClosure ℚ) K L hLK hnormal q)
          (rationalAbstractExtensionIdeleClassEquiv
            K L hLK hnormal x) := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let := hnormal
  let : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let : NumberField F := NumberField.of_module_finite ℚ F
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let : MulDistribMulAction (E ≃ₐ[F] E)
      (RelativeIdeleGroup.ClassGroup F E) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
  refine Quotient.inductionOn' q ?_
  intro σ
  exact
    rationalAbstractExtensionIdeleClassEquiv_action_mk
      K L hLK hnormal σ x

end Reciprocity
end GlobalClassFieldTheory
end
end


