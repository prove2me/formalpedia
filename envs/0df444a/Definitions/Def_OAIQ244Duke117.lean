-- Prove2me | Definitions.Def_OAIQ244Duke117
-- name    : OAIQ244Duke117
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T01:17:21.157647+00:00
-- url     : https://prove2.me/theorems/0ac2f960-7b88-42fd-9a85-75b020608b22
-- title:
--   Definitions bundle OAIQ244Duke117 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 55 declarations of OpenAI's Lean: 13 definitions and 42 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.RationalCyclotomicPrincipalPrimePadicLevel`, `GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormComposite`, `GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeContinuous`, `GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeInMulNatRange`, `GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeInMulNatRangeContinuous`, `GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValue`, `GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuous`, `GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuousMul`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueContinuousAdd`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueReduction`, `GlobalClassFieldTheory.Reciprocity.rationalIdeleArchimedeanPart`, `GlobalClassFieldTheory.Reciprocity.rationalIdeleFinitePart`, `LocalClassFieldTheory.padicCompletedChangedUniformizerNegativePrimeUnit`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleValue`, `GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleValueTopology`, `GlobalClassFieldTheory_Reciprocity_CyclotomicPrincipalIdele`, `GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange`, `GlobalClassFieldTheory_Reciprocity_FiniteIdeleArtin`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `GlobalClassFieldTheory_Reciprocity_GlobalArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_NormRestriction`, `LocalClassFieldTheory_LubinTateApplication_PadicMultiplicativeArtinComparison`, `LubinTate_Padic_CompletedChangedStandardUnramified`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke088` and `OAIQ244Duke089` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke092`.
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
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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
import Definitions.Def_OAIQ244Duke088
import Definitions.Def_OAIQ244Duke089

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instSMulCommClass _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- The cyclotomic intersection degree is positive. -/
theorem cyclotomicZHatIntersectionDegree_pos :
    0 < cyclotomicZHatIntersectionDegree K :=
  Module.finrank_pos

/-- Under the actual Galois identification with `ZHat`, the
subgroup fixing `K ∩ ℚ̃` is precisely
`f_K ZHat`, where `f_K = [K ∩ ℚ̃ : ℚ]`. -/
theorem
    rationalCyclotomicZHatFieldGal_fixingSubgroup_image_eq_mulNat_range :
    (((numberFieldCyclotomicZHatIntersection K).restrict
          (show
            numberFieldCyclotomicZHatIntersection K ≤
              rationalCyclotomicZHatField from
            inf_le_right)).fixingSubgroup.map
        rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom).toAddSubgroup' =
      (zHatMulNat
        (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range := by
  let hle :
      numberFieldCyclotomicZHatIntersection K ≤
        rationalCyclotomicZHatField :=
    inf_le_right
  let E : IntermediateField ℚ rationalCyclotomicZHatField :=
    (numberFieldCyclotomicZHatIntersection K).restrict hle
  let e :=
    rationalCyclotomicZHatFieldGalEquivZHat
  change
    (E.fixingSubgroup.map
      e.toMonoidHom).toAddSubgroup' =
        (zHatMulNat
          (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range
  refine
    zHatAddSubgroup_eq_mulNat_range_of_index_eq
      (E.fixingSubgroup.map
        e.toMonoidHom).toAddSubgroup'
      (cyclotomicZHatIntersectionDegree_pos K) ?_
  change
    (E.fixingSubgroup.map e.toMonoidHom).index =
      cyclotomicZHatIntersectionDegree K
  calc
    (E.fixingSubgroup.map e.toMonoidHom).index = E.fixingSubgroup.index :=
      Subgroup.index_map_equiv E.fixingSubgroup e.toMulEquiv
    _ = Module.finrank ℚ E :=
      (IntermediateField.finrank_eq_fixingSubgroup_index rationalCyclotomicZHatField E).symm
    _ = cyclotomicZHatIntersectionDegree K := by
      change
        Module.finrank ℚ
            ((numberFieldCyclotomicZHatIntersection K).restrict hle) =
          Module.finrank ℚ (numberFieldCyclotomicZHatIntersection K)
      exact
        ((IntermediateField.restrictAlgEquiv hle).toLinearEquiv).finrank_eq.symm

/-- Restriction to a finite rational cyclotomic layer commutes with
first restricting an automorphism of the full compositum to the
corresponding finite compositum over `K`. -/
theorem
    restrictNormalHom_numberFieldCyclotomicZHatCompositumRestriction
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (σ :
      Gal((numberFieldCyclotomicZHatCompositum K)/K)) :
    letI : Algebra ℚ (numberFieldCyclotomicZHatCompositum K) :=
      (numberFieldCyclotomicZHatCompositum K).algebra'
    letI : Algebra K (numberFieldCyclotomicZHatCompositum K) :=
      numberFieldCyclotomicZHatCompositum_algebra K
    letI : IsScalarTower ℚ K (numberFieldCyclotomicZHatCompositum K) :=
      numberFieldCyclotomicZHatCompositum_scalarTower K
    letI : Normal ℚ E := E.isGalois.to_normal
    letI : Normal K
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) := by
      let : IsAbelianGalois K
          (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
        numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois K E
      exact IsGalois.to_normal
    letI : IsScalarTower K
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
        (numberFieldCyclotomicZHatCompositum K) := by
      exact IntermediateField.isScalarTower_mid
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
    AlgEquiv.restrictNormalHom E
        (numberFieldCyclotomicZHatCompositumRestriction K σ) =
      IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E K
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
        (AlgEquiv.restrictNormalHom
          (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
          σ) := by
  let : Normal ℚ E := E.isGalois.to_normal
  let : Algebra ℚ (numberFieldCyclotomicZHatCompositum K) :=
    (numberFieldCyclotomicZHatCompositum K).algebra'
  let : Algebra K (numberFieldCyclotomicZHatCompositum K) :=
    numberFieldCyclotomicZHatCompositum_algebra K
  let : IsScalarTower ℚ K (numberFieldCyclotomicZHatCompositum K) :=
    numberFieldCyclotomicZHatCompositum_scalarTower K
  let : Normal K
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) := by
    let : IsAbelianGalois K
        (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
      numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois K E
    exact IsGalois.to_normal
  let : IsScalarTower K
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
      (numberFieldCyclotomicZHatCompositum K) := by
    exact IntermediateField.isScalarTower_mid
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
  let C := numberFieldCyclotomicZHatCompositum K
  let T := rationalCyclotomicZHatField
  let P : IntermediateField K C :=
    numberFieldCyclotomicZHatFiniteLayerInCompositum K E
  let : Algebra T C := rationalCyclotomicZHatCompositum_algebra K
  let : IsScalarTower ℚ T C :=
    rationalCyclotomicZHatCompositum_scalarTower K
  let : Algebra E P :=
    rationalCyclotomicZHatFiniteLayerInCompositum_algebra K E
  let : IsScalarTower ℚ E P :=
    rationalCyclotomicZHatFiniteLayerInCompositum_scalarTower K E
  let : IsAbelianGalois K P := by
    change IsAbelianGalois K
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)
    exact numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois K E
  let : Normal K P := IsGalois.to_normal
  let eEP : E →ₐ[ℚ] P :=
    rationalCyclotomicZHatFiniteLayerInCompositumEmbedding K E
  let iP : P →ₐ[K] C := IntermediateField.val P
  let iT : T →ₐ[ℚ] C := rationalCyclotomicZHatCompositumEmbedding K
  have hEmbedding (z : E) :
      iP (eEP z) = iT (z : T) := by
    apply Subtype.ext
    rfl
  have hL (z : E) :
      ((AlgEquiv.restrictNormalHom E
        (numberFieldCyclotomicZHatCompositumRestriction K σ)) z : T) =
        (numberFieldCyclotomicZHatCompositumRestriction K σ) (z : T) := by
    change
      algebraMap E T
          ((AlgEquiv.restrictNormalHom E
            (numberFieldCyclotomicZHatCompositumRestriction K σ)) z) =
        (numberFieldCyclotomicZHatCompositumRestriction K σ)
          (algebraMap E T z)
    change
      algebraMap E T
          ((AlgEquiv.restrictNormal
            (numberFieldCyclotomicZHatCompositumRestriction K σ) E) z) =
        (numberFieldCyclotomicZHatCompositumRestriction K σ)
          (algebraMap E T z)
    exact AlgEquiv.restrictNormal_commutes
      (numberFieldCyclotomicZHatCompositumRestriction K σ) E z
  have hRaw (z : T) :
      iT (numberFieldCyclotomicZHatCompositumRestriction K σ z) =
        σ (iT z) := by
    change
      algebraMap T C
          (numberFieldCyclotomicZHatCompositumRestriction K σ z) =
        σ (algebraMap T C z)
    change
      algebraMap T C
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ C σ) T) z) =
        (MulSemiringAction.toAlgEquiv ℚ C σ) (algebraMap T C z)
    exact AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv ℚ C σ) T z
  have hP (z : P) :
      iP (AlgEquiv.restrictNormalHom P σ z) = σ (iP z) := by
    change
      algebraMap P C (AlgEquiv.restrictNormalHom P σ z) =
        σ (algebraMap P C z)
    change
      algebraMap P C
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv K C σ) P) z) =
        (MulSemiringAction.toAlgEquiv K C σ) (algebraMap P C z)
    exact AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv K C σ) P z
  have hQ (z : E) :
      eEP
          (IntermediateField.restrictRestrictAlgEquivMapHom
            ℚ E K P (AlgEquiv.restrictNormalHom P σ) z) =
        (AlgEquiv.restrictNormalHom P σ) (eEP z) := by
    change
      algebraMap E P
          (IntermediateField.restrictRestrictAlgEquivMapHom
            ℚ E K P (AlgEquiv.restrictNormalHom P σ) z) =
        (AlgEquiv.restrictNormalHom P σ) (algebraMap E P z)
    change
      algebraMap E P
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ P
              (AlgEquiv.restrictNormalHom P σ)) E) z) =
        (MulSemiringAction.toAlgEquiv ℚ P
          (AlgEquiv.restrictNormalHom P σ)) (algebraMap E P z)
    exact AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv ℚ P
        (AlgEquiv.restrictNormalHom P σ)) E z
  apply AlgEquiv.ext
  intro x
  apply eEP.injective
  apply iP.injective
  calc
    iP (eEP
        (AlgEquiv.restrictNormalHom E
          (numberFieldCyclotomicZHatCompositumRestriction K σ) x)) =
        iT (((AlgEquiv.restrictNormalHom E
          (numberFieldCyclotomicZHatCompositumRestriction K σ) x) : T)) :=
      hEmbedding _
    _ = iT
        (numberFieldCyclotomicZHatCompositumRestriction K σ (x : T)) :=
      congrArg iT (hL x)
    _ = σ (iT (x : T)) := hRaw (x : T)
    _ = σ (iP (eEP x)) := congrArg σ (hEmbedding x).symm
    _ = iP (AlgEquiv.restrictNormalHom P σ (eEP x)) := (hP (eEP x)).symm
    _ = iP (eEP
        (IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E K P (AlgEquiv.restrictNormalHom P σ) x)) :=
      congrArg iP (hQ x).symm

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_NormRestriction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Norm--restriction for local Artin maps

This module proves norm--restriction naturality for actual finite abelian local Artin maps.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped IsMulCommutative ValuativeRel

/-- The actual finite abelian local Artin maps satisfy norm--restriction
naturality in an arbitrary finite square of nonarchimedean local fields. -/
theorem abelianLocalArtinMonoidHom_norm_restriction
    (K K' L L' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L] [Field L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation K')]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L'] :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (abelianLocalArtinMonoidHom K' L') =
      (abelianLocalArtinMonoidHom K L).comp
        (normUnits K K') := by
  apply MonoidHom.ext
  intro a
  let : FiniteDimensional K L' :=
    FiniteDimensional.trans K K' L'
  let : Algebra.IsSeparable K L' :=
    Algebra.IsSeparable.trans K K' L'
  let j : L' →ₐ[K] SeparableClosure K :=
    IsSepClosed.lift
  let jLower : L →ₐ[K] SeparableClosure K :=
    j.comp (IsScalarTower.toAlgHom K L L')
  let iLower : K →ₐ[K] SeparableClosure K :=
    jLower.comp (IsScalarTower.toAlgHom K K L)
  let eLower :
      @AlgEquiv K (SeparableClosure K) (SeparableClosure K)
        _ _ _
        (separableClosure K (AlgebraicClosure K)).algebra
        iLower.toRingHom.toAlgebra := by
    refine @AlgEquiv.ofRingEquiv
      K (SeparableClosure K) (SeparableClosure K)
      _ _ _
      (separableClosure K (AlgebraicClosure K)).algebra
      iLower.toRingHom.toAlgebra
      (RingEquiv.refl (SeparableClosure K)) ?_
    intro x
    change algebraMap K (SeparableClosure K) x = iLower x
    exact (iLower.commutes x).symm
  let iUpper : K' →ₐ[K] SeparableClosure K :=
    j.comp (IsScalarTower.toAlgHom K K' L')
  let eUpper :
      letI : Algebra K' (SeparableClosure K) :=
        iUpper.toRingHom.toAlgebra
      SeparableClosure K' ≃ₐ[K'] SeparableClosure K := by
    letI : Algebra K' (SeparableClosure K) :=
      iUpper.toRingHom.toAlgebra
    letI : Algebra.IsSeparable K' (SeparableClosure K) :=
      Algebra.isSeparable_tower_top_of_isSeparable
        K K' (SeparableClosure K)
    letI : IsSepClosure K' (SeparableClosure K) :=
      ⟨inferInstance, inferInstance⟩
    exact
      IsSepClosure.equiv K'
        (SeparableClosure K') (SeparableClosure K)
  let restrictActual :
      Gal(L' / K') →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  let aNorm : Kˣ :=
    normUnits K K' a
  let ambientUpper : Gal(L' / K') :=
    ambientEmbeddedNormResidueElement K K' L' j eUpper a
  let ambientLower : Gal(L / K) :=
    ambientEmbeddedNormResidueElement K K L jLower eLower aNorm
  have hUpper :
      abelianLocalArtinMonoidHom K' L' a = ambientUpper :=
    abelianLocalArtin_eq_ambientEmbeddedNormResidueSymbol_of_equiv
      K K' L' j eUpper a
  have hLower :
      abelianLocalArtinMonoidHom K L aNorm = ambientLower :=
    abelianLocalArtin_eq_ambientEmbeddedNormResidueSymbol_of_equiv
      K K L jLower eLower aNorm
  have htransport :
      restrictActual ambientUpper = ambientLower := by
    simpa only [restrictActual, ambientUpper, ambientLower, aNorm, jLower] using
      ambientEmbeddedNormResidueElement_norm_restriction
        K K' L L' j eLower eUpper a
  change
    restrictActual (abelianLocalArtinMonoidHom K' L' a) =
      abelianLocalArtinMonoidHom K L aNorm
  calc
    restrictActual (abelianLocalArtinMonoidHom K' L' a) =
        restrictActual ambientUpper := by
      exact congrArg restrictActual hUpper
    _ = ambientLower := htransport
    _ = abelianLocalArtinMonoidHom K L aNorm := hLower.symm

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instLocallyCompactSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.OAI.PrimeDegreePackets.xT2Space _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseIsNonarchimedeanLocalField _root_.chosenFinitePlaceBaseIsUltrametricDist _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.chosenFinitePlaceBaseNontriviallyNormedField _root_.chosenFinitePlaceBaseValuativeRel _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Norm--restriction for finite-place Artin homomorphisms

This module proves norm--restriction naturality for finite-place Artin maps in an actual square of number fields and their chosen completed local extensions.
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

theorem finitePlaceLocalArtin_norm_restriction_apply
    {C D E E' : Type}
    [Field C] [ValuativeRel C] [TopologicalSpace C]
    [IsNonarchimedeanLocalField C]
    [Field D] [ValuativeRel D] [TopologicalSpace D]
    [IsNonarchimedeanLocalField D]
    [Field E] [Field E']
    [Algebra C D] [Algebra C E] [Algebra C E']
    [Algebra D E'] [Algebra E E']
    [IsScalarTower C D E'] [IsScalarTower C E E']
    [FiniteDimensional C D] [Algebra.IsSeparable C D]
    [Valuation.HasExtension
      (ValuativeRel.valuation C) (ValuativeRel.valuation D)]
    [FiniteDimensional C E] [IsAbelianGalois C E]
    [FiniteDimensional D E'] [IsAbelianGalois D E']
    (y : Dˣ) :
    AlgEquiv.restrictNormalHom E
        ((AlgEquiv.restrictScalarsHom C)
          (LocalClassFieldTheory.abelianLocalArtinMonoidHom
            D E' y)) =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom C E
        (LocalFieldTheory.normUnits C D y) :=
  DFunLike.congr_fun
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom_norm_restriction
      C D E E') y

section FinitePlaceNormRestrictionInstances

variable {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')

local notation "vKₙ" =>
  NumberField.HeightOneSpectrum.adicAbv K v
local notation "vKₙ'" =>
  NumberField.HeightOneSpectrum.adicAbv K' W
local notation "Cₙ" =>
  finitePlaceNormCompletion K v
local notation "Dₙ" =>
  finitePlaceNormCompletion K' W
local notation "Eₙ" =>
  finitePlaceNormLocalizedCompletion K L v w
local notation "Eₙ'" =>
  finitePlaceNormLocalizedCompletion K' L' W w'

local instance finitePlaceNormLowerExtensionAlgebra_r22ff4b_1 :
    Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K) w.1
local instance finitePlaceNormLowerCompletionAlgebra_r22ff4b_1 :
    Algebra Cₙ w.1.Completion :=
  AbsoluteValue.completionAlgebra vKₙ w.1 w.2
local instance finitePlaceNormLowerGlobalAlgebra_r22ff4b_1 :
    Algebra K Eₙ :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra vKₙ w
local instance finitePlaceNormUpperExtensionAlgebra_r22ff4b_1 :
    Algebra K' w'.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K') w'.1
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperCompletionAlgebra
local instance finitePlaceNormUpperGlobalAlgebra_r22ff4b_1 :
    Algebra K' Eₙ' :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra vKₙ' w'
local instance finitePlaceNormLowerNontriviallyNormedField_r22ff4b_1 :
    NontriviallyNormedField Cₙ :=
  absoluteValueExtension_completionNontriviallyNormedField
    vKₙ (RayClass.adicAbv_isNontrivial v)
local instance finitePlaceNormLowerLocallyCompactSpace_r22ff4b_1 :
    LocallyCompactSpace Cₙ :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry v)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocallyCompactSpace
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormLowerLocalizedFiniteDimensional
local instance finitePlaceNormLowerLocalizedAbelianGalois_r22ff4b_1 :
    IsAbelianGalois Cₙ Eₙ :=
  LocalClassFieldTheory.localizedCompletion_isAbelianGalois
    vKₙ (RayClass.adicAbv_isNontrivial v) w
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocalizedFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocalizedAbelianGalois
local instance finitePlaceNormLowerUltrametric_r22ff4b_1 :
    IsUltrametricDist Cₙ :=
  finitePlaceArtinCompletionIsUltrametricDist vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValued_r22ff4b_1 :
    Valued Cₙ ℝ≥0 :=
  finitePlaceArtinCompletionValued vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValuationNontrivial_r22ff4b_1 :
    (Valued.v : Valuation Cₙ ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation (K := Cₙ)).IsNontrivial)
local instance finitePlaceNormLowerValuativeRel_r22ff4b_1 :
    ValuativeRel Cₙ :=
  finitePlaceArtinCompletionValuativeRel vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValuationCompatible_r22ff4b_1 :
    (Valued.v : Valuation Cₙ ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation
    (Valued.v : Valuation Cₙ ℝ≥0)
local instance finitePlaceNormLowerValuativeRelNontrivial_r22ff4b_1 :
    ValuativeRel.IsNontrivial Cₙ :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation Cₙ ℝ≥0)).2 inferInstance
local instance finitePlaceNormLowerLocalField_r22ff4b_1 :
    IsNonarchimedeanLocalField Cₙ :=
  finitePlaceArtinCompletionIsNonarchimedeanLocalField vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperUltrametric
local instance finitePlaceNormUpperValued_r22ff4b_1 :
    Valued Dₙ ℝ≥0 :=
  finitePlaceArtinCompletionValued vKₙ'
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W)
local instance finitePlaceNormUpperValuationNontrivial_r22ff4b_1 :
    (Valued.v : Valuation Dₙ ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation (K := Dₙ)).IsNontrivial)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperValuativeRel
local instance finitePlaceNormUpperValuationCompatible_r22ff4b_1 :
    (Valued.v : Valuation Dₙ ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation
    (Valued.v : Valuation Dₙ ℝ≥0)
local instance finitePlaceNormUpperValuativeRelNontrivial_r22ff4b_1 :
    ValuativeRel.IsNontrivial Dₙ :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation Dₙ ℝ≥0)).2 inferInstance
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperLocalField
theorem finitePlaceNormRawArtin_naturality
    [NumberField L]
    (hW : finitePlaceBelow (K := K) W = v)
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (y : Dₙˣ) :
    finitePlaceCrossLocalRestrictionMonoidHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W hW w w' hcentres
        (finitePlaceNormUpperRawArtin
          (K' := K') (L' := L') W w' y) =
      finitePlaceNormLowerRawArtin
        (K := K) (L := L) (K' := K')
        v W w hW y := by
  let C := finitePlaceNormCompletion K v
  let D := finitePlaceNormCompletion K' W
  let E := finitePlaceNormLocalizedCompletion K L v w
  let E' := finitePlaceNormLocalizedCompletion K' L' W w'
  let : Algebra C D :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  let : ContinuousSMul C D :=
    continuousSMul_of_algebraMap C D <|
      finitePlaceArtinRelativeCompletionRingHom_continuous
        (K := K) (K' := K') v W hW
  let : FiniteDimensional C D :=
    FiniteDimensional.of_locallyCompactSpace C
  let : CharZero C :=
    charZero_of_injective_algebraMap
      (algebraMap K C).injective
  let : Algebra.IsIntegral C D :=
    Algebra.IsIntegral.of_finite C D
  let : Algebra.IsSeparable C D :=
    Algebra.IsSeparable.of_integral C D
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
  let :
      (ValuativeRel.valuation C).HasExtension
        (ValuativeRel.valuation D) :=
    finitePlaceArtinCompletionHasExtension
      (K := K) (K' := K') v W hW
  let hGaloisE : IsGalois C E :=
    (inferInstance : IsAbelianGalois C E).toIsGalois
  let : Normal C E := hGaloisE.to_normal
  unfold finitePlaceNormUpperRawArtin
  unfold finitePlaceNormLowerRawArtin
  change
    AlgEquiv.restrictNormalHom E
        ((AlgEquiv.restrictScalarsHom C)
          (LocalClassFieldTheory.abelianLocalArtinMonoidHom
            D E' y)) =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom C E
        (LocalFieldTheory.normUnits C D y)
  exact finitePlaceLocalArtin_norm_restriction_apply y

theorem finitePlaceNormLocalizedArtin_naturality
    [NumberField L]
    (hW : finitePlaceBelow (K := K) W = v)
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (y : Dₙˣ) :
    finitePlaceNormRestrictedArtin
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hW hcentres y =
      finitePlaceNormLowerArtin
        (K := K) (L := L) (K' := K')
        v W w hW y := by
  calc
    _ =
        finitePlaceCrossLocalRestrictionMonoidHom
          (K := K) (L := L) (K' := K') (L' := L')
          v W hW w w' hcentres
          (finitePlaceNormUpperRawArtin
            (K' := K') (L' := L') W w' y) := by
      unfold finitePlaceNormRestrictedArtin
      exact congrArg
        (finitePlaceCrossLocalRestrictionMonoidHom
          (K := K) (L := L) (K' := K') (L' := L')
          v W hW w w' hcentres)
        (finitePlaceNormUpperArtin_eq_raw
          (K' := K') (L' := L') W w' y)
    _ =
        finitePlaceNormLowerRawArtin
          (K := K) (L := L) (K' := K')
          v W w hW y :=
      finitePlaceNormRawArtin_naturality
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hW hcentres y
    _ =
        finitePlaceNormLowerArtin
          (K := K) (L := L) (K' := K')
          v W w hW y :=
      (finitePlaceNormLowerArtin_eq_raw
        (K := K) (L := L) (K' := K')
        v W w hW y).symm

theorem
    finitePlaceLocalArtinMonoidHom_norm_restriction_localized
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
    (y : (finitePlaceNormCompletion K' W)ˣ) :
    finitePlaceCrossLocalRestrictionMonoidHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W hW w w' hcentres
        (finitePlaceLocalArtinMonoidHom
          (K := K') (L := L') W w'
          (finitePlaceCompletionUnitsContinuousMulEquiv W y)) =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w
        (finitePlaceCompletionUnitsContinuousMulEquiv v
          (finitePlaceRelativeNormUnits
            (K := K) (K' := K') v W hW y)) := by
  calc
    _ =
        finitePlaceNormRestrictedArtin
          (K := K) (L := L) (K' := K') (L' := L')
          v W w w' hW hcentres y :=
      rfl
    _ =
        finitePlaceNormLowerArtin
          (K := K) (L := L) (K' := K')
          v W w hW y :=
      finitePlaceNormLocalizedArtin_naturality
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hW hcentres y
    _ = _ :=
      rfl

/-- The local Artin maps attached to specified finite places commute
with the norm between their concrete adic completions. -/
theorem finitePlaceLocalArtinMonoidHom_norm_restriction
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
    (x : (W.adicCompletion K')ˣ) :
    letI : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
      (finitePlaceAdicCompletionMap
        K K' v ⟨W, hW⟩).toAlgebra
    finitePlaceCrossLocalRestrictionMonoidHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W hW w w' hcentres
        (finitePlaceLocalArtinMonoidHom
          (K := K') (L := L') W w' x) =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K') x) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
  let C := vK.Completion
  let D := vK'.Completion
  let eCUnits :
      Cˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  let eDUnits :
      Dˣ ≃* (W.adicCompletion K')ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv W
  let : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
    (finitePlaceAdicCompletionMap
      K K' v ⟨W, hW⟩).toAlgebra
  let : Algebra C D :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  calc
    finitePlaceCrossLocalRestrictionMonoidHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W hW w w' hcentres
        (finitePlaceLocalArtinMonoidHom
          (K := K') (L := L') W w' x) =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w
        (eCUnits
          (finitePlaceRelativeNormUnits
            (K := K) (K' := K') v W hW
            (eDUnits.symm x))) :=
      by
        have h :=
          finitePlaceLocalArtinMonoidHom_norm_restriction_localized
            (K := K) (L := L) (K' := K') (L' := L')
            v W hW w w' hcentres (eDUnits.symm x)
        change
          finitePlaceCrossLocalRestrictionMonoidHom
              (K := K) (L := L) (K' := K') (L' := L')
              v W hW w w' hcentres
              (finitePlaceLocalArtinMonoidHom
                (K := K') (L := L') W w'
                (eDUnits (eDUnits.symm x))) =
            finitePlaceLocalArtinMonoidHom
              (K := K) (L := L) v w
              (eCUnits
                (finitePlaceRelativeNormUnits
                  (K := K) (K' := K') v W hW
                  (eDUnits.symm x))) at h
        rw [eDUnits.apply_symm_apply] at h
        exact h
    _ =
      finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K') x) :=
      congrArg
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w)
        (finitePlaceArtinConcreteNormUnits
          (K := K) (K' := K') v W hW x)

end FinitePlaceNormRestrictionInstances

/-- The local Artin map attached to specified finite places carries a
local norm to the restriction of the upper Artin element. -/
theorem
    finitePlaceArtinMonoidHomOfExtension_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
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
      letI : NumberField L :=
        NumberField.of_module_finite K L
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w) :
    letI : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
      (finitePlaceAdicCompletionMap
        K K' v ⟨W, hW⟩).toAlgebra
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (finitePlaceArtinMonoidHomOfExtension
          (K := K') (L := L') W w') =
      (finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w).comp
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K')) := by
  let : NumberField L := NumberField.of_module_finite K L
  let : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
    (finitePlaceAdicCompletionMap
      K K' v ⟨W, hW⟩).toAlgebra
  let globalRestriction :
      (L' ≃ₐ[K'] L') →* (L ≃ₐ[K] L) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  let localUpper :=
    finitePlaceLocalArtinMonoidHom
      (K := K') (L := L') W w'
  let localLower :=
    finitePlaceLocalArtinMonoidHom
      (K := K) (L := L) v w
  let localRestriction :=
    finitePlaceCrossLocalRestrictionMonoidHom
      (K := K) (L := L) (K' := K') (L' := L')
      v W hW w w' hcentres
  let norm :=
    LocalFieldTheory.normUnits
      (v.adicCompletion K) (W.adicCompletion K')
  calc
    globalRestriction.comp
        (finitePlaceArtinMonoidHomOfExtension
          (K := K') (L := L') W w') =
      globalRestriction.comp
        ((finitePlaceLocalToGlobalMonoidHom
          (K := K') (L := L') W w').comp localUpper) :=
      congrArg
        (fun f => globalRestriction.comp f)
        (finitePlaceArtinMonoidHomOfExtension_factor
          (K := K') (L := L') W w')
    _ =
        (globalRestriction.comp
          (finitePlaceLocalToGlobalMonoidHom
            (K := K') (L := L') W w')).comp localUpper := by
      rfl
    _ =
        ((finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := L) v w).comp
          localRestriction).comp localUpper :=
      congrArg
        (fun f :
            finitePlaceNormLocalizedAut K' L' W w' →*
              (L ≃ₐ[K] L) =>
          f.comp localUpper)
        (by
          apply MonoidHom.ext
          intro tau
          exact
            finitePlaceCrossDecompositionTransport
              (K := K) (L := L) (K' := K') (L' := L')
              v W hW w w' hcentres tau)
    _ =
        (finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := L) v w).comp
          (localRestriction.comp localUpper) := by
      rfl
    _ =
        (finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := L) v w).comp
          (localLower.comp norm) :=
      congrArg
        (fun f => (finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := L) v w).comp f)
        (by
          apply MonoidHom.ext
          intro x
          exact
            finitePlaceLocalArtinMonoidHom_norm_restriction
              (K := K) (L := L) (K' := K') (L' := L')
              v W hW w w' hcentres x)
    _ =
        ((finitePlaceLocalToGlobalMonoidHom
          (K := K) (L := L) v w).comp localLower).comp norm := by
      rfl
    _ =
        (finitePlaceArtinMonoidHomOfExtension
          (K := K) (L := L) v w).comp norm :=
      congrArg
        (fun f => f.comp norm)
        (finitePlaceArtinMonoidHomOfExtension_factor
          (K := K) (L := L) v w).symm

/-- Finite-place norm--restriction compatibility.  Restriction of the upper
local Artin
factor is the lower local Artin factor after the norm between the
corresponding concrete adic completions. -/
theorem chosenFinitePlaceArtinMonoidHom_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (W : HeightOneSpectrum (𝓞 K')) :
    let v := finitePlaceBelow (K := K) W
    letI : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
      (finitePlaceAdicCompletionMap
        K K' v ⟨W, rfl⟩).toAlgebra
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (chosenFinitePlaceArtinMonoidHom
          (K := K') (L := L') W) =
      (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v).comp
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K')) := by
  let : NumberField L := NumberField.of_module_finite K L
  dsimp only
  let v :=
    finitePlaceBelow (K := K) W
  let w' :=
    chosenFinitePlaceExtension
      (L := L') W
  let U' :=
    finitePlaceExtensionCentre
      (K := K') (L := L') W w'
  let U :=
    finitePlaceBelow (K := L) U'
  have hUK : finitePlaceBelow (K := K) U = v := by
    calc
      finitePlaceBelow (K := K) U =
          finitePlaceBelow (K := K) U' := by
        exact
          finitePlaceBelow_finitePlaceBelow
            (K := K) (M := L) (L := L') U'
      _ =
          finitePlaceBelow (K := K)
            (finitePlaceBelow (K := K') U') := by
        symm
        exact
          finitePlaceBelow_finitePlaceBelow
            (K := K) (M := K') (L := L') U'
      _ = finitePlaceBelow (K := K) W := by
        rw [
          finitePlaceBelow_finitePlaceExtensionCentre
            (K := K') (L := L') W w']
      _ = v := rfl
  let Uv :
      {Q : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := K) Q = v} :=
    ⟨U, hUK⟩
  let w :
      AbsoluteValueExtension
        (NumberField.HeightOneSpectrum.adicAbv K v) L :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) v).symm Uv
  have hwCentre :
      finitePlaceExtensionCentre
          (K := K) (L := L) v w = U := by
    have h :=
      congrArg Subtype.val
        ((finitePlaceExtensionEquivAbove
          (K := K) (L := L) v).apply_symm_apply Uv)
    simpa only [
      finitePlaceExtensionEquivAbove_coe
    ] using h
  let : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
    (finitePlaceAdicCompletionMap
      K K' v ⟨W, rfl⟩).toAlgebra
  calc
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (chosenFinitePlaceArtinMonoidHom
          (K := K') (L := L') W) =
      (finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w).comp
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K')) := by
      exact
        finitePlaceArtinMonoidHomOfExtension_norm_restriction
          (K := K) (L := L) v W rfl w w'
          (by
            change
              finitePlaceBelow (K := L) U' =
                finitePlaceExtensionCentre
                  (K := K) (L := L) v w
            rw [hwCentre])
    _ =
      (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v).comp
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K')) := by
      change
        (finitePlaceArtinMonoidHomOfExtension
          (K := K) (L := L) v w).comp
            (LocalFieldTheory.normUnits
              (v.adicCompletion K) (W.adicCompletion K')) =
          (finitePlaceArtinMonoidHomOfExtension
            (K := K) (L := L) v
              (chosenFinitePlaceExtension
                (L := L) v)).comp
            (LocalFieldTheory.normUnits
              (v.adicCompletion K) (W.adicCompletion K'))
      exact congrArg
        (fun f : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) =>
          f.comp
            (LocalFieldTheory.normUnits
              (v.adicCompletion K) (W.adicCompletion K')))
        (finitePlaceArtinMonoidHomOfExtension_eq
          (K := K) (L := L) v w
          (chosenFinitePlaceExtension
            (L := L) v))

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteIdeleArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The finite-place product of local Artin homomorphisms

For a finite abelian extension of number fields `L / K`, the local
Artin factors of an idele are trivial at all but finitely many finite
places.  This file forms their `finprod` directly in the actual global
Galois group.
-/

open scoped Classical IsMulCommutative NumberField NNReal ValuativeRel
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open Function

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The finite part of the Artin norm--restriction field diamond.
Restriction of the upper finite Artin product is the lower finite Artin product
after the ordinary idele norm. -/
theorem finitePlaceGlobalArtinMonoidHom_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L'] :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (finitePlaceGlobalArtinMonoidHom
          (K := K') (L := L')) =
      (finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)).comp
        (IdeleGroup.norm K K') := by
  apply MonoidHom.ext
  intro a
  let : ∀ W : HeightOneSpectrum (𝓞 K'),
      Algebra
        ((finitePlaceBelow
          (K := K) W).adicCompletion K)
        (W.adicCompletion K') :=
    fun W =>
      (finitePlaceAdicCompletionMap
        K K'
        (finitePlaceBelow (K := K) W)
        ⟨W, rfl⟩).toAlgebra
  change
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (∏ᶠ W : HeightOneSpectrum (𝓞 K'),
          chosenFinitePlaceArtinMonoidHom
            (K := K') (L := L') W
            (IdeleGroup.finiteComponent W a)) =
      finitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K K' a)
  rw [finitePlaceGlobalArtinMonoidHom_norm_eq_finprod]
  rw [MonoidHom.map_finprod
    ((AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K))
    (finitePlaceArtinFactors_hasFiniteMulSupport
      (K := K') (L := L') a)]
  apply finprod_congr
  intro W
  exact
    DFunLike.congr_fun
      (chosenFinitePlaceArtinMonoidHom_norm_restriction
        (K := K) (L := L) W)
      (IdeleGroup.finiteComponent W a)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalArtin
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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

/-- Norm--restriction for the actual global Artin homomorphism.  In a number-field
diamond `K ⊂ K'`, `L ⊂ L'`, the ordinary idele norm and mathlib's standard
restriction composite form a commuting square. -/
theorem globalArtinMonoidHom_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L'] :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (globalArtinMonoidHom
          (K := K') (L := L')) =
      (globalArtinMonoidHom
        (K := K) (L := L)).comp
        (IdeleGroup.norm K K') := by
  apply MonoidHom.ext
  intro a
  change
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (infinitePlaceGlobalArtinMonoidHom
            (K := K') (L := L') a *
          finitePlaceGlobalArtinMonoidHom
            (K := K') (L := L') a) =
      infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := L)
          (IdeleGroup.norm K K' a) *
        finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L)
          (IdeleGroup.norm K K' a)
  rw [map_mul]
  have hinfinite :
      ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
          (infinitePlaceGlobalArtinMonoidHom
            (K := K') (L := L') a) =
        infinitePlaceGlobalArtinMonoidHom
          (K := K) (L := L)
          (IdeleGroup.norm K K' a) := by
    simpa only [MonoidHom.comp_apply] using
      DFunLike.congr_fun
        (infinitePlaceGlobalArtinMonoidHom_norm_restriction
          (K := K) (L := L))
        a
  have hfinite :
      ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
          (finitePlaceGlobalArtinMonoidHom
            (K := K') (L := L') a) =
        finitePlaceGlobalArtinMonoidHom
          (K := K) (L := L)
          (IdeleGroup.norm K K' a) := by
    simpa only [MonoidHom.comp_apply] using
      DFunLike.congr_fun
        (finitePlaceGlobalArtinMonoidHom_norm_restriction
          (K := K) (L := L))
        a
  rw [hinfinite, hfinite]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleValue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalFiniteGaloisIdeleClassMulDistribMulAction _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalAbsoluteGaloisIdeleClass_smul_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The normalized cyclotomic idele value

For a number field `K`, the actual cyclotomic `ZHat`-extension is the
compositum of the embedded copy of `K` with the rational cyclotomic
`ZHat`-extension.  Its normalization factor is the actual intersection degree

`f_K = [K ∩ ℚ̃ : ℚ]`,

constructed in `CyclotomicZHatBaseChange`.

This file first constructs the idele-level map

`(1 / f_K) v_ℚ ∘ N_{K/ℚ} : I_K → ZHat`.

The factor `f_K` is removed only after proving that the unnormalized
value lies in the actual subgroup `f_K ZHat`.  This file stops at that
idele-level construction.  Descent from `I_K` to `C_K`, together with
the resulting integer-value and norm-range identities, requires the
genuine cyclotomic principal-idele formula and is the next
source-producing frontier; no quotient projection or abstract valuation
hypothesis is substituted for it here.
-/

noncomputable section

open scoped Topology

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation

/-- Evaluating the rational cyclotomic idele value applies the fixed
Galois-to-`ZHat` equivalence to the rational global Artin image. -/
@[simp]
theorem rationalCyclotomicZHatIdeleValue_apply
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValue a =
      rationalCyclotomicZHatFieldGalEquivZHat
        (rationalCyclotomicZHatGlobalArtin a) :=
  rfl

variable (K : Type) [Field K] [NumberField K]

local instance instIsAbelianGaloisRatSubtypeSeparableClosureMemIntermediateFieldRationalCyclotomicZHatField
    (E : FiniteGaloisIntermediateField
      ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois ℚ E :=
  IsAbelianGalois.of_algHom E.toIntermediateField.val

/-- On the actual cyclotomic compositum over `K`, the chosen
local-factor product restricts to the rational cyclotomic Artin symbol
of the ordinary idele norm. -/
@[simp]
theorem
    numberFieldCyclotomicZHatCompositumRestriction_infiniteGlobalArtinMonoidHom
    (a : IdeleGroup K) :
    numberFieldCyclotomicZHatCompositumRestriction K
        (infiniteGlobalArtinMonoidHom K
          (numberFieldCyclotomicZHatCompositum K) a) =
      rationalCyclotomicZHatGlobalArtin
        (IdeleGroup.norm ℚ K a) := by
  apply
    (InfiniteGalois.continuousMulEquivToLimit
      ℚ rationalCyclotomicZHatField).injective
  apply Subtype.ext
  funext Eop
  let E := Eop.unop
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  let P :=
    numberFieldCyclotomicZHatFiniteGaloisLayerInCompositum K E
  let : NumberField P :=
    numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField K E
  let : Algebra E P :=
    rationalCyclotomicZHatFiniteLayerInCompositum_algebra K E
  let : SMul E P :=
    rationalCyclotomicZHatFiniteLayerInCompositum_smul K E
  let : Module E P := Algebra.toModule
  let : IsScalarTower ℚ E P :=
    rationalCyclotomicZHatFiniteLayerInCompositum_scalarTower K E
  let : IsAbelianGalois K P :=
    numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois K E
  have hcomm :
      (IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E K P).comp
          (globalArtinMonoidHom
            (K := K) (L := P)) =
        (globalArtinMonoidHom
          (K := ℚ) (L := E)).comp
            (IdeleGroup.norm ℚ K) := by
    have hr :
        IntermediateField.restrictRestrictAlgEquivMapHom
            ℚ E K P =
          (AlgEquiv.restrictNormalHom E).comp
            (AlgEquiv.restrictScalarsHom ℚ) := by
      ext σ x
      exact rfl
    rw [hr]
    exact
      globalArtinMonoidHom_norm_restriction
        (K := ℚ) (L := E)
        (K' := K)
        (L' := P)
  have hPProjection :
      AlgEquiv.restrictNormalHom P
          (infiniteGlobalArtinMonoidHom K
            (numberFieldCyclotomicZHatCompositum K) a) =
        globalArtinMonoidHom (K := K) (L := P) a :=
    restrictNormalHom_infiniteGlobalArtinMonoidHom
      K (numberFieldCyclotomicZHatCompositum K) a P
  have hQProjection :
      AlgEquiv.restrictNormalHom E
          (rationalCyclotomicZHatGlobalArtin
            (IdeleGroup.norm ℚ K a)) =
        globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) :=
    restrictNormalHom_rationalCyclotomicZHatGlobalArtin
      (IdeleGroup.norm ℚ K a) E
  change
    AlgEquiv.restrictNormalHom E
        (numberFieldCyclotomicZHatCompositumRestriction K
          (infiniteGlobalArtinMonoidHom K
            (numberFieldCyclotomicZHatCompositum K) a)) =
      AlgEquiv.restrictNormalHom E
        (rationalCyclotomicZHatGlobalArtin
          (IdeleGroup.norm ℚ K a))
  calc
    AlgEquiv.restrictNormalHom E
          (numberFieldCyclotomicZHatCompositumRestriction K
            (infiniteGlobalArtinMonoidHom K
              (numberFieldCyclotomicZHatCompositum K) a)) =
        IntermediateField.restrictRestrictAlgEquivMapHom ℚ E K
          P
          (AlgEquiv.restrictNormalHom
            P
            (infiniteGlobalArtinMonoidHom K
              (numberFieldCyclotomicZHatCompositum K) a)) :=
      restrictNormalHom_numberFieldCyclotomicZHatCompositumRestriction
        K E
          (infiniteGlobalArtinMonoidHom K
            (numberFieldCyclotomicZHatCompositum K) a)
    _ = IntermediateField.restrictRestrictAlgEquivMapHom ℚ E K
          P
          (globalArtinMonoidHom
            (K := K) (L := P) a) :=
      congrArg
        (IntermediateField.restrictRestrictAlgEquivMapHom ℚ E K P)
        hPProjection
    _ = globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) :=
      DFunLike.congr_fun hcomm a
    _ = AlgEquiv.restrictNormalHom E
          (rationalCyclotomicZHatGlobalArtin
            (IdeleGroup.norm ℚ K a)) := by
      exact hQProjection.symm

/-- The rational normalization factor is one:
`[ℚ ∩ ℚ̃ : ℚ] = 1`. -/
@[simp]
theorem cyclotomicZHatIntersectionDegree_rat :
    cyclotomicZHatIntersectionDegree ℚ = 1 :=
  Nat.dvd_one.mp (by
    simpa using
      (cyclotomicZHatIntersectionDegree_dvd_finrank ℚ))

/-- The unnormalized composite
`v_ℚ ∘ N_{K/ℚ}`, in additive notation. -/
noncomputable def cyclotomicZHatNormComposite :
    Additive (IdeleGroup K) →+ ZHat :=
  MonoidHom.toAdditive
    (rationalCyclotomicZHatIdeleValue.toMonoidHom.comp
      (IdeleGroup.norm ℚ K))

/-- The additive norm composite evaluates by taking the ordinary idele
norm and then the rational cyclotomic idele value. -/
@[simp]
theorem cyclotomicZHatNormComposite_apply
    (a : IdeleGroup K) :
    cyclotomicZHatNormComposite K (Additive.ofMul a) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue
          (IdeleGroup.norm ℚ K a)) :=
  rfl

/-- The ordinary norm `N_{K/ℚ}` factors through the determinant norm
from the actual intersection `K ∩ ℚ̃`.  This is determinant-norm
transitivity in the fixed-bottom-field tower presentation. -/
theorem
    ideleNorm_mem_cyclotomicZHatIntersection_relativeIdeleNorm_range
    (a : IdeleGroup K) :
    let hle :
        numberFieldCyclotomicZHatIntersection K ≤
          rationalCyclotomicZHatField :=
      inf_le_right
    let E :=
      (numberFieldCyclotomicZHatIntersection K).restrict hle
    letI : FiniteDimensional ℚ E :=
      (IntermediateField.restrictAlgEquiv hle).toLinearEquiv.finiteDimensional
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    IdeleGroup.norm ℚ K a ∈
      (RelativeIdeleGroup.norm ℚ E).range := by
  let hle :
      numberFieldCyclotomicZHatIntersection K ≤
        rationalCyclotomicZHatField :=
    inf_le_right
  let E :=
    (numberFieldCyclotomicZHatIntersection K).restrict hle
  let : FiniteDimensional ℚ E :=
    (IntermediateField.restrictAlgEquiv hle).toLinearEquiv.finiteDimensional
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  let eEK : E →ₐ[ℚ] K :=
    (numberFieldCyclotomicZHatIntersectionEmbedding K).comp
      (IntermediateField.restrictAlgEquiv hle).symm.toAlgHom
  let : Algebra E K :=
    eEK.toRingHom.toAlgebra
  let : IsScalarTower ℚ E K :=
    IsScalarTower.of_algebraMap_eq'
      eEK.comp_algebraMap.symm
  let : FiniteDimensional E K :=
    FiniteDimensional.right ℚ E K
  let b : RelativeIdeleGroup ℚ K :=
    (relativeIdeleBaseChangeMulEquiv
      (K := ℚ) (L := K)).symm a
  let t : TowerRelativeIdeleGroup ℚ E K :=
    (towerRelativeIdeleEquiv ℚ E K).symm b
  refine
    ⟨TowerRelativeIdeleGroup.norm ℚ E K t,
      ?_⟩
  calc
    RelativeIdeleGroup.norm ℚ E
          (TowerRelativeIdeleGroup.norm
            ℚ E K t) =
        RelativeIdeleGroup.norm ℚ K
          (towerRelativeIdeleEquiv
            ℚ E K t) :=
      TowerRelativeIdeleGroup.norm_transitive_flatten ℚ E K t
    _ = RelativeIdeleGroup.norm ℚ K b := by
      rw [show
        towerRelativeIdeleEquiv ℚ E K t = b by
          simp [t]]
    _ = IdeleGroup.norm ℚ K
          (relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K) b) :=
      (IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv
        ℚ K b).symm
    _ = IdeleGroup.norm ℚ K a := by
      rw [show
        relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K) b = a by
          simp [b]]

/-- The infinite rational Artin symbol of `N_{K/ℚ}(a)` fixes the actual
intersection `K ∩ ℚ̃`. -/
theorem
    rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
    (a : IdeleGroup K) :
    rationalCyclotomicZHatGlobalArtin
          (IdeleGroup.norm ℚ K a) ∈
      ((numberFieldCyclotomicZHatIntersection K).restrict
        (show
          numberFieldCyclotomicZHatIntersection K ≤
            rationalCyclotomicZHatField from
          inf_le_right)).fixingSubgroup := by
  let hle :
      numberFieldCyclotomicZHatIntersection K ≤
        rationalCyclotomicZHatField :=
    inf_le_right
  let E₀ :=
    (numberFieldCyclotomicZHatIntersection K).restrict hle
  let : FiniteDimensional ℚ E₀ :=
    (IntermediateField.restrictAlgEquiv hle).toLinearEquiv.finiteDimensional
  let : NumberField E₀ :=
    NumberField.of_module_finite ℚ E₀
  let : IsAbelianGalois ℚ rationalCyclotomicZHatField :=
    rationalCyclotomicZHatField_isAbelianGalois
  let inclusion : E₀ →ₐ[ℚ] rationalCyclotomicZHatField :=
    E₀.val.toRingHom.toRatAlgHom
  let E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField :=
    { toIntermediateField := E₀
      finiteDimensional := inferInstance
      isGalois :=
        (IsAbelianGalois.of_algHom (K := ℚ) (L := E₀)
          (M := rationalCyclotomicZHatField) inclusion).toIsGalois }
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  have hnorm :
      IdeleGroup.norm ℚ K a ∈
        (RelativeIdeleGroup.norm ℚ E).range := by
    change
      IdeleGroup.norm ℚ K a ∈
        (RelativeIdeleGroup.norm ℚ E₀).range
    simpa only [E₀, hle] using
      ideleNorm_mem_cyclotomicZHatIntersection_relativeIdeleNorm_range
        K a
  obtain ⟨z, hz⟩ := hnorm
  let : IsAbelianGalois ℚ E :=
    IsAbelianGalois.of_algHom (K := ℚ) (L := E)
      (M := rationalCyclotomicZHatField)
      (show E →ₐ[ℚ] rationalCyclotomicZHatField from
        E.toIntermediateField.val.toRingHom.toRatAlgHom)
  have hfinite :
      globalArtinMonoidHom
          (K := ℚ) (L := E)
          (IdeleGroup.norm ℚ K a) =
        1 := by
    rw [← hz]
    exact
      globalArtinMonoidHom_relativeIdeleNorm_eq_one
        (K := ℚ) (L := E) z
  change
    rationalCyclotomicZHatGlobalArtin
          (IdeleGroup.norm ℚ K a) ∈
      E.fixingSubgroup
  rw [
    FiniteGaloisIntermediateField.mem_fixingSubgroup_iff]
  calc
    AlgEquiv.restrictNormalHom E
          (rationalCyclotomicZHatGlobalArtin
            (IdeleGroup.norm ℚ K a)) =
        globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) :=
      restrictNormalHom_rationalCyclotomicZHatGlobalArtin
        (IdeleGroup.norm ℚ K a) E
    _ = 1 := hfinite

/-- The unnormalized value `v_ℚ(N_{K/ℚ}(a))` lies in the actual
subgroup `f_K ZHat`. -/
theorem cyclotomicZHatNormComposite_mem_mulNat_range
    (a : Additive (IdeleGroup K)) :
    cyclotomicZHatNormComposite K a ∈
      (zHatMulNat
        (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range := by
  let σ :=
    rationalCyclotomicZHatGlobalArtin
      (IdeleGroup.norm ℚ K (Additive.toMul a))
  have hfix :
      σ ∈
        ((numberFieldCyclotomicZHatIntersection K).restrict
          (show
            numberFieldCyclotomicZHatIntersection K ≤
              rationalCyclotomicZHatField from
            inf_le_right)).fixingSubgroup := by
    exact
      rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
        K (Additive.toMul a)
  have hmap :
      rationalCyclotomicZHatFieldGalEquivZHat σ ∈
        ((numberFieldCyclotomicZHatIntersection K).restrict
          (show
            numberFieldCyclotomicZHatIntersection K ≤
              rationalCyclotomicZHatField from
            inf_le_right)).fixingSubgroup.map
          rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom :=
    ⟨σ, hfix, rfl⟩
  have hadd :
      Multiplicative.toAdd
          (rationalCyclotomicZHatFieldGalEquivZHat σ) ∈
        Subgroup.toAddSubgroup'
          (((numberFieldCyclotomicZHatIntersection K).restrict
            (show
              numberFieldCyclotomicZHatIntersection K ≤
                rationalCyclotomicZHatField from
              inf_le_right)).fixingSubgroup.map
          rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom) := by
    rw [Subgroup.mem_toAddSubgroup']
    simpa using hmap
  rw [
    rationalCyclotomicZHatFieldGal_fixingSubgroup_image_eq_mulNat_range
      K] at hadd
  change
    Multiplicative.toAdd
        (rationalCyclotomicZHatFieldGalEquivZHat σ) ∈
      (zHatMulNat
        (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range
  exact hadd

/-- The unnormalized composite, with codomain restricted to the actual
multiple subgroup `f_K ZHat`. -/
noncomputable def cyclotomicZHatNormCompositeInMulNatRange :
    Additive (IdeleGroup K) →+
      (zHatMulNat
        (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range :=
  (cyclotomicZHatNormComposite K).codRestrict
    (zHatMulNat
    (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range
    (cyclotomicZHatNormComposite_mem_mulNat_range K)

/-- The normalized cyclotomic value on ideles:
`(1 / f_K) v_ℚ ∘ N_{K/ℚ}`. -/
noncomputable def normalizedCyclotomicZHatIdeleValue :
    Additive (IdeleGroup K) →+ ZHat :=
  (zHatDivide
    (cyclotomicZHatIntersectionDegree K)
    (cyclotomicZHatIntersectionDegree_pos K)).toAddMonoidHom.comp
      (cyclotomicZHatNormCompositeInMulNatRange K)

/-- The defining normalization identity
`f_K v_K(a) = v_ℚ(N_{K/ℚ}(a))` at the idele level. -/
theorem cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleValue
    (a : Additive (IdeleGroup K)) :
    cyclotomicZHatIntersectionDegree K •
        normalizedCyclotomicZHatIdeleValue K a =
      cyclotomicZHatNormComposite K a := by
  exact
    zHatMulNat_zHatDivide
      (cyclotomicZHatIntersectionDegree K)
      (cyclotomicZHatIntersectionDegree_pos K)
      (cyclotomicZHatNormCompositeInMulNatRange K a)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleValueTopology
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Topology of the rational cyclotomic idele value

The rational cyclotomic idele value is constructed multiplicatively in
`CyclotomicIdeleValue`.  For descent to the additive idele class group and
for the valuation package, this file records its genuine continuous additive
form.  Its finite reductions give the open-kernel finite quotients which form
the profinite neighbourhood system used after principal-idèle vanishing has
been proved.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation

/-- The rational cyclotomic idele value in continuous additive notation. -/
noncomputable def rationalCyclotomicZHatIdeleValueContinuousAdd :
    Additive (IdeleGroup ℚ) →ₜ+ ZHat where
  __ :=
    rationalCyclotomicZHatIdeleValue.toMonoidHom.toAdditiveLeft
  continuous_toFun :=
    continuous_toAdd.comp
      (rationalCyclotomicZHatIdeleValue.continuous_toFun.comp
        continuous_toMul)

/-- Evaluation of the continuous additive rational cyclotomic value agrees
with the original multiplicative value. -/
@[simp]
theorem rationalCyclotomicZHatIdeleValueContinuousAdd_apply
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValueContinuousAdd
        (Additive.ofMul a) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue a) :=
  rfl

/-- Reduction of the rational cyclotomic idele value modulo a positive
integer, as an actual continuous additive homomorphism. -/
noncomputable def rationalCyclotomicZHatIdeleValueReduction
    (n : ℕ) (hn : 0 < n) :
    Additive (IdeleGroup ℚ) →ₜ+ ZMod n :=
  (zHatReduction n hn).comp
    rationalCyclotomicZHatIdeleValueContinuousAdd

/-- Evaluation of a finite reduction is reduction of the original
cyclotomic value. -/
@[simp]
theorem rationalCyclotomicZHatIdeleValueReduction_apply
    (n : ℕ) (hn : 0 < n) (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValueReduction n hn
        (Additive.ofMul a) =
      zHatReduction n hn
        (Multiplicative.toAdd
          (rationalCyclotomicZHatIdeleValue a)) :=
  rfl

variable (K : Type) [Field K] [NumberField K]

/-- The unnormalized cyclotomic norm composite, bundled with its actual
continuity.  Continuity here uses the global idele norm rather than a
quotient-level substitute. -/
noncomputable def cyclotomicZHatNormCompositeContinuous :
    Additive (IdeleGroup K) →ₜ+ ZHat where
  __ := cyclotomicZHatNormComposite K
  continuous_toFun := by
    change
      Continuous
        (fun a : Additive (IdeleGroup K) =>
          Multiplicative.toAdd
            (rationalCyclotomicZHatIdeleValue
              (IdeleGroup.norm ℚ K (Additive.toMul a))))
    exact
      continuous_toAdd.comp
        (rationalCyclotomicZHatIdeleValue.continuous_toFun.comp
          ((IdeleGroup.norm_continuous ℚ K).comp
            continuous_toMul))

/-- The continuous norm composite agrees pointwise with the underlying
unnormalized cyclotomic norm composite. -/
@[simp]
theorem cyclotomicZHatNormCompositeContinuous_apply
    (a : IdeleGroup K) :
    cyclotomicZHatNormCompositeContinuous K (Additive.ofMul a) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue
          (IdeleGroup.norm ℚ K a)) :=
  rfl

/-- The unnormalized composite, continuously restricted to its actual
multiple subgroup `f_K ℤ̂`. -/
noncomputable def cyclotomicZHatNormCompositeInMulNatRangeContinuous :
    Additive (IdeleGroup K) →ₜ+
      (zHatMulNat
        (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range where
  __ := cyclotomicZHatNormCompositeInMulNatRange K
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (cyclotomicZHatNormCompositeContinuous K).continuous_toFun

/-- Coercing the continuous range-restricted norm composite recovers the
underlying cyclotomic norm composite. -/
@[simp]
theorem cyclotomicZHatNormCompositeInMulNatRangeContinuous_apply
    (a : Additive (IdeleGroup K)) :
    (cyclotomicZHatNormCompositeInMulNatRangeContinuous K a :
        ZHat) =
      cyclotomicZHatNormComposite K a :=
  rfl

/-- The normalized cyclotomic value on ideles as a genuine continuous
additive homomorphism. -/
noncomputable def normalizedCyclotomicZHatIdeleValueContinuous :
    Additive (IdeleGroup K) →ₜ+ ZHat :=
  (zHatDivide
      (cyclotomicZHatIntersectionDegree K)
      (cyclotomicZHatIntersectionDegree_pos K)).comp
    (cyclotomicZHatNormCompositeInMulNatRangeContinuous K)

/-- The continuous normalized cyclotomic value agrees pointwise with its
underlying additive homomorphism. -/
@[simp]
theorem normalizedCyclotomicZHatIdeleValueContinuous_apply
    (a : Additive (IdeleGroup K)) :
    normalizedCyclotomicZHatIdeleValueContinuous K a =
      normalizedCyclotomicZHatIdeleValue K a :=
  rfl

/-- The normalized cyclotomic value in continuous multiplicative notation.
This is the source homomorphism which descends through the principal-idèle
quotient once the rational principal product formula has been established. -/
noncomputable def normalizedCyclotomicZHatIdeleValueContinuousMul :
    IdeleGroup K →ₜ* Multiplicative ZHat where
  toMonoidHom :=
    AddMonoidHom.toMultiplicativeRight
      (normalizedCyclotomicZHatIdeleValueContinuous K).toAddMonoidHom
  continuous_toFun :=
    continuous_ofAdd.comp
      ((normalizedCyclotomicZHatIdeleValueContinuous K).continuous_toFun.comp
        continuous_toAdd)

/-- The multiplicative continuous normalized value is the multiplicative
form of the underlying additive normalized value. -/
@[simp]
theorem normalizedCyclotomicZHatIdeleValueContinuousMul_apply
    (a : IdeleGroup K) :
    normalizedCyclotomicZHatIdeleValueContinuousMul K a =
      Multiplicative.ofAdd
        (normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a)) :=
  rfl

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicPrincipalIdele
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeInMulNatRangeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuousMul_apply _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueContinuousAdd_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueReduction_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Principal ideles and the rational cyclotomic value

This file isolates the part of the rational principal-idele product
formula which follows from the existing archimedean reciprocity API.
Every rational idele is split into its archimedean and finite parts.
The archimedean part has Artin image of order at most two at every
finite layer; the actual Galois group of the rational `ZHat`-extension
is torsion-free, so its image in that extension is trivial.

Consequently the rational cyclotomic value of a principal idele is
exactly the value of its finite part.  At every finite cyclotomic layer
that remaining value is the genuine finite product of the chosen local
Artin maps.  Proving that product trivial requires a pointwise
compatibility theorem between the chosen finite-place Artin map and
the explicit cyclotomic action; no such compatibility is assumed here.
-/

open scoped BigOperators Classical NumberField IsMulCommutative
open NumberField IsDedekindDomain ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrimePowerNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrimePowerIsGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrimePowerIsAbelianGalois
local instance localInst_r22ff4b_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
noncomputable local instance
    cyclotomicPrincipalLevelIsAbelianGalois_r22ff4b_1
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) := by
  have : IsGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
    inferInstance
  let e :=
    IsCyclotomicExtension.Rat.galEquivZMod
      (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)
  exact
    { is_comm.comm σ τ := by
        apply e.injective
        simp only [map_mul]
        exact mul_comm _ _ }
/-- The archimedean part of a rational idele, with all finite
components replaced by one. -/
def rationalIdeleArchimedeanPart
    (a : IdeleGroup ℚ) :
    IdeleGroup ℚ :=
  (a.1, 1)

/-- The finite part of a rational idele, with its archimedean
component replaced by one. -/
def rationalIdeleFinitePart
    (a : IdeleGroup ℚ) :
    IdeleGroup ℚ :=
  (1, a.2)

/-- The archimedean part preserves every infinite component. -/
@[simp]
theorem rationalIdeleArchimedeanPart_infiniteComponent
    (a : IdeleGroup ℚ)
    (v : InfinitePlace ℚ) :
    IdeleGroup.infiniteComponent v
        (rationalIdeleArchimedeanPart a) =
      IdeleGroup.infiniteComponent v a :=
  rfl

/-- Every finite component of the archimedean part is one. -/
@[simp]
theorem rationalIdeleArchimedeanPart_finiteComponent
    (a : IdeleGroup ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    IdeleGroup.finiteComponent v
        (rationalIdeleArchimedeanPart a) =
      1 :=
  rfl

/-- Every infinite component of the finite part is one. -/
@[simp]
theorem rationalIdeleFinitePart_infiniteComponent
    (a : IdeleGroup ℚ)
    (v : InfinitePlace ℚ) :
    IdeleGroup.infiniteComponent v
        (rationalIdeleFinitePart a) =
      1 :=
  rfl

/-- The finite part preserves every finite component. -/
@[simp]
theorem rationalIdeleFinitePart_finiteComponent
    (a : IdeleGroup ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    IdeleGroup.finiteComponent v
        (rationalIdeleFinitePart a) =
      IdeleGroup.finiteComponent v a :=
  rfl

/-- The archimedean and finite parts multiply back to the original
rational idele. -/
theorem rationalIdeleArchimedeanPart_mul_finitePart
    (a : IdeleGroup ℚ) :
    rationalIdeleArchimedeanPart a *
        rationalIdeleFinitePart a =
      a := by
  ext <;> simp [rationalIdeleArchimedeanPart,
    rationalIdeleFinitePart]

/-- At a finite abelian layer, the global Artin image of the
archimedean part of a rational idele has order at most two. -/
theorem globalArtinMonoidHom_rationalIdeleArchimedeanPart_sq
    {L : Type}
    [Field L] [NumberField L] [Algebra ℚ L]
    [IsAbelianGalois ℚ L]
    (a : IdeleGroup ℚ) :
    globalArtinMonoidHom
          (K := ℚ) (L := L)
          (rationalIdeleArchimedeanPart a) ^ 2 =
      1 := by
  rw [globalArtinMonoidHom_apply, Fintype.prod_unique]
  have hfinite :
      (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        chosenFinitePlaceArtinMonoidHom
          (K := ℚ) (L := L) v
          (IdeleGroup.finiteComponent v
            (rationalIdeleArchimedeanPart a))) =
        1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [rationalIdeleArchimedeanPart_finiteComponent,
      map_one]
  rw [hfinite, mul_one]
  rw [show (default : InfinitePlace ℚ) = Rat.infinitePlace by
    exact Subsingleton.elim _ _]
  rw [← map_pow]
  apply
    chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
      (K := ℚ) (L := L)
      Rat.infinitePlace Rat.isReal_infinitePlace
  have hne :
      InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace
          ((IdeleGroup.infiniteComponent
            Rat.infinitePlace
            (rationalIdeleArchimedeanPart a) :
              Rat.infinitePlace.Completionˣ) :
            Rat.infinitePlace.Completion) ≠
        0 := by
    exact
      (map_ne_zero
        (InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace)).2
        (Units.ne_zero
          (IdeleGroup.infiniteComponent
            Rat.infinitePlace
            (rationalIdeleArchimedeanPart a)))
  simpa only [Units.val_pow_eq_pow_val, map_pow] using
    sq_pos_of_ne_zero hne

/-- The actual rational `ZHat` Artin homomorphism kills every idele
supported at the archimedean place.  The finite-layer images have
order at most two, while the inverse-limit Galois group is
torsion-free. -/
@[simp]
theorem
    rationalCyclotomicZHatGlobalArtin_rationalIdeleArchimedeanPart
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatGlobalArtin
        (rationalIdeleArchimedeanPart a) =
      1 := by
  let _
      (E :
        FiniteGaloisIntermediateField
          ℚ rationalCyclotomicZHatField) :
      NumberField E :=
    NumberField.of_module_finite ℚ E
  let _
      (E :
        FiniteGaloisIntermediateField
          ℚ rationalCyclotomicZHatField) :
      IsAbelianGalois ℚ E :=
    IsAbelianGalois.of_algHom E.toIntermediateField.val
  have hsq :
      rationalCyclotomicZHatGlobalArtin
          (rationalIdeleArchimedeanPart a) ^ 2 =
        1 := by
    have happly :
        InfiniteGalois.continuousMulEquivToLimit
            ℚ rationalCyclotomicZHatField
            (rationalCyclotomicZHatGlobalArtin
              (rationalIdeleArchimedeanPart a)) =
          infiniteGlobalArtinToLimit
            ℚ rationalCyclotomicZHatField
            (rationalIdeleArchimedeanPart a) := by
      exact
        (InfiniteGalois.continuousMulEquivToLimit
          ℚ rationalCyclotomicZHatField).apply_symm_apply _
    apply
      (InfiniteGalois.continuousMulEquivToLimit
        ℚ rationalCyclotomicZHatField).injective
    rw [map_pow, happly, map_one]
    apply Subtype.ext
    funext E
    exact
      globalArtinMonoidHom_rationalIdeleArchimedeanPart_sq
        (L := E.unop) a
  exact
    (pow_left_injective
      (M :=
        rationalCyclotomicZHatField ≃ₐ[ℚ]
          rationalCyclotomicZHatField)
      (n := 2) (by norm_num))
        (by simpa using hsq)

/-- The rational cyclotomic value kills the archimedean part of every
rational idele. -/
@[simp]
theorem
    rationalCyclotomicZHatIdeleValue_rationalIdeleArchimedeanPart
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValue
        (rationalIdeleArchimedeanPart a) =
      1 := by
  rw [rationalCyclotomicZHatIdeleValue_apply,
    rationalCyclotomicZHatGlobalArtin_rationalIdeleArchimedeanPart,
    map_one]

/-- The rational cyclotomic value depends only on the finite part of
an idele. -/
theorem rationalCyclotomicZHatIdeleValue_eq_finitePart
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValue a =
      rationalCyclotomicZHatIdeleValue
        (rationalIdeleFinitePart a) := by
  calc
    rationalCyclotomicZHatIdeleValue a =
        rationalCyclotomicZHatIdeleValue
          (rationalIdeleArchimedeanPart a *
            rationalIdeleFinitePart a) :=
      congrArg rationalCyclotomicZHatIdeleValue
        (rationalIdeleArchimedeanPart_mul_finitePart a).symm
    _ = rationalCyclotomicZHatIdeleValue
          (rationalIdeleArchimedeanPart a) *
        rationalCyclotomicZHatIdeleValue
          (rationalIdeleFinitePart a) :=
      (rationalCyclotomicZHatIdeleValue).map_mul _ _
    _ = rationalCyclotomicZHatIdeleValue
          (rationalIdeleFinitePart a) := by
      rw [
        rationalCyclotomicZHatIdeleValue_rationalIdeleArchimedeanPart,
        one_mul]

/-- Principal-idele evaluation reduced to its genuine finite local
part. -/
theorem
    rationalCyclotomicZHatIdeleValue_principalIdele_eq_finitePart
    (x : ℚˣ) :
    rationalCyclotomicZHatIdeleValue
        (IdeleGroup.principalIdele ℚ x) =
      rationalCyclotomicZHatIdeleValue
        (rationalIdeleFinitePart
          (IdeleGroup.principalIdele ℚ x)) :=
  rationalCyclotomicZHatIdeleValue_eq_finitePart
    (IdeleGroup.principalIdele ℚ x)

/-- The unnormalized value on a principal idele over a number field
is the rational cyclotomic value of the finite part of its field-norm
principal idele. -/
theorem cyclotomicZHatNormComposite_principalIdele_eq_finitePart
    (K : Type) [Field K] [NumberField K]
    (x : Kˣ) :
    cyclotomicZHatNormComposite K
        (Additive.ofMul
          (IdeleGroup.principalIdele K x)) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue
          (rationalIdeleFinitePart
            (IdeleGroup.principalIdele ℚ
              (Units.map (Algebra.norm ℚ) x)))) := by
  rw [cyclotomicZHatNormComposite_apply,
    IdeleGroup.norm_principalIdele,
    rationalCyclotomicZHatIdeleValue_principalIdele_eq_finitePart]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedChangedStandardUnramified
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedChangedUniformizerFixedField_nontriviallyNormedField _root_.LubinTate.padicCompletedChangedUniformizerFixedField_valuativeRel _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsNonarchimedeanLocalField _root_.chosenFinitePlaceBaseValuativeRel _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- The changed prime element is a uniformizer both in the changed fixed
field and in the finite standard/changed compositum, when both finite fields
carry their canonical p-adic spectral valuations. -/
theorem
    padicCompletedChangedUniformizerPrimeElement_isUniformizer_in_changedField_and_compositum
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
    (localCompleteDVF D).valuation.IsUniformizer
        (padicCompletedChangedUniformizerPrimeElement p u n : D) ∧
      (localCompleteDVF M).valuation.IsUniformizer
        (algebraMap D M
          (padicCompletedChangedUniformizerPrimeElement p u n)) := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let A := padicCompletedUnramifiedField p
  let E := padicCompletedLevelField p n
  let padicBase := (padicLocalField p).toCompleteDVF
  let canonicalBase := localCompleteDVF ℚ_[p]
  let coefficient := padicCompletedUnramifiedCompleteDVF p
  let ambient := padicCompletedLevelCompleteDVF p n
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
      Valuation.HasExtension (ValuativeRel.valuation ℚ_[p])
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension ℚ_[p] M
  let :
      canonicalBase.valuation.HasExtension
        (localCompleteDVF D).valuation :=
    localCompleteDVFValuation_hasExtension ℚ_[p] D
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
  let : canonicalBase.valuation.HasExtension ambient.valuation :=
    localCompleteDVFValuation_hasExtension_of_padicLocalField
      p ambient.valuation
  let inclusionD : D →+* E := D.val.toRingHom
  have inclusionD_comp :
      inclusionD.comp (algebraMap ℚ_[p] D) =
        algebraMap ℚ_[p] E := by
    ext x
    exact D.val.commutes x
  let :
      canonicalBase.valuation.HasExtension
        (ambient.valuation.comap inclusionD) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusionD inclusionD_comp
  let inclusionM : M →+* E := M.val.toRingHom
  have inclusionM_comp :
      inclusionM.comp (algebraMap ℚ_[p] M) =
        algebraMap ℚ_[p] E := by
    ext x
    exact M.val.commutes x
  let :
      canonicalBase.valuation.HasExtension
        (ambient.valuation.comap inclusionM) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusionM inclusionM_comp
  have hthetaAmbient :
      ambient.valuation.IsUniformizer
        (((padicChangedUniformizerThetaValue p u n :
          ambient.valuationSubring) : E)) :=
    padicChangedUniformizerThetaValue_isUniformizer p u n
  have hthetaD :
      (localCompleteDVF D).valuation.IsUniformizer
        (padicCompletedChangedUniformizerPrimeElement p u n : D) := by
    apply
      isUniformizer_of_ambient_image_isUniformizer
        canonicalBase (localCompleteDVF D) ambient inclusionD
    change
      ambient.valuation.IsUniformizer
        (((padicChangedUniformizerThetaValue p u n :
          ambient.valuationSubring) : E))
    exact hthetaAmbient
  have hthetaM :
      (localCompleteDVF M).valuation.IsUniformizer
        (algebraMap D M
          (padicCompletedChangedUniformizerPrimeElement p u n)) := by
    apply
      isUniformizer_of_ambient_image_isUniformizer
        canonicalBase (localCompleteDVF M) ambient inclusionM
    change
      ambient.valuation.IsUniformizer
        (((padicChangedUniformizerThetaValue p u n :
          ambient.valuationSubring) : E))
    exact hthetaAmbient
  exact ⟨hthetaD, hthetaM⟩

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_LubinTateApplication_PadicMultiplicativeArtinComparison
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsNonarchimedeanLocalField _root_.chosenFinitePlaceBaseValuativeRel _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.zHatUnitsDecomposition_freeCoordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
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

/-- The negative changed-uniformizer prime element as an actual unit of its
completed fixed field.  Its norm is the changed base uniformizer `u p`. -/
noncomputable def padicCompletedChangedUniformizerNegativePrimeUnit
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    (padicCompletedChangedUniformizerFixedField p u n)ˣ :=
  Units.mk0
    (-padicCompletedChangedUniformizerPrimeElement p u n)
    (by
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
      apply neg_ne_zero.mpr
      exact
        (padicCompletedChangedUniformizerPrimeElement_isUniformizer_in_changedField_and_compositum
          p u n).1.ne_zero)

/-- The underlying field element of the negative changed prime unit is
`-theta`. -/
@[simp]
theorem padicCompletedChangedUniformizerNegativePrimeUnit_coe
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    (padicCompletedChangedUniformizerNegativePrimeUnit p n u :
      padicCompletedChangedUniformizerFixedField p u n) =
      -padicCompletedChangedUniformizerPrimeElement p u n :=
  rfl

section PadicStandardLevelRestriction

theorem padicArtinStandardLevel_normal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Normal ℚ_[p]
      (standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :=
  (standardLubinTateLevelField_isGalois (F := padicLocalField p)
    (padicMultiplicativeLubinTateSeries_isUniformizer p) n).to_normal

attribute [local instance] padicArtinStandardLevel_normal

end PadicStandardLevelRestriction

end LocalClassFieldTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul
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
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_r22ff4b_1
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsNonarchimedeanLocalField
/-- The standard multiplicative Lubin--Tate field at level `n`. -/
abbrev RationalCyclotomicPrincipalPrimePadicLevel
    (p : Nat.Primes) (n : ℕ) :=
  standardLubinTateLevelField
    (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n

end Reciprocity
end GlobalClassFieldTheory
end
end


