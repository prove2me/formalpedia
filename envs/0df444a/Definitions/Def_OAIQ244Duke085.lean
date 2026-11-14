-- Prove2me | Definitions.Def_OAIQ244Duke085
-- name    : OAIQ244Duke085
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T00:31:42.967989+00:00
-- url     : https://prove2.me/theorems/f5771b5b-c702-412c-81cc-24eb9f923a3c
-- title:
--   Definitions bundle OAIQ244Duke085 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 43 declarations of OpenAI's Lean: 18 definitions, 19 instances and 6 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum`, `GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositumEmbedding`, `GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositumRestriction`, `GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum`, `GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositumEmbedding`, `GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositumInclusion`, `GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositumInclusionOverBase`, `GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteGaloisLayerInCompositum`, `GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum`, `GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection`, `GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersectionEmbedding`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicFullRestrictionToZHat`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositumEmbedding`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatField`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldGalEquivZHat`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositumEmbedding`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositumEmbedding`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatGlobalArtin`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange`, `GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke115` and `OAIQ244Duke116` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke088`, `OAIQ244Duke089`, `OAIQ244Duke090` and `OAIQ244Duke091`.
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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.QuotientRing
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
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
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
import Mathlib.RingTheory.RamificationInertia.Inertia
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
import Definitions.Def_OAIQ244Duke115
import Definitions.Def_OAIQ244Duke116

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional_over_extension _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.LubinTate.standardLubinTateUnitParameter_finite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_mul _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusConjugationLift_coe _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerLift_coe _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.fixedFieldNormalizedDegree_generator _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegree_generator _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusFixedField_normalizedDegreeEquiv_apply _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusMul_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.DegreeData.transferNormNaturalityTransferFrobeniusLift_coe _root_.ClassFormation.DegreeData.transferNormNaturalityTransferNormOrbitEquiv_mk _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.localBaseValuation_baseFieldUnitsEquiv _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.padicMultiplicativeLubinTateSeries_toPowerSeries _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.padicChangedUniformizerIntertwiner_coeff _root_.LubinTate.padicChangedUniformizerIntertwiner_coeff_one _root_.LubinTate.padicCompletedChangedStandardScalarEndomorphism_coeff_one _root_.LubinTate.padicCompletedChangedStandardScalarEndomorphism_one _root_.LubinTate.padicCompletedLevelPadicIntegerCoefficientHom_coe _root_.LubinTate.padicCompletedLevelPowerSeriesEval_C _root_.LubinTate.padicCompletedLevelPowerSeriesEval_X _root_.LubinTate.padicCompletedLevelPowerSeriesEval_coe _root_.LubinTate.padicCompletedLevelWittCoefficientHom_apply _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphismValue_one _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphism_coeff_one _root_.LubinTate.padicCompletedPrimitiveRootInteger_coe _root_.LubinTate.padicCompletedStandardScalarEndomorphismValue_one _root_.LubinTate.padicCompletedStandardScalarEndomorphism_one _root_.LubinTate.padicCompletedUnramifiedIntegerMap_coe _root_.LubinTate.padicStandardToMultiplicativeIntertwiner_coeff_one _root_.LubinTate.padicValuationSubringToCompletedUnramifiedWittRing_uniformizer _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.LubinTate.padicChangedUniformizerLinearCoefficient_coe _root_.LubinTate.padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
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

/-- The cyclotomic `ZHat`-extension of `ℚ`, regarded as an actual
intermediate field of `SeparableClosure ℚ`. -/
def rationalCyclotomicZHatField :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  IntermediateField.lift rationalCyclotomicTorsionFixedField

noncomputable instance rationalCyclotomicZHatField_isAbelianGalois :
    IsAbelianGalois ℚ rationalCyclotomicZHatField := by
  exact @IsAbelianGalois.of_algHom
    ℚ rationalCyclotomicZHatField rationalCyclotomicTorsionFixedField
    _ _ _ _ _
    (IntermediateField.liftAlgEquiv
      rationalCyclotomicTorsionFixedField).symm.toAlgHom
    KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois

/-- The lifted cyclotomic `ZHat`-field is normal for the ambient algebra
structure selected by ordinary Galois-theory APIs. -/
noncomputable instance rationalCyclotomicZHatField_isNormal :
    Normal ℚ rationalCyclotomicZHatField :=
  rationalCyclotomicZHatField_isAbelianGalois.toIsGalois.to_normal

/-- The cyclotomic Galois-group equivalence, transported from the nested
presentation to the copy of `ℚ̃` in `SeparableClosure ℚ`. -/
noncomputable def rationalCyclotomicZHatFieldGalEquivZHat :
    (rationalCyclotomicZHatField ≃ₐ[ℚ]
      rationalCyclotomicZHatField) ≃ₜ*
        Multiplicative ZHat := by
  let _ : T2Space
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
    krullTopology_t2
  let e :=
    IntermediateField.liftAlgEquiv
      rationalCyclotomicTorsionFixedField
  let c :
      (rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
          rationalCyclotomicTorsionFixedField) ≃ₜ*
        (rationalCyclotomicZHatField ≃ₐ[ℚ]
          rationalCyclotomicZHatField) :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.continuousMulEquivOfCompactToT2
        (AlgEquiv.autCongr e)
        (continuous_algEquiv_autCongr e)
  exact c.symm.trans
    rationalCyclotomicTorsionFixedFieldGalEquivZHat

/-- Restriction from the full rational cyclotomic field to its actual
`ZHat` torsion-fixed subfield, transported to the copy inside
`SeparableClosure ℚ`. -/
noncomputable def rationalCyclotomicFullRestrictionToZHat :
    (KummerTheory.rationalCyclotomicField ≃ₐ[ℚ]
        KummerTheory.rationalCyclotomicField) →*
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
  (AlgEquiv.autCongr
      (IntermediateField.liftAlgEquiv
        KummerTheory.rationalCyclotomicTorsionFixedField)).toMonoidHom.comp
    (@AlgEquiv.restrictNormalHom
      ℚ _ KummerTheory.rationalCyclotomicField _ _
      KummerTheory.rationalCyclotomicTorsionFixedField _ _ _ _
      KummerTheory.rationalCyclotomicTorsionFixedField_normal)

/-- The actual restriction to the lifted `ZHat`-field has coordinate
equal to the torsion-free component of the full cyclotomic character. -/
@[simp]
theorem rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction
    (σ :
      KummerTheory.rationalCyclotomicField ≃ₐ[ℚ]
        KummerTheory.rationalCyclotomicField) :
    rationalCyclotomicZHatFieldGalEquivZHat
        (rationalCyclotomicFullRestrictionToZHat σ) =
      (KummerTheory.zHatUnitsDecomposition
        (KummerTheory.rationalCyclotomicCharacterContinuousMulEquiv
          σ)).1 := by
  let _ : T2Space
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
    krullTopology_t2
  let e :=
    IntermediateField.liftAlgEquiv
      KummerTheory.rationalCyclotomicTorsionFixedField
  let c :
      (KummerTheory.rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
          KummerTheory.rationalCyclotomicTorsionFixedField) ≃ₜ*
        (rationalCyclotomicZHatField ≃ₐ[ℚ]
          rationalCyclotomicZHatField) :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.continuousMulEquivOfCompactToT2
      (AlgEquiv.autCongr e)
      (continuous_algEquiv_autCongr e)
  change
    rationalCyclotomicTorsionFixedFieldGalEquivZHat
        (c.symm
          (c
            (@AlgEquiv.restrictNormalHom
              ℚ _ KummerTheory.rationalCyclotomicField _ _
              KummerTheory.rationalCyclotomicTorsionFixedField _ _ _ _
              KummerTheory.rationalCyclotomicTorsionFixedField_normal σ))) =
      (KummerTheory.zHatUnitsDecomposition
        (KummerTheory.rationalCyclotomicCharacterContinuousMulEquiv
          σ)).1
  rw [c.symm_apply_apply,
    rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal]

variable (K : Type*) [Field K] [NumberField K]

/-- The finite intersection `K ∩ ℚ̃` inside the common separable
closure. -/
def numberFieldCyclotomicZHatIntersection :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  numberFieldInRationalSeparableClosure K ⊓
    rationalCyclotomicZHatField

/-- The intersection `K ∩ ℚ̃`, embedded back into the original number
field through the chosen copy of `K` in `SeparableClosure ℚ`. -/
noncomputable def numberFieldCyclotomicZHatIntersectionEmbedding :
    numberFieldCyclotomicZHatIntersection K →ₐ[ℚ] K :=
  (numberFieldSeparableClosureEmbedding K).equivFieldRange.symm.toAlgHom.comp
    (IntermediateField.inclusion inf_le_left)

/-- The embedding of the cyclotomic intersection into `K` commutes with
the chosen embedding of `K` into the rational separable closure. -/
@[simp]
theorem numberFieldCyclotomicZHatIntersectionEmbedding_commutes
    (x : numberFieldCyclotomicZHatIntersection K) :
    numberFieldSeparableClosureEmbedding K
        (numberFieldCyclotomicZHatIntersectionEmbedding K x) =
      (x : SeparableClosure ℚ) := by
  change
    (((numberFieldSeparableClosureEmbedding K).equivFieldRange
      ((numberFieldSeparableClosureEmbedding K).equivFieldRange.symm
        ((IntermediateField.inclusion inf_le_left) x)) :
        numberFieldInRationalSeparableClosure K) :
      SeparableClosure ℚ) =
        (x : SeparableClosure ℚ)
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- The actual compositum of the chosen copy of `K` with a finite
Galois layer of the rational cyclotomic `ZHat`-extension. -/
def numberFieldCyclotomicZHatFiniteCompositum
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  numberFieldInRationalSeparableClosure K ⊔
    IntermediateField.lift E.toIntermediateField

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositum_finiteDimensional
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional ℚ
      (numberFieldCyclotomicZHatFiniteCompositum K E) := by
  let : FiniteDimensional ℚ (IntermediateField.lift E.toIntermediateField) :=
    ((IntermediateField.liftAlgEquiv E.toIntermediateField).toLinearEquiv).finiteDimensional
  exact
    IntermediateField.finiteDimensional_sup
      (numberFieldInRationalSeparableClosure K)
      (IntermediateField.lift E.toIntermediateField)

/-- The chosen embedding of `K` into each finite cyclotomic
compositum. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteCompositumEmbedding
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    K →ₐ[ℚ] numberFieldCyclotomicZHatFiniteCompositum K E :=
  (numberFieldSeparableClosureEmbedding K).codRestrict
    (numberFieldCyclotomicZHatFiniteCompositum K E).toSubalgebra
    (fun x =>
      (show numberFieldInRationalSeparableClosure K ≤
          numberFieldCyclotomicZHatFiniteCompositum K E from
        le_sup_left)
        (show numberFieldSeparableClosureEmbedding K x ∈
            numberFieldInRationalSeparableClosure K from
          (AlgHom.mem_fieldRange).mpr ⟨x, rfl⟩))

/-- A finite cyclotomic layer embedded into its compositum with `K`. -/
noncomputable def
    rationalCyclotomicZHatFiniteLayerCompositumEmbedding
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    E →ₐ[ℚ] numberFieldCyclotomicZHatFiniteCompositum K E :=
  (IntermediateField.inclusion le_sup_right).comp
    (IntermediateField.liftAlgEquiv E.toIntermediateField).toAlgHom

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositum_algebra
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra K
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  (numberFieldCyclotomicZHatFiniteCompositumEmbedding K E).toRingHom.toAlgebra

instance
    numberFieldCyclotomicZHatFiniteCompositum_scalarTower
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ K
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  IsScalarTower.of_algebraMap_eq'
    ((numberFieldCyclotomicZHatFiniteCompositumEmbedding K E).comp_algebraMap.symm)

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositum_finiteDimensional_over_K
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional K
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  FiniteDimensional.right ℚ K
    (numberFieldCyclotomicZHatFiniteCompositum K E)

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositum_isGalois
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsGalois K
      (numberFieldCyclotomicZHatFiniteCompositum K E) := by
  let C :=
    numberFieldCyclotomicZHatFiniteCompositum K E
  let : Algebra ℚ C := C.algebra'
  let A : IntermediateField ℚ C :=
    (numberFieldInRationalSeparableClosure K).restrict
      (show
        numberFieldInRationalSeparableClosure K ≤ C from
        le_sup_left)
  let B : IntermediateField ℚ C :=
    (IntermediateField.lift E.toIntermediateField).restrict
      (show IntermediateField.lift E.toIntermediateField ≤ C from le_sup_right)
  let : Algebra ℚ B := B.algebra'
  let eK : K ≃ₐ[ℚ] A :=
    (numberFieldSeparableClosureEmbedding K).equivFieldRange.trans
      (IntermediateField.restrictAlgEquiv le_sup_left)
  let eE : E ≃ₐ[ℚ] B :=
    (IntermediateField.liftAlgEquiv E.toIntermediateField).trans
      (IntermediateField.restrictAlgEquiv le_sup_right)
  let hE : IsGalois ℚ E := E.isGalois
  let : IsGalois ℚ E := hE
  let hfiniteB : FiniteDimensional ℚ B :=
    eE.toLinearEquiv.finiteDimensional
  let hB : IsGalois ℚ B :=
    @IsGalois.of_algEquiv ℚ E _ _ B _ _ _ hE eE
  let : FiniteDimensional ℚ B := hfiniteB
  let : IsGalois ℚ B := hB
  have hsup : B ⊔ A = ⊤ := by
    apply IntermediateField.lift_injective C
    rw [IntermediateField.lift_sup,
      IntermediateField.lift_restrict,
      IntermediateField.lift_restrict,
      IntermediateField.lift_top]
    exact sup_comm _ _
  let : IsGalois A C :=
    @IsGalois.sup_right ℚ _ C _ _ B A hB hfiniteB hsup
  refine
    @IsGalois.of_equiv_equiv A C _ _ _ K C _ _ _ (by infer_instance)
      eK.symm.toRingEquiv (RingEquiv.refl C) ?_
  ext x
  have heK (y : K) :
      algebraMap K C y = algebraMap A C (eK y) := by
    apply Subtype.ext
    rfl
  simpa using
    congrArg (fun z : C => (z : SeparableClosure ℚ)) (heK (eK.symm x))

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositum_isAbelianGalois
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois K
      (numberFieldCyclotomicZHatFiniteCompositum K E) := by
  let C :=
    numberFieldCyclotomicZHatFiniteCompositum K E
  let : Algebra ℚ C := C.algebra'
  let A : IntermediateField ℚ C :=
    (numberFieldInRationalSeparableClosure K).restrict
      (show
        numberFieldInRationalSeparableClosure K ≤ C from
        le_sup_left)
  let B : IntermediateField ℚ C :=
    (IntermediateField.lift E.toIntermediateField).restrict
      (show IntermediateField.lift E.toIntermediateField ≤ C from le_sup_right)
  let : Algebra ℚ B := B.algebra'
  let eK : K ≃ₐ[ℚ] A :=
    (numberFieldSeparableClosureEmbedding K).equivFieldRange.trans
      (IntermediateField.restrictAlgEquiv le_sup_left)
  let eE : E ≃ₐ[ℚ] B :=
    (IntermediateField.liftAlgEquiv E.toIntermediateField).trans
      (IntermediateField.restrictAlgEquiv le_sup_right)
  let hE : IsGalois ℚ E := E.isGalois
  let : IsGalois ℚ E := hE
  let hfiniteB : FiniteDimensional ℚ B :=
    eE.toLinearEquiv.finiteDimensional
  let : IsAbelianGalois ℚ E :=
    IsAbelianGalois.tower_bot ℚ E rationalCyclotomicZHatField
  let hB : IsAbelianGalois ℚ B :=
    @IsAbelianGalois.of_algHom ℚ B E _ _ _ _ _ eE.symm.toAlgHom
      (IsAbelianGalois.tower_bot ℚ E rationalCyclotomicZHatField)
  let : FiniteDimensional ℚ B := hfiniteB
  let : IsAbelianGalois ℚ B := hB
  have hsup : B ⊔ A = ⊤ := by
    apply IntermediateField.lift_injective C
    rw [IntermediateField.lift_sup,
      IntermediateField.lift_restrict,
      IntermediateField.lift_restrict,
      IntermediateField.lift_top]
    exact sup_comm _ _
  let : IsGalois A C :=
    @IsGalois.sup_right ℚ _ C _ _ B A hB.toIsGalois hfiniteB hsup
  let r :
      (C ≃ₐ[A] C) →* (B ≃ₐ[ℚ] B) :=
    IntermediateField.restrictRestrictAlgEquivMapHom
      ℚ B A C
  have hr : Function.Injective r :=
    IntermediateField.restrictRestrictAlgEquivMapHom_injective B A hsup
  let : IsAbelianGalois A C :=
    { is_comm.comm := fun σ τ => by
        apply hr
        calc
          r (σ * τ) = r σ * r τ := r.map_mul σ τ
          _ = r τ * r σ := IsMulCommutative.is_comm.comm _ _
          _ = r (τ * σ) := (r.map_mul τ σ).symm }
  have heK (x : K) :
      algebraMap K C x =
        algebraMap A C (eK x) := by
    apply Subtype.ext
    rfl
  let changeBase :
      (C ≃ₐ[K] C) →* (C ≃ₐ[A] C) :=
    { toFun := fun σ =>
        { σ.toRingEquiv with
          commutes' := by
            intro y
            have hy :
                algebraMap K C (eK.symm y) =
                  algebraMap A C y := by
              simpa using heK (eK.symm y)
            rw [← hy]
            change σ (algebraMap K C (eK.symm y)) =
              algebraMap K C (eK.symm y)
            exact σ.commutes _ }
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hchangeBase :
      Function.Injective changeBase := by
    intro σ τ hστ
    apply AlgEquiv.ext
    intro x
    exact
      congrArg
        (fun f : C ≃ₐ[A] C => f x)
        hστ
  exact
    { is_comm.comm := fun σ τ => by
        apply hchangeBase
        calc
          changeBase (σ * τ) = changeBase σ * changeBase τ :=
            changeBase.map_mul σ τ
          _ = changeBase τ * changeBase σ := IsMulCommutative.is_comm.comm _ _
          _ = changeBase (τ * σ) := (changeBase.map_mul τ σ).symm }

/-- The actual compositum `Kℚ̃` inside `SeparableClosure ℚ`. -/
def numberFieldCyclotomicZHatCompositum :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  numberFieldInRationalSeparableClosure K ⊔
    rationalCyclotomicZHatField

/-- The chosen copy of `K` embedded into its actual cyclotomic
`ZHat`-compositum. -/
noncomputable def numberFieldCyclotomicZHatCompositumEmbedding :
    K →ₐ[ℚ] numberFieldCyclotomicZHatCompositum K :=
  (numberFieldSeparableClosureEmbedding K).codRestrict
    (numberFieldCyclotomicZHatCompositum K).toSubalgebra
    (fun x =>
      (show numberFieldInRationalSeparableClosure K ≤
          numberFieldCyclotomicZHatCompositum K from
        le_sup_left)
        (show numberFieldSeparableClosureEmbedding K x ∈
            numberFieldInRationalSeparableClosure K from
          (AlgHom.mem_fieldRange).mpr ⟨x, rfl⟩))

/-- The rational cyclotomic `ZHat`-field embedded into its compositum
with `K`. -/
noncomputable def rationalCyclotomicZHatCompositumEmbedding :
    rationalCyclotomicZHatField →ₐ[ℚ]
      numberFieldCyclotomicZHatCompositum K :=
  IntermediateField.inclusion le_sup_right

noncomputable instance numberFieldCyclotomicZHatCompositum_algebra :
    Algebra K (numberFieldCyclotomicZHatCompositum K) :=
  ((numberFieldCyclotomicZHatCompositumEmbedding K).toRingHom).toAlgebra

noncomputable instance rationalCyclotomicZHatCompositum_algebra :
    Algebra rationalCyclotomicZHatField
      (numberFieldCyclotomicZHatCompositum K) :=
  ((rationalCyclotomicZHatCompositumEmbedding K).toRingHom).toAlgebra

instance numberFieldCyclotomicZHatCompositum_scalarTower :
    IsScalarTower ℚ K
      (numberFieldCyclotomicZHatCompositum K) :=
  IsScalarTower.of_algebraMap_eq'
    ((numberFieldCyclotomicZHatCompositumEmbedding K).comp_algebraMap.symm)

instance rationalCyclotomicZHatCompositum_scalarTower :
    IsScalarTower ℚ rationalCyclotomicZHatField
      (numberFieldCyclotomicZHatCompositum K) :=
  IsScalarTower.of_algebraMap_eq'
    ((rationalCyclotomicZHatCompositumEmbedding K).comp_algebraMap.symm)

noncomputable instance
    numberFieldCyclotomicZHatCompositum_isGalois :
    IsGalois K (numberFieldCyclotomicZHatCompositum K) := by
  let A : IntermediateField ℚ (SeparableClosure ℚ) :=
    numberFieldInRationalSeparableClosure K
  let : Algebra A (SeparableClosure ℚ) := A.val.toAlgebra
  let rationalCyclotomicZHatFieldIsGalois :
      IsGalois ℚ rationalCyclotomicZHatField :=
    rationalCyclotomicZHatField_isAbelianGalois.toIsGalois
  let C := numberFieldCyclotomicZHatCompositum K
  let eK : K ≃ₐ[ℚ] A :=
    (numberFieldSeparableClosureEmbedding K).equivFieldRange
  have hG :
      ∀ E : FiniteGaloisIntermediateField ℚ rationalCyclotomicZHatField,
        IsGalois A
          (IntermediateField.extendScalars (F := A)
            (E := A ⊔ IntermediateField.lift E.toIntermediateField)
            le_sup_left) := by
    intro E
    let D := numberFieldCyclotomicZHatFiniteCompositum K E
    let hAD : A ≤ D := by
      dsimp only [A, D, numberFieldCyclotomicZHatFiniteCompositum]
      exact le_sup_left
    let : Algebra A D := (IntermediateField.inclusion hAD).toAlgebra
    change IsGalois A (IntermediateField.extendScalars hAD)
    have hcompat (x : K) :
        algebraMap K D x = IntermediateField.inclusion hAD (eK x) := by
      apply Subtype.ext
      rfl
    refine
      IsGalois.of_equiv_equiv
        (F := K) (E := D) (M := A) (N := D)
        (h := by infer_instance)
        (f := eK.toRingEquiv) (g := RingEquiv.refl D) ?_
    apply RingHom.ext
    intro x
    have hADmap (y : A) :
        algebraMap A D y = IntermediateField.inclusion hAD y := by
      rfl
    change algebraMap A D (eK x) = algebraMap K D x
    exact (hADmap (eK x)).trans (hcompat x).symm
  let hAC : A ≤ C := by
    dsimp only [A, C, numberFieldCyclotomicZHatCompositum]
    exact le_sup_left
  let full : IntermediateField A (SeparableClosure ℚ) :=
    IntermediateField.extendScalars hAC
  have hfull0 : IsGalois A
      (IntermediateField.extendScalars (F := A)
        (E := A ⊔ rationalCyclotomicZHatField) le_sup_left) :=
    @IntermediateField.isGalois_extendScalars_sup_of_forall_finiteGalois
      ℚ (SeparableClosure ℚ) _ _ _ A rationalCyclotomicZHatField
      rationalCyclotomicZHatFieldIsGalois hG
  have hfull_eq : full =
      IntermediateField.extendScalars (F := A)
        (E := A ⊔ rationalCyclotomicZHatField) le_sup_left := by
    dsimp only [full, hAC, C, numberFieldCyclotomicZHatCompositum]
  have hfull : IsGalois A full := by
    change IsGalois A
      (IntermediateField.extendScalars (F := A)
        (E := A ⊔ rationalCyclotomicZHatField) le_sup_left)
    exact hfull0
  let : Algebra A C := (IntermediateField.inclusion hAC).toAlgebra
  have hfull' := hfull
  change IsGalois A C at hfull'
  let : IsGalois A C := hfull'
  have hcompat (x : K) :
      algebraMap K C x =
        IntermediateField.inclusion hAC (eK x) := by
    apply Subtype.ext
    rfl
  refine
    IsGalois.of_equiv_equiv
      (F := A) (E := C) (M := K) (N := C)
      (h := hfull')
      (f := eK.symm.toRingEquiv) (g := RingEquiv.refl C) ?_
  apply RingHom.ext
  intro x
  have hACmap (y : A) :
      algebraMap A C y = IntermediateField.inclusion hAC y := by
    rfl
  have hEq : algebraMap K C (eK.symm x) = algebraMap A C x := by
    refine (hcompat (eK.symm x)).trans ?_
    rw [eK.apply_symm_apply]
    exact (hACmap x).symm
  exact hEq

noncomputable instance
    numberFieldCyclotomicZHatCompositum_isAbelianGalois :
    IsAbelianGalois K
      (numberFieldCyclotomicZHatCompositum K) := by
  let C := numberFieldCyclotomicZHatCompositum K
  let : Algebra ℚ C := C.algebra'
  let A : IntermediateField ℚ C :=
    (numberFieldInRationalSeparableClosure K).restrict
      (show
        numberFieldInRationalSeparableClosure K ≤ C from
        le_sup_left)
  let B : IntermediateField ℚ C :=
    rationalCyclotomicZHatField.restrict
      (show rationalCyclotomicZHatField ≤ C from le_sup_right)
  let : Algebra ℚ B := B.algebra'
  let eK : K ≃ₐ[ℚ] A :=
    (numberFieldSeparableClosureEmbedding K).equivFieldRange.trans
      (IntermediateField.restrictAlgEquiv le_sup_left)
  let eT : rationalCyclotomicZHatField ≃ₐ[ℚ] B :=
    IntermediateField.restrictAlgEquiv le_sup_right
  let hB : IsAbelianGalois ℚ B :=
    @IsAbelianGalois.of_algHom ℚ B rationalCyclotomicZHatField
      _ _ _ _ _ eT.symm.toAlgHom
      rationalCyclotomicZHatField_isAbelianGalois
  let : IsAbelianGalois ℚ B := hB
  have hsup : B ⊔ A = ⊤ := by
    apply IntermediateField.lift_injective C
    rw [IntermediateField.lift_sup,
      IntermediateField.lift_restrict,
      IntermediateField.lift_restrict,
      IntermediateField.lift_top]
    exact sup_comm _ _
  have heK (x : K) :
      algebraMap K C x =
        algebraMap A C (eK x) := by
    apply Subtype.ext
    rfl
  let hAC : IsGalois A C := by
    refine
      @IsGalois.of_equiv_equiv K C _ _ _ A C _ _ _ (by infer_instance)
        eK.toRingEquiv (RingEquiv.refl C) ?_
    ext x
    simpa using
      congrArg (fun z : C => (z : SeparableClosure ℚ)) (heK x).symm
  let : IsGalois A C := hAC
  let r :
      (C ≃ₐ[A] C) →* (B ≃ₐ[ℚ] B) :=
    IntermediateField.restrictRestrictAlgEquivMapHom
      ℚ B A C
  have hr : Function.Injective r :=
    IntermediateField.restrictRestrictAlgEquivMapHom_injective
      B A hsup
  let : IsAbelianGalois A C :=
    { is_comm.comm := fun σ τ => by
        apply hr
        calc
          r (σ * τ) = r σ * r τ := r.map_mul σ τ
          _ = r τ * r σ := IsMulCommutative.is_comm.comm _ _
          _ = r (τ * σ) := (r.map_mul τ σ).symm }
  let changeBase :
      (C ≃ₐ[K] C) →* (C ≃ₐ[A] C) :=
    { toFun := fun σ =>
        { σ.toRingEquiv with
          commutes' := by
            intro y
            have hy :
                algebraMap K C (eK.symm y) =
                  algebraMap A C y := by
              simpa using heK (eK.symm y)
            rw [← hy]
            change σ (algebraMap K C (eK.symm y)) =
              algebraMap K C (eK.symm y)
            exact σ.commutes _ }
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hchangeBase :
      Function.Injective changeBase := by
    intro σ τ hστ
    apply AlgEquiv.ext
    intro x
    exact
      congrArg
        (fun f : C ≃ₐ[A] C => f x)
        hστ
  exact
    { is_comm.comm := fun σ τ => by
        apply hchangeBase
        calc
          changeBase (σ * τ) = changeBase σ * changeBase τ :=
            changeBase.map_mul σ τ
          _ = changeBase τ * changeBase σ := IsMulCommutative.is_comm.comm _ _
          _ = changeBase (τ * σ) :=
            (changeBase.map_mul τ σ).symm }

/-- Inclusion of a finite cyclotomic compositum into the full
cyclotomic `ZHat`-compositum. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteCompositumInclusion
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    numberFieldCyclotomicZHatFiniteCompositum K E →ₐ[ℚ]
      numberFieldCyclotomicZHatCompositum K :=
  IntermediateField.inclusion
    (sup_le_sup le_rfl
      (IntermediateField.lift_le E.toIntermediateField))

/-- The same finite-layer inclusion, over the chosen copy of `K`. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteCompositumInclusionOverBase
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    numberFieldCyclotomicZHatFiniteCompositum K E →ₐ[K]
      numberFieldCyclotomicZHatCompositum K := by
  let f :=
    numberFieldCyclotomicZHatFiniteCompositumInclusion K E
  exact
    { f.toRingHom with
      commutes' := by
        intro x
        rfl }

/-- The finite cyclotomic compositum, as an intermediate field of the
full compositum over `K`. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteLayerInCompositum
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IntermediateField K
      (numberFieldCyclotomicZHatCompositum K) :=
  (numberFieldCyclotomicZHatFiniteCompositumInclusionOverBase K E).fieldRange

noncomputable instance
    numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional K
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
  (AlgEquiv.toLinearEquiv
    (AlgHom.equivFieldRange
      (numberFieldCyclotomicZHatFiniteCompositumInclusionOverBase K E))).finiteDimensional

noncomputable instance
    numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois K
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
  IsAbelianGalois.of_algHom
    (AlgEquiv.toAlgHom
      (AlgEquiv.symm
        (AlgHom.equivFieldRange
          (numberFieldCyclotomicZHatFiniteCompositumInclusionOverBase K E))))

noncomputable instance
    numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
  NumberField.of_module_finite K
    (numberFieldCyclotomicZHatFiniteLayerInCompositum K E)

/-- A finite rational cyclotomic layer embedded into the corresponding
finite intermediate field of the full compositum. -/
noncomputable def
    rationalCyclotomicZHatFiniteLayerInCompositumEmbedding
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    E →ₐ[ℚ]
      numberFieldCyclotomicZHatFiniteLayerInCompositum K E := by
  exact
    (AlgEquiv.toAlgHom
      (AlgEquiv.restrictScalars ℚ
        (AlgHom.equivFieldRange
          (numberFieldCyclotomicZHatFiniteCompositumInclusionOverBase K E)))).comp
      (rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E)

noncomputable instance
    rationalCyclotomicZHatFiniteLayerInCompositum_algebra
  (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra E
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
  RingHom.toAlgebra
    (AlgHom.toRingHom
      (rationalCyclotomicZHatFiniteLayerInCompositumEmbedding K E))

/-- The finite-layer scalar action on its actual image in the full
compositum. -/
noncomputable instance
    rationalCyclotomicZHatFiniteLayerInCompositum_smul
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul E
      (numberFieldCyclotomicZHatFiniteLayerInCompositum K E) :=
  Algebra.toSMul
    (self := rationalCyclotomicZHatFiniteLayerInCompositum_algebra K E)

/-- The corresponding finite layer as an object of the inverse system
of finite Galois subextensions of the full compositum. -/
noncomputable def
    numberFieldCyclotomicZHatFiniteGaloisLayerInCompositum
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteGaloisIntermediateField K
      (numberFieldCyclotomicZHatCompositum K) where
  toIntermediateField :=
    numberFieldCyclotomicZHatFiniteLayerInCompositum K E
  finiteDimensional := inferInstance
  isGalois := inferInstance

/-- Restriction from the cyclotomic compositum over `K` to the rational
cyclotomic `ZHat`-field. -/
noncomputable def numberFieldCyclotomicZHatCompositumRestriction :
    Gal((numberFieldCyclotomicZHatCompositum K)/K) →*
      Gal(rationalCyclotomicZHatField/ℚ) :=
  IntermediateField.restrictRestrictAlgEquivMapHom
    ℚ rationalCyclotomicZHatField K
      (numberFieldCyclotomicZHatCompositum K)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
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

/-- Projection of the infinite global Artin homomorphism to a finite
Galois intermediate field is exactly that field's finite global Artin
homomorphism, using a caller-supplied number-field witness. -/
@[simp]
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E) :
    letI : NumberField E := hE
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom
        (K := K) (L := E) a := by
  let : NumberField E := hE
  have hcomponent :=
    congrArg
      (InfiniteGalois.proj
        (k := K) (K := Ω) E)
      ((InfiniteGalois.continuousMulEquivToLimit
        K Ω).apply_symm_apply
          (infiniteGlobalArtinToLimit K Ω a))
  exact hcomponent

/-- Projection of the infinite global Artin homomorphism to a finite
Galois intermediate field, with its canonical module-finite number-field
structure. -/
@[simp]
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω) :
    letI : NumberField E :=
      NumberField.of_module_finite K E
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom
        (K := K) (L := E) a := by
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E (NumberField.of_module_finite K E)

/-- The actual continuous global Artin homomorphism from rational ideles
to the Galois group of the `ZHat`-extension of `ℚ`. -/
noncomputable def rationalCyclotomicZHatGlobalArtin :
    IdeleGroup ℚ →ₜ*
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
  infiniteGlobalArtinMonoidHom ℚ rationalCyclotomicZHatField

theorem
    continuousMulEquivToLimit_rationalCyclotomicZHatGlobalArtin_apply
    (a : IdeleGroup ℚ) :
    InfiniteGalois.continuousMulEquivToLimit
        ℚ rationalCyclotomicZHatField
        (rationalCyclotomicZHatGlobalArtin a) =
      infiniteGlobalArtinToLimit
        ℚ rationalCyclotomicZHatField a := by
  exact
    (InfiniteGalois.continuousMulEquivToLimit
      ℚ rationalCyclotomicZHatField).apply_symm_apply _

/-- Projection of the rational `ZHat` Artin homomorphism is the finite
global Artin homomorphism. -/
@[simp]
theorem restrictNormalHom_rationalCyclotomicZHatGlobalArtin
    (a : IdeleGroup ℚ)
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    letI : IsAbelianGalois ℚ E :=
      IsAbelianGalois.of_algHom E.toIntermediateField.val
    AlgEquiv.restrictNormalHom E
        (rationalCyclotomicZHatGlobalArtin a) =
      globalArtinMonoidHom
        (K := ℚ) (L := E) a :=
  restrictNormalHom_infiniteGlobalArtinMonoidHom
    ℚ rationalCyclotomicZHatField a E

end Reciprocity
end GlobalClassFieldTheory
end
end


