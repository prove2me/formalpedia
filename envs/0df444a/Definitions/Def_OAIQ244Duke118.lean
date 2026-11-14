-- Prove2me | Definitions.Def_OAIQ244Duke118
-- name    : OAIQ244Duke118
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T02:05:35.09719+00:00
-- url     : https://prove2.me/theorems/91bb51f3-9a6a-46ab-9c7e-c21ab65ec0a8
-- title:
--   Definitions bundle OAIQ244Duke118 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 3 definitions and 21 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldAlgebra`, `GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicPadicDecompositionCoordinate`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPadicCoordinate`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_CyclotomicAbstractFixedFieldArtin`, `GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleValue`, `GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleValueTopology`, `GlobalClassFieldTheory_Reciprocity_CyclotomicNormOneCorrection`, `GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceCyclotomicFrobeniusLift`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionNorm`, `GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke092` and `OAIQ244Duke093` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke096`.
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
import Definitions.Def_OAIQ244Duke092
import Definitions.Def_OAIQ244Duke093

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- Restriction from the full cyclotomic compositum to its rational
cyclotomic factor is continuous for the actual Krull topologies. -/
theorem numberFieldCyclotomicZHatCompositumRestriction_continuous :
    Continuous
      (numberFieldCyclotomicZHatCompositumRestriction K) := by
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def, map_one]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨M, hMfinite, hMU⟩ := hU
  let : FiniteDimensional ℚ M := hMfinite
  let E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField :=
    { toIntermediateField :=
        IntermediateField.normalClosure
          ℚ M rationalCyclotomicZHatField
      finiteDimensional :=
        normalClosure.is_finiteDimensional
          ℚ M rationalCyclotomicZHatField
      isGalois :=
        IsGalois.normalClosure
          ℚ M rationalCyclotomicZHatField }
  let : Normal ℚ E := E.isGalois.to_normal
  let P :=
    numberFieldCyclotomicZHatFiniteLayerInCompositum K E
  let : IsAbelianGalois K P :=
    numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois K E
  let : Normal K P := IsGalois.to_normal
  let : IsScalarTower K P
      (numberFieldCyclotomicZHatCompositum K) :=
    IntermediateField.isScalarTower_mid P
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨P, inferInstance, ?_⟩
  intro σ hσ
  have hfixP :
      AlgEquiv.restrictNormalHom
          P
          σ =
        1 := by
    have hker : σ ∈ (AlgEquiv.restrictNormalHom P).ker := by
      rw [IntermediateField.restrictNormalHom_ker]
      exact hσ
    exact hker
  have hkerE :
      AlgEquiv.restrictNormalHom E
          (numberFieldCyclotomicZHatCompositumRestriction K σ) = 1 := by
    rw [
      restrictNormalHom_numberFieldCyclotomicZHatCompositumRestriction,
      hfixP,
      map_one]
  have hfixE :
      (numberFieldCyclotomicZHatCompositumRestriction K σ) ∈
        (E : IntermediateField ℚ rationalCyclotomicZHatField).fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    exact hkerE
  apply hMU
  exact IntermediateField.fixingSubgroup_antitone
    (IntermediateField.le_normalClosure M) hfixE

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIsGalois
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

/-- Finite-place norm--restriction with the lower place supplied
explicitly.  This form keeps the equality proof in the completion
algebra and avoids dependent elimination through adic-completion
types. -/
theorem chosenFinitePlaceArtinMonoidHom_norm_restriction_of_below_eq
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v) :
    letI : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
      (finitePlaceAdicCompletionMap
        K K' v ⟨W, hW⟩).toAlgebra
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (chosenFinitePlaceArtinMonoidHom
          (K := K') (L := L') W) =
      (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v).comp
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion K')) := by
  subst v
  exact
    chosenFinitePlaceArtinMonoidHom_norm_restriction
      (K := K) (L := L) (K' := K') (L' := L') W

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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

/-- Norm-restriction naturality with the upper finite global Artin homomorphism
expressed through an explicit number-field witness. -/
theorem globalArtinMonoidHomOfNumberField_norm_restriction
    (K L K' L' : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    [Field K'] [NumberField K']
    [Field L'] [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (hL' : NumberField L') :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (globalArtinMonoidHomOfNumberField K' L' hL') =
      (globalArtinMonoidHom (K := K) (L := L)).comp
        (IdeleGroup.norm K K') := by
  let : NumberField L' := hL'
  exact globalArtinMonoidHom_norm_restriction

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleValue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalFiniteGaloisIdeleClassMulDistribMulAction _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instIsAbelianGaloisRatSubtypeSeparableClosureMemIntermediateFieldRationalCyclotomicZHatField
/-- On the canonical inclusion of a rational idele into `I_K`, the
unnormalized value is multiplication by the absolute degree `[K : ℚ]`.
This is the determinant-norm formula for scalar extension, expressed in
the rational cyclotomic `ZHat` coordinate. -/
theorem cyclotomicZHatNormComposite_baseIdeleInclusion
    (a : IdeleGroup ℚ) :
    cyclotomicZHatNormComposite K
        (Additive.ofMul
          (relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K)
            (RelativeIdeleGroup.inclusion ℚ K a))) =
      Module.finrank ℚ K •
        Multiplicative.toAdd
          (rationalCyclotomicZHatIdeleValue a) := by
  change
    Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue
          (IdeleGroup.norm ℚ K
            (relativeIdeleBaseChangeMulEquiv
              (K := ℚ) (L := K)
              (RelativeIdeleGroup.inclusion ℚ K a)))) =
      Module.finrank ℚ K •
        Multiplicative.toAdd
          (rationalCyclotomicZHatIdeleValue a)
  rw [IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv,
    RelativeIdeleGroup.norm_inclusion, map_pow,
    toAdd_pow]

/-- At every finite cyclotomic layer, the Artin image of norms from
`K` is exactly the image of restriction from the actual finite
compositum over `K`. -/
theorem finiteCyclotomicLayer_normArtin_range
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    let C :=
      numberFieldCyclotomicZHatFiniteCompositum K E
    ((globalArtinMonoidHom
        (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ K)).range =
      (IntermediateField.restrictRestrictAlgEquivMapHom
        ℚ E K C).range := by
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  let C :=
    numberFieldCyclotomicZHatFiniteCompositum K E
  let r :
      (C ≃ₐ[K] C) →* (E ≃ₐ[ℚ] E) :=
    IntermediateField.restrictRestrictAlgEquivMapHom
      ℚ E K C
  have hcomm :
      r.comp
          (globalArtinMonoidHom
            (K := K) (L := C)) =
        (globalArtinMonoidHom
          (K := ℚ) (L := E)).comp
            (IdeleGroup.norm ℚ K) :=
    by
      have hr :
          r =
            (AlgEquiv.restrictNormalHom E).comp
              (AlgEquiv.restrictScalarsHom ℚ) := by
        ext σ x
        exact rfl
      rw [hr]
      exact
        globalArtinMonoidHom_norm_restriction
          (K := ℚ) (L := E) (K' := K) (L' := C)
  apply le_antisymm
  · rintro σ ⟨a, rfl⟩
    refine
      ⟨globalArtinMonoidHom
          (K := K) (L := C) a,
        ?_⟩
    exact DFunLike.congr_fun hcomm a
  · rintro σ ⟨τ, rfl⟩
    obtain ⟨a, ha⟩ :=
      globalArtinMonoidHom_surjective
        (K := K) (L := C) τ
    refine ⟨a, ?_⟩
    have h := DFunLike.congr_fun hcomm a
    change
      r (globalArtinMonoidHom (K := K) (L := C) a) =
        globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) at h
    calc
      globalArtinMonoidHom
            (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) =
          r (globalArtinMonoidHom (K := K) (L := C) a) := h.symm
      _ = r τ := congrArg r ha

/-- Finite-layer form of the norm-image calculation: the Artin image
of the norms from `K` is precisely the subgroup fixing the actual
intersection `K ∩ E`. -/
theorem finiteCyclotomicLayer_normArtin_range_eq_fixingSubgroup
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    ((globalArtinMonoidHom
        (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ K)).range =
      (numberFieldCyclotomicZHatFiniteIntersection K E).fixingSubgroup := by
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  rw [finiteCyclotomicLayer_normArtin_range K E]
  exact
    numberFieldCyclotomicZHatFiniteCompositum_restriction_range
      K E

/-- The rational Artin symbols of norms from `K` are dense in the
subgroup fixing the actual intersection `K ∩ ℚ̃`.  At each finite
cyclotomic layer this is the exact restriction-image calculation above;
the Krull neighborhood basis then gives density in the inverse limit. -/
theorem
    rationalCyclotomicZHatGlobalArtin_norm_denseRange_in_intersection_fixingSubgroup :
    let hle :
        numberFieldCyclotomicZHatIntersection K ≤
          rationalCyclotomicZHatField :=
      inf_le_right
    let F :=
      (numberFieldCyclotomicZHatIntersection K).restrict hle
    DenseRange
      (fun a : IdeleGroup K =>
        (⟨rationalCyclotomicZHatGlobalArtin
              (IdeleGroup.norm ℚ K a),
            rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
              K a⟩ :
          F.fixingSubgroup)) := by
  let hle :
      numberFieldCyclotomicZHatIntersection K ≤
        rationalCyclotomicZHatField :=
    inf_le_right
  let F :=
    (numberFieldCyclotomicZHatIntersection K).restrict hle
  change
    DenseRange
      (fun a : IdeleGroup K =>
        (⟨rationalCyclotomicZHatGlobalArtin
              (IdeleGroup.norm ℚ K a),
            rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
              K a⟩ :
          F.fixingSubgroup))
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨σ, hσU⟩
  rw [isOpen_induced_iff] at hU
  obtain ⟨U₀, hU₀open, hUeq⟩ := hU
  have hσU₀ :
      σ.1 ∈ U₀ := by
    have hσpre :
        σ ∈
          Subtype.val ⁻¹' U₀ := by
      exact hUeq.symm ▸ hσU
    exact hσpre
  let V :
      Set
        (rationalCyclotomicZHatField ≃ₐ[ℚ]
          rationalCyclotomicZHatField) :=
    (Homeomorph.mulLeft
      σ.1) ⁻¹' U₀
  have hVopen : IsOpen V :=
    hU₀open.preimage
      (Homeomorph.mulLeft
        σ.1).continuous
  have hVone : ((1 : F.fixingSubgroup).1) ∈ V := by
    change
      σ.1 * (1 : F.fixingSubgroup).1 ∈ U₀
    rw [show
      σ.1 * (1 : F.fixingSubgroup).1 = σ.1 by
        exact congrArg Subtype.val (mul_one σ)]
    exact hσU₀
  have hVnhds :
      V ∈ 𝓝 ((1 : F.fixingSubgroup).1) :=
    hVopen.mem_nhds hVone
  have hkrull :=
    InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
      (k := ℚ) (K := rationalCyclotomicZHatField) V
  obtain ⟨E, hEV⟩ :=
    hkrull.mp hVnhds
  let hENumberField : NumberField E :=
    NumberField.of_module_finite ℚ E
  let : NumberField E := hENumberField
  let hEAbelian : IsAbelianGalois ℚ E :=
    IsAbelianGalois.of_algHom E.toIntermediateField.val
  let : IsAbelianGalois ℚ E := hEAbelian
  have hσfix :
      ∀ x : rationalCyclotomicZHatField,
        x ∈ F →
          σ.1 x = x := by
    exact
      (IntermediateField.mem_fixingSubgroup_iff F σ.1).1
        σ.property
  have hrestrictFix :
      AlgEquiv.restrictNormalHom E
          σ.1 ∈
        (numberFieldCyclotomicZHatFiniteIntersection K E).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    apply Subtype.ext
    have hxF :
        ((x : E) : rationalCyclotomicZHatField) ∈ F := by
      apply
        (IntermediateField.mem_restrict hle
          ((x : E) : rationalCyclotomicZHatField)).2
      exact
        numberFieldCyclotomicZHatFiniteIntersection_coe_mem_intersection
          K E x hx
    calc
      (((AlgEquiv.restrictNormalHom E
            σ.1) x : E) :
          rationalCyclotomicZHatField) =
          σ.1
            ((x : E) : rationalCyclotomicZHatField) :=
        AlgEquiv.restrictNormal_commutes
          σ.1 E x
      _ = ((x : E) : rationalCyclotomicZHatField) :=
        hσfix ((x : E) : rationalCyclotomicZHatField) hxF
  have hrestrictRange :
      AlgEquiv.restrictNormalHom E
          σ.1 ∈
        ((globalArtinMonoidHom
            (K := ℚ) (L := E)).comp
          (IdeleGroup.norm ℚ K)).range := by
    rw [
      finiteCyclotomicLayer_normArtin_range_eq_fixingSubgroup
        K E]
    exact hrestrictFix
  obtain ⟨a, ha⟩ := hrestrictRange
  let τ :
      F.fixingSubgroup :=
    ⟨rationalCyclotomicZHatGlobalArtin
        (IdeleGroup.norm ℚ K a),
      rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
        K a⟩
  let δ : F.fixingSubgroup := σ⁻¹ * τ
  have hδ :
      δ.1 = (σ.1)⁻¹ * τ.1 :=
    rfl
  have hτ :
      τ.1 =
        rationalCyclotomicZHatGlobalArtin
          (IdeleGroup.norm ℚ K a) :=
    rfl
  have ha' :
      globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) =
        AlgEquiv.restrictNormalHom E σ.1 := by
    simpa only [MonoidHom.comp_apply] using ha
  have hτProjection :
      AlgEquiv.restrictNormalHom E τ.1 =
        globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a) := by
    rw [hτ]
    change
      AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom
            ℚ rationalCyclotomicZHatField
            (IdeleGroup.norm ℚ K a)) =
        globalArtinMonoidHom
          (K := ℚ) (L := E) (IdeleGroup.norm ℚ K a)
    exact
      restrictNormalHom_rationalCyclotomicZHatGlobalArtin_of_structures
        (IdeleGroup.norm ℚ K a) E hENumberField hEAbelian
  have hrestrictEq :
      AlgEquiv.restrictNormalHom E τ.1 =
        AlgEquiv.restrictNormalHom E σ.1 :=
    hτProjection.trans ha'
  have hfixE :
      δ.1 ∈ E.fixingSubgroup := by
    apply
      (IntermediateField.mem_fixingSubgroup_iff
        E.toIntermediateField δ.1).2
    intro x hx
    have hrestrictedValue :=
      congrArg
        (fun f : E ≃ₐ[ℚ] E => f ⟨x, hx⟩)
        hrestrictEq
    have hτx : τ.1 x = σ.1 x := by
      calc
        τ.1 x =
            ((AlgEquiv.restrictNormalHom E τ.1)
              ⟨x, hx⟩ : E) :=
          (AlgEquiv.restrictNormal_commutes
            τ.1 E ⟨x, hx⟩).symm
        _ =
            ((AlgEquiv.restrictNormalHom E σ.1)
              ⟨x, hx⟩ : E) :=
          congrArg Subtype.val hrestrictedValue
        _ = σ.1 x :=
          AlgEquiv.restrictNormal_commutes
            σ.1 E ⟨x, hx⟩
    calc
      δ.1 x = ((σ.1)⁻¹ * τ.1) x :=
        congrArg (fun f => f x) hδ
      _ = (σ.1)⁻¹ (τ.1 x) := rfl
      _ = (σ.1)⁻¹ (σ.1 x) :=
        congrArg
          (fun y : rationalCyclotomicZHatField =>
            (σ.1)⁻¹ y)
          hτx
      _ = x := (σ.1).symm_apply_apply x
  have hmemV :
      δ.1 ∈ V :=
    hEV hfixE
  have hτU₀ :
      τ.1 ∈ U₀ := by
    change σ.1 * δ.1 ∈ U₀ at hmemV
    have hcancel : σ * δ = τ := by
      dsimp only [δ]
      exact mul_inv_cancel_left σ τ
    have hcancelVal := congrArg Subtype.val hcancel
    change σ.1 * δ.1 = τ.1 at hcancelVal
    rw [hcancelVal] at hmemV
    exact hmemV
  have hτU : τ ∈ U := by
    have hτpre : τ ∈ Subtype.val ⁻¹' U₀ :=
      hτU₀
    exact hUeq ▸ hτpre
  exact ⟨τ, hτU, ⟨a, rfl⟩⟩

/-- The unnormalized norm value is dense in its exact ambient subgroup
`f_K ℤ̂`.  This is the additive-coordinate form of the Krull-density
statement for norm Artin symbols. -/
theorem cyclotomicZHatNormCompositeInMulNatRange_denseRange :
    DenseRange
      (cyclotomicZHatNormCompositeInMulNatRange K) := by
  let hle :
      numberFieldCyclotomicZHatIntersection K ≤
        rationalCyclotomicZHatField :=
    inf_le_right
  let F :=
    (numberFieldCyclotomicZHatIntersection K).restrict hle
  let H := F.fixingSubgroup
  let f := cyclotomicZHatIntersectionDegree K
  let R :=
    (zHatMulNat f).toAddMonoidHom.range
  let e :=
    rationalCyclotomicZHatFieldGalEquivZHat
  have himage :
      (H.map e.toMonoidHom).toAddSubgroup' = R := by
    simpa only [H, F, f, R, e] using
      (rationalCyclotomicZHatFieldGal_fixingSubgroup_image_eq_mulNat_range
        K)
  let g : H → R :=
    fun σ =>
      ⟨Multiplicative.toAdd (e σ.1), by
        have hσ :
            Multiplicative.toAdd (e σ.1) ∈
              (H.map e.toMonoidHom).toAddSubgroup' := by
          rw [Subgroup.mem_toAddSubgroup']
          exact ⟨σ.1, σ.2, rfl⟩
        rw [himage] at hσ
        exact hσ⟩
  have hgContinuous : Continuous g := by
    apply Continuous.subtype_mk
    change
      Continuous
        (fun σ : H =>
          e σ.1)
    exact e.continuous.comp continuous_subtype_val
  have hgSurjective : Function.Surjective g := by
    intro z
    have hz :
        z.1 ∈
          (H.map e.toMonoidHom).toAddSubgroup' := by
      rw [himage]
      exact z.2
    rw [Subgroup.mem_toAddSubgroup'] at hz
    obtain ⟨σ, hσ, hσz⟩ := hz
    refine ⟨⟨σ, hσ⟩, ?_⟩
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd hσz
  have hnormDense :
      DenseRange
        (fun a : IdeleGroup K =>
          (⟨rationalCyclotomicZHatGlobalArtin
                (IdeleGroup.norm ℚ K a),
              rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
                K a⟩ :
            H)) := by
    simpa only [H, F] using
      (rationalCyclotomicZHatGlobalArtin_norm_denseRange_in_intersection_fixingSubgroup
        K)
  have hcompDense :
      DenseRange
        (fun a : IdeleGroup K =>
          g
            (⟨rationalCyclotomicZHatGlobalArtin
                  (IdeleGroup.norm ℚ K a),
                rationalCyclotomicZHatGlobalArtin_norm_mem_intersection_fixingSubgroup
                  K a⟩ :
              H)) :=
    hgSurjective.denseRange.comp
      hnormDense hgContinuous
  apply hcompDense.mono
  rintro z ⟨a, rfl⟩
  refine ⟨Additive.ofMul a, ?_⟩
  apply Subtype.ext
  rfl

/-- The normalized cyclotomic value has dense image in `ℤ̂`. -/
theorem normalizedCyclotomicZHatIdeleValue_denseRange :
    DenseRange (normalizedCyclotomicZHatIdeleValue K) := by
  change
    DenseRange
      (fun a =>
        zHatDivide
          (cyclotomicZHatIntersectionDegree K)
          (cyclotomicZHatIntersectionDegree_pos K)
          (cyclotomicZHatNormCompositeInMulNatRange K a))
  exact
    (zHatMulNatRangeEquiv
        (cyclotomicZHatIntersectionDegree K)
        (cyclotomicZHatIntersectionDegree_pos K)).symm.surjective.denseRange.comp
      (cyclotomicZHatNormCompositeInMulNatRange_denseRange K)
      (zHatDivide
        (cyclotomicZHatIntersectionDegree K)
        (cyclotomicZHatIntersectionDegree_pos K)).continuous

/-- On scalar extension of a rational idele, the normalized value is
multiplication by the relative factor `[K : ℚ] / f_K`. -/
theorem normalizedCyclotomicZHatIdeleValue_baseIdeleInclusion
    (a : IdeleGroup ℚ) :
    normalizedCyclotomicZHatIdeleValue K
        (Additive.ofMul
          (relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K)
            (RelativeIdeleGroup.inclusion ℚ K a))) =
      (Module.finrank ℚ K /
          cyclotomicZHatIntersectionDegree K) •
        Multiplicative.toAdd
          (rationalCyclotomicZHatIdeleValue a) := by
  apply
    zHatMulNat_injective
      (cyclotomicZHatIntersectionDegree_pos K)
  rw [zHatMulNat_apply, zHatMulNat_apply,
    cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleValue,
    cyclotomicZHatNormComposite_baseIdeleInclusion,
    ← mul_nsmul,
    Nat.div_mul_cancel
      (cyclotomicZHatIntersectionDegree_dvd_finrank K)]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicNormOneCorrection
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalFiniteGaloisIdeleClassMulDistribMulAction _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeInMulNatRangeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuousMul_apply _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalAbsoluteGaloisIdeleClass_smul_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractFixedFieldIdeleClassEquivFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatGlobalArtin_rationalIdeleArchimedeanPart _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueContinuousAdd_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueReduction_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValue_rationalIdeleArchimedeanPart _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleArchimedeanPart_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleArchimedeanPart_infiniteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleFinitePart_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleFinitePart_infiniteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norm-one correction for the normalized cyclotomic idele value

The positive archimedean section over `ℚ` gives the source term in the
cyclotomic norm-one reduction.  After taking a positive
`[K : ℚ]`-th root of the absolute norm of an idele, scalar extension of
that section cancels the absolute norm.  Its rational cyclotomic Artin
value is trivial, so the normalized value is unchanged.
-/

open scoped NNReal NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable (K : Type) [Field K] [NumberField K]

/-- Every idele has the same normalized cyclotomic value as an actual
norm-one idele. -/
theorem
    exists_normOneIdele_same_normalizedCyclotomicZHatIdeleValue
    (a : IdeleGroup K) :
    ∃ b : IdeleGroup.normOneSubgroup (K := K),
      normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul (b : IdeleGroup K)) =
        normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a) := by
  let d := Module.finrank ℚ K
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  let r : ℝ≥0ˣ := IdeleGroup.absoluteNorm a
  have hrpos : 0 < (r : ℝ≥0) :=
    pos_iff_ne_zero.mpr r.ne_zero
  let s0 : ℝ≥0 := (r : ℝ≥0) ^ ((d : ℝ)⁻¹)
  have hs0pos : 0 < s0 := by
    exact NNReal.rpow_pos hrpos
  let s : ℝ≥0ˣ := Units.mk0 s0 hs0pos.ne'
  have hs_pow : s ^ d = r := by
    apply Units.ext
    change s0 ^ d = (r : ℝ≥0)
    exact NNReal.rpow_inv_natCast_pow (r : ℝ≥0) hd
  let c : IdeleGroup K :=
    relativeIdeleBaseChangeMulEquiv
      (K := ℚ) (L := K)
      (RelativeIdeleGroup.inclusion ℚ K
        (rationalPositiveArchimedeanIdele s))
  have hc_absoluteNorm :
      IdeleGroup.absoluteNorm c = r⁻¹ := by
    change
      IdeleGroup.absoluteNorm
          (relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K)
            (RelativeIdeleGroup.inclusion ℚ K
              (rationalPositiveArchimedeanIdele s))) =
        r⁻¹
    rw [
      IdeleGroup.absoluteNorm_relativeIdeleBaseChange_inclusion_of_finite_eq_one
        (L := K) (rationalPositiveArchimedeanIdele s) rfl,
      rationalPositiveArchimedeanIdele_absoluteNorm,
      inv_pow, hs_pow]
  have hs_value :
      rationalCyclotomicZHatIdeleValue
          (rationalPositiveArchimedeanIdele s) =
        1 := by
    rw [rationalCyclotomicZHatIdeleValue_apply,
      rationalCyclotomicZHatGlobalArtin_rationalPositiveArchimedeanIdele,
      map_one]
  have hc_value :
      normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul c) =
        0 := by
    change
      normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul
            (relativeIdeleBaseChangeMulEquiv
              (K := ℚ) (L := K)
              (RelativeIdeleGroup.inclusion ℚ K
                (rationalPositiveArchimedeanIdele s)))) =
        0
    rw [normalizedCyclotomicZHatIdeleValue_baseIdeleInclusion,
      hs_value]
    simp
  refine ⟨⟨a * c, ?_⟩, ?_⟩
  · change IdeleGroup.absoluteNorm (a * c) = 1
    rw [map_mul, hc_absoluteNorm]
    simp [r]
  · change
      normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a + Additive.ofMul c) =
        normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a)
    rw [map_add, hc_value, add_zero]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleValueTopology
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractFixedFieldIdeleClassEquivFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatGlobalArtin_rationalIdeleArchimedeanPart _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValue_rationalIdeleArchimedeanPart _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleArchimedeanPart_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleArchimedeanPart_infiniteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleFinitePart_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleFinitePart_infiniteComponent _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
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

variable (K : Type) [Field K] [NumberField K]

/-- The actual norm-one ideles already have dense normalized cyclotomic
value.  The source reduction uses the positive archimedean correction,
whose cyclotomic value is trivial. -/
theorem normalizedCyclotomicZHatIdeleValue_normOne_denseRange :
    DenseRange
      (fun b : IdeleGroup.normOneSubgroup (K := K) =>
        normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul (b : IdeleGroup K))) := by
  apply (normalizedCyclotomicZHatIdeleValue_denseRange K).mono
  rintro z ⟨a, rfl⟩
  obtain ⟨b, hb⟩ :=
    exists_normOneIdele_same_normalizedCyclotomicZHatIdeleValue
      K (Additive.toMul a)
  refine ⟨b, ?_⟩
  simpa using hb

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicAbstractFixedFieldArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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
# Cyclotomic Artin coordinates over abstract fixed fields

The cyclotomic degree datum on the rational absolute Galois group has
an actual maximal-unramified field over every finite abstract fixed
field.  This file identifies its genuine Galois group with
`Multiplicative ZHat`, using the normalized degree map, and supplies
the abelian Galois structure needed by the actual infinite global
Artin homomorphism.

These constructions are the source side of the comparison between
abstract finite reciprocity and the chosen local-factor product.  No
reciprocity comparison is assumed in their definitions.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

attribute [local instance] GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtin_separableClosureAlgebra
noncomputable local instance
    cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldAlgebra :
    Algebra ℚ rationalCyclotomicZHatField :=
  DivisionRing.toRatAlgebra

/-- On a quotient representative, cyclotomic restriction of the
actual relative automorphism is ordinary restriction of the same
ambient absolute-Galois automorphism. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldNormal :
    Normal ℚ rationalCyclotomicZHatField :=
  rationalCyclotomicZHatField_isNormal

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceCyclotomicFrobeniusLift
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.cyclicPrimeDegreeIntermediate_isGalois
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicZHatNormCompositeInMulNatRangeContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuousMul_apply _root_.GlobalClassFieldTheory.Reciprocity.normalizedCyclotomicZHatIdeleValueContinuous_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueContinuousAdd_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatIdeleValueReduction_apply _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

local instance localInst_r34ff46_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerNumberField_r34ff46_1
    (p : Nat.Primes) (k : ℕ) :
    NumberField (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerFiniteDimensional_r34ff46_1
    (p : Nat.Primes) (k : ℕ) :
    FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerIsAbelianGalois_r34ff46_1
    (p : Nat.Primes) (k : ℕ) :
    IsAbelianGalois ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevelIsAbelianGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
noncomputable local instance
    rationalCyclotomicFrobeniusLiftLevelFiniteDimensional_r34ff46_1
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional m
noncomputable local instance
    rationalCyclotomicFrobeniusLiftLevelIsAbelianGalois_r34ff46_1
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicLevelIsAbelianGalois m
variable
    {K L Ω : Type}
    [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower K L Ω] [Normal K L]

/-- The infinite global Artin symbol of a finite one-place idèle
stabilizes every chosen extension of that finite place to an abelian
Galois overfield.

The proof is genuinely inverse-limit in nature.  For each element of
the overfield, we pass to the finite Galois closure it generates.  The
restriction of the infinite Artin symbol is then the finite chosen local
Artin symbol, whose image is the finite decomposition group.  Independence
of the exact extension in the abelian finite layer returns the valuation
stabilizer statement upstairs. -/
theorem
    infiniteGlobalArtinMonoidHom_finitePlaceIdele_mem_absoluteValueDecompositionGroup
    {F A : Type}
    [Field F] [NumberField F]
    [Field A] [Algebra F A] [IsAbelianGalois F A]
    (v : HeightOneSpectrum (𝓞 F))
    (wA : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) A)
    (x : (v.adicCompletion F)ˣ) :
    infiniteGlobalArtinMonoidHom F A
        (IdeleGroup.finitePlaceIdele v x) ∈
      absoluteValueDecompositionGroup F wA.1 := by
  rw [mem_absoluteValueDecompositionGroup_iff]
  intro y
  let M : IntermediateField F A :=
    IntermediateField.adjoin F {y}
  let : FiniteDimensional F M :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral y)
  let E :
      FiniteGaloisIntermediateField F A :=
    { toIntermediateField :=
        IntermediateField.normalClosure F M A
      finiteDimensional :=
        normalClosure.is_finiteDimensional F M A
      isGalois :=
        IsGalois.normalClosure F M A }
  let : NumberField E :=
    NumberField.of_module_finite F E
  let : IsAbelianGalois F E :=
    IsAbelianGalois.of_algHom
      (E : IntermediateField F A).val
  let vF :=
    NumberField.HeightOneSpectrum.adicAbv F v
  let wE : AbsoluteValueExtension vF E :=
    restrictAbsoluteValueExtensionToIntermediate
      vF wA E
  have hyM : y ∈ M :=
    IntermediateField.subset_adjoin
      (F := F) (S := {y}) (by rfl)
  have hyE : y ∈ E.toIntermediateField :=
    IntermediateField.le_normalClosure M hyM
  have hrestriction :
      AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom F A
            (IdeleGroup.finitePlaceIdele v x)) =
        chosenFinitePlaceArtinMonoidHom
          (K := F) (L := E) v x := by
    rw [
      restrictNormalHom_infiniteGlobalArtinMonoidHom,
      globalArtinMonoidHom_finitePlaceIdele]
  have hchosen :
      AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom F A
            (IdeleGroup.finitePlaceIdele v x)) ∈
        finitePlaceDecompositionGroup
          (K := F) (L := E) v := by
    rw [←
      chosenFinitePlaceArtinMonoidHom_range
        (K := F) (L := E) v]
    exact ⟨x, hrestriction.symm⟩
  have hrestricted :
      AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom F A
            (IdeleGroup.finitePlaceIdele v x)) ∈
        absoluteValueDecompositionGroup F wE.1 := by
    rw [←
      absoluteValueDecompositionGroup_eq_of_exactExtensions_of_isMulCommutative
        vF
        (RayClass.adicAbv_isNontrivial v)
        (chosenFinitePlaceExtension (L := E) v)
        wE]
    exact hchosen
  have hvalue :=
    (mem_absoluteValueDecompositionGroup_iff F wE.1 _).1
      hrestricted ⟨y, hyE⟩
  have hcommutes :
      (((AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom F A
            (IdeleGroup.finitePlaceIdele v x))) ⟨y, hyE⟩ : E) : A) =
        infiniteGlobalArtinMonoidHom F A
          (IdeleGroup.finitePlaceIdele v x) y :=
    AlgEquiv.restrictNormal_commutes
      (infiniteGlobalArtinMonoidHom F A
        (IdeleGroup.finitePlaceIdele v x)) E ⟨y, hyE⟩
  simpa only [wE, restrictAbsoluteValueExtensionToIntermediate_apply,
    hcommutes] using hvalue

/-- The genuine `p`-adic cyclotomic coordinate on the actual Galois
group of the rational cyclotomic `ZHat`-extension. -/
noncomputable def rationalCyclotomicPadicCoordinate
    (p : Nat.Primes) :
    (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) →ₜ*
      Multiplicative ℤ_[p.1] := by
  let pCoordinate :
      Multiplicative ZHat →ₜ*
        Multiplicative ℤ_[p.1] :=
    ⟨AddMonoidHom.toMultiplicative
        (zHatToPadicInt p).toAddMonoidHom,
      continuous_ofAdd.comp
        ((continuous_zHatToPadicInt p).comp
          continuous_toAdd)⟩
  exact
    pCoordinate.comp
      (ContinuousMonoidHom.toContinuousMonoidHom
        rationalCyclotomicZHatFieldGalEquivZHat)

/-- The rational cyclotomic `p`-adic coordinate is obtained by applying the
canonical `ZHat`-to-`ℤ_p` coordinate to the cyclotomic character. -/
@[simp]
theorem rationalCyclotomicPadicCoordinate_apply
    (p : Nat.Primes)
    (σ :
      rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :
    Multiplicative.toAdd
        (rationalCyclotomicPadicCoordinate p σ) =
      zHatToPadicInt p
        (Multiplicative.toAdd
          (rationalCyclotomicZHatFieldGalEquivZHat σ)) :=
  rfl

/-- The `p`-adic cyclotomic coordinate on the actual decomposition
group of an arbitrary absolute value of the number-field cyclotomic
`ZHat`-compositum.

This is the restriction of the genuine compositum Galois group to the
rational cyclotomic factor, followed by its actual `ℤ_p` coordinate.
The source is the valuation stabilizer itself, rather than an abstract
copy of a local Galois group. -/
noncomputable def
    numberFieldCyclotomicPadicDecompositionCoordinate
    (F : Type) [Field F] [NumberField F]
    (wC : AbsoluteValue
      (numberFieldCyclotomicZHatCompositum F) ℝ)
    (p : Nat.Primes) :
    absoluteValueDecompositionGroup F wC →ₜ*
      Multiplicative ℤ_[p.1] where
  toMonoidHom :=
    (rationalCyclotomicPadicCoordinate p).toMonoidHom.comp
      ((numberFieldCyclotomicZHatCompositumRestriction F).comp
        (absoluteValueDecompositionGroup F wC).subtype)
  continuous_toFun :=
    (rationalCyclotomicPadicCoordinate p).continuous_toFun.comp
      ((numberFieldCyclotomicZHatCompositumRestriction_continuous
        (K := F)).comp continuous_subtype_val)

/-- The decomposition-group coordinate is the rational cyclotomic coordinate
of the restricted global automorphism. -/
@[simp]
theorem numberFieldCyclotomicPadicDecompositionCoordinate_apply
    (F : Type) [Field F] [NumberField F]
    (wC : AbsoluteValue
      (numberFieldCyclotomicZHatCompositum F) ℝ)
    (p : Nat.Primes)
    (σ : absoluteValueDecompositionGroup F wC) :
    numberFieldCyclotomicPadicDecompositionCoordinate
        F wC p σ =
      rationalCyclotomicPadicCoordinate p
        (numberFieldCyclotomicZHatCompositumRestriction F σ.1) :=
  rfl

/-- On an actual global Artin symbol lying in a decomposition group,
the decomposition coordinate is the `p`-adic coordinate of the
rational cyclotomic idèle value of the ordinary field norm. -/
theorem
    numberFieldCyclotomicPadicDecompositionCoordinate_infiniteGlobalArtin
    (F : Type) [Field F] [NumberField F]
    (wC : AbsoluteValue
      (numberFieldCyclotomicZHatCompositum F) ℝ)
    (p : Nat.Primes) (a : IdeleGroup F)
    (ha :
      infiniteGlobalArtinMonoidHom F
          (numberFieldCyclotomicZHatCompositum F) a ∈
        absoluteValueDecompositionGroup F wC) :
    numberFieldCyclotomicPadicDecompositionCoordinate
        F wC p
        ⟨infiniteGlobalArtinMonoidHom F
          (numberFieldCyclotomicZHatCompositum F) a, ha⟩ =
      Multiplicative.ofAdd
        (zHatToPadicInt p
          (Multiplicative.toAdd
            (rationalCyclotomicZHatIdeleValue
              (IdeleGroup.norm ℚ F a)))) := by
  apply Multiplicative.ext
  rw [
    numberFieldCyclotomicPadicDecompositionCoordinate_apply,
    numberFieldCyclotomicZHatCompositumRestriction_infiniteGlobalArtinMonoidHom,
    rationalCyclotomicPadicCoordinate_apply,
    rationalCyclotomicZHatIdeleValue_apply]
  rfl

/-- The image of a cyclotomic `p`-adic decomposition coordinate is
closed.  This is the compact image of the actual closed decomposition
group in the Krull topology. -/
theorem
    numberFieldCyclotomicPadicDecompositionCoordinate_range_isClosed
    (F : Type) [Field F] [NumberField F]
    (wC : AbsoluteValue
      (numberFieldCyclotomicZHatCompositum F) ℝ)
    (p : Nat.Primes) :
    IsClosed
      ((numberFieldCyclotomicPadicDecompositionCoordinate
        F wC p).range :
        Set (Multiplicative ℤ_[p.1])) := by
  let :
      CompactSpace
        (absoluteValueDecompositionGroup F wC) :=
    isCompact_iff_compactSpace.mp
      (absoluteValueDecompositionGroup_isClosed F wC).isCompact
  rw [MonoidHom.coe_range]
  exact
    (isCompact_range
      (numberFieldCyclotomicPadicDecompositionCoordinate
        F wC p).continuous_toFun).isClosed

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

/-- Under the fixed-field realization, the representation norm is the
existing relative idele-class norm, viewed in the upper class group by
the existing class inclusion. -/
theorem rationalAbstractExtensionIdeleClassEquiv_norm
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (x : (extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal).V) :
    let comparison :=
      rationalExtensionNormComparison K L hLK hnormal x
    comparison.1 = comparison.2 := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ := hnormal
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K inferInstance
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK inferInstance inferInstance
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let _ : NumberField E := NumberField.of_module_finite ℚ E
  let _ : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let _ : MulDistribMulAction (E ≃ₐ[F] E)
      (RelativeIdeleGroup.ClassGroup F E) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  let _ : Fintype Q := Fintype.ofFinite Q
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let e :=
    rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
  let eQ :=
    abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let c : RelativeIdeleGroup.ClassGroup F E :=
    Additive.toMul (e x)
  change e (M.norm.hom x) =
    includedRelativeIdeleClassNormAdditiveValue F E (e x)
  apply Additive.toMul.injective
  simp only [Rep.norm, Representation.norm]
  change
    Additive.toMul (e ((∑ q : Q, M.ρ q) x)) =
      RelativeIdeleGroup.classInclusion F E
        (RelativeIdeleGroup.Cohomology.ideleClassNorm F E c)
  rw [LinearMap.sum_apply, map_sum, toMul_sum]
  have hActionProd :
      (∏ q : Q, Additive.toMul (e (M.ρ q x))) =
        ∏ q : Q, eQ q • c := by
    apply Finset.prod_congr rfl
    intro q _
    rw [rationalAbstractExtensionIdeleClassEquiv_action
      K L hLK hnormal q x]
    exact repOfMulDistribMulAction_rho_toMul (eQ q) (e x)
  have hReindex :
      (∏ q : Q, eQ q • c) =
        ∏ τ : E ≃ₐ[F] E, τ • c := by
    exact fintype_prod_comp_equiv eQ.toEquiv
      (fun τ : E ≃ₐ[F] E => τ • c)
  have hNormProd :
      (∏ τ : E ≃ₐ[F] E, τ • c) =
        RelativeIdeleGroup.classInclusion F E
          (RelativeIdeleGroup.Cohomology.ideleClassNorm F E c) :=
    (RelativeIdeleGroup.classInclusion_ideleClassNorm_eq_prod_conjugates
      c).symm
  exact Eq.trans hActionProd (Eq.trans hReindex hNormProd)

theorem rationalRelativeNormClassNorm_eq
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
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    rationalRelativeNormClassNormSource
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a =
      rationalRelativeNormClassNormTarget
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ := hnormal
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let _ : NumberField E := NumberField.of_module_finite ℚ E
  let _ : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  let _ : Fintype Q := Fintype.ofFinite Q
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let eK :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K
  let e :=
    rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
  let x := eAmbient.symm a
  let n :=
    relativeNorm rationalIdeleClassRepresentation K L hLK a
  let q :=
    RelativeIdeleGroup.Cohomology.ideleClassNorm F E
      (Additive.toMul (e x))
  let cK : RelativeIdeleGroup.ClassGroup ℚ F :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := F)).symm
      (Additive.toMul (eK.symm n))
  have hcK :
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) cK =
        Additive.toMul (eK.symm n) := by
    exact
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := F)).apply_symm_apply
        (Additive.toMul (eK.symm n))
  have hn :
      eK
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := F) cK)) =
        n := by
    rw [hcK]
    change eK (eK.symm n) = n
    exact eK.apply_symm_apply n
  have hMnorm :
      M.norm.hom x =
        eAmbient.symm
          (fixedFieldInclusion rationalIdeleClassRepresentation
            K L hLK n) := by
    exact rationalRelativeNorm_representation_norm
      (hfinite := hfinite) K L hLK hnormal a
  have hNorm :=
    rationalAbstractExtensionIdeleClassEquiv_norm
      K L hLK hnormal x
  have hInclusion :=
    rationalAbstractExtensionIdeleClassEquiv_fixedFieldInclusion
      K L hLK hnormal cK
  change
    e (M.norm.hom x) =
      Additive.ofMul
        (RelativeIdeleGroup.classInclusion F E q) at hNorm
  change
    e
        (eAmbient.symm
          (fixedFieldInclusion rationalIdeleClassRepresentation
            K L hLK
            (eK
              (Additive.ofMul
                (_root_.relativeIdeleClassBaseChangeMulEquiv
                  (K := ℚ) (L := F) cK))))) =
      Additive.ofMul
        (RelativeIdeleGroup.classInclusion F E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) cK)) at hInclusion
  have hNorm' :=
    (congrArg (fun t => e t) hMnorm).symm.trans hNorm
  have hInclusionLeft := congrArg
    (fun b =>
      e
        (eAmbient.symm
          (fixedFieldInclusion rationalIdeleClassRepresentation
            K L hLK b)))
    hn
  have hInclusionRight := congrArg
    (fun d : IdeleClassGroup F =>
      Additive.ofMul
        (RelativeIdeleGroup.classInclusion F E d))
    hcK
  have hInclusion' :=
    hInclusionLeft.symm.trans (hInclusion.trans hInclusionRight)
  have hq :
      q = Additive.toMul (eK.symm n) := by
    exact eq_of_common_ofMul_image
      (fun d : IdeleClassGroup F =>
        RelativeIdeleGroup.classInclusion F E d)
      (RelativeIdeleGroup.classInclusion_injective F E)
      hNorm' hInclusion'
  change q = Additive.toMul (eK.symm n)
  exact hq

/-- The relative norm in the rational absolute idele-class
representation is the existing relative idele-class norm on the two
actual fixed fields. -/
theorem
    rationalAbstractFixedFieldIdeleClassEquivFixed_relativeNorm
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
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    rationalRelativeNormSource
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a =
      rationalRelativeNormTarget
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a := by
  have h := congrArg Additive.ofMul
    (rationalRelativeNormClassNorm_eq
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK hnormal a).symm
  change
    rationalRelativeNormSource
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a =
      rationalRelativeNormTarget
        (hKfinite := hKfinite) (hfinite := hfinite)
        K L hLK hnormal a at h
  exact h

end Reciprocity
end GlobalClassFieldTheory
end
end


