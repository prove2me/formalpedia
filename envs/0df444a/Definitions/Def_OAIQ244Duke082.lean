-- Prove2me | Definitions.Def_OAIQ244Duke082
-- name    : OAIQ244Duke082
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T23:22:27.800696+00:00
-- url     : https://prove2.me/theorems/80d2d105-f2eb-4d88-9b8f-47ee3fc57509
-- title:
--   Definitions bundle OAIQ244Duke082 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 44 declarations of OpenAI's Lean: 8 definitions, 1 instance and 35 theorems. The definitions and types are `GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient`, `GlobalClassFieldTheory.GlobalClassFields.cyclotomicFullSUnitKummerExtension`, `GlobalClassFieldTheory.GlobalClassFields.cyclotomicKummerNormDescent_kummerAlgebraOverBase`, `GlobalClassFieldTheory.GlobalClassFields.cyclotomicKummerNormDescent_kummerModuleOverBase`, `GlobalClassFieldTheory.GlobalClassFields.cyclotomicKummerNormDescent_kummerSMulOverBase`, `GlobalClassFieldTheory.GlobalClassFields.cyclotomicKummerNormSupport`, `GlobalClassFieldTheory.GlobalClassFields.cyclotomicKummerNormSupportAbove`, `GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_GlobalClassFields_ConductorSupport`, `GlobalClassFieldTheory_GlobalClassFields_CyclotomicKummerNormDescent`, `GlobalClassFieldTheory_GlobalClassFields_HilbertClassFieldMaximality`, `GlobalClassFieldTheory_GlobalClassFields_HilbertNormCharacterization`, `GlobalClassFieldTheory_GlobalClassFields_KummerNormDescent`, `GlobalClassFieldTheory_GlobalClassFields_NormConductor`, `GlobalClassFieldTheory_GlobalClassFields_NormRayClassMaximality`, `GlobalClassFieldTheory_GlobalClassFields_NormTowerConductor`, `GlobalClassFieldTheory_GlobalClassFields_SUnitKummerNormCore`, `GlobalClassFieldTheory_GlobalClassFields_SmallHilbertNormCharacterization`, `GlobalClassFieldTheory_Reciprocity_CyclotomicTorsionFixedField`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitAbstractFixedField`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_SeparableClosurePadicLift`, `GlobalClassFieldTheory_Reciprocity_OnePlaceNormKernel`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke073`, `OAIQ244Duke074`, `OAIQ244Duke075`, `OAIQ244Duke076`, `OAIQ244Duke077`, `OAIQ244Duke078` and `OAIQ244Duke079` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke086`, `OAIQ244Duke087` and `OAIQ244Duke116`.
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
import Mathlib.Algebra.Group.Subgroup.Pointwise
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
import Mathlib.NumberTheory.RamificationInertia.Unramified
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
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Pointwise
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
import Definitions.Def_OAIQ244Duke073
import Definitions.Def_OAIQ244Duke074
import Definitions.Def_OAIQ244Duke075
import Definitions.Def_OAIQ244Duke076
import Definitions.Def_OAIQ244Duke077
import Definitions.Def_OAIQ244Duke078
import Definitions.Def_OAIQ244Duke079

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_OnePlaceNormKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalFiniteGaloisIdeleClassMulDistribMulAction _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The one-place norm kernel

At the source level, the key calculation is that an idele supported at one
finite place is a global relative-idele norm exactly when its local component
is a norm from the corresponding local tensor algebra.  The determinant-norm
comparison then identifies this image with the norm group of any chosen
completion above the place.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- A chosen local norm at one finite place gives an actual global
idele-class norm.  The witness is the relative idele supported at that
place, transported to an ordinary idele of the extension field. -/
theorem finitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_chosenLocalNorm
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (hx :
      x ∈ chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v) :
    IdeleGroup.finitePlaceIdeleClass v x ∈
      (_root_.ideleClassNorm K L).range := by
  have hnorm :
      IdeleGroup.finitePlaceIdele v x ∈
        ideleNormSubgroup (K := K) (L := L) :=
    (finitePlaceIdele_mem_ideleNormSubgroup_iff_chosenLocalNorm
      (K := K) (L := L) v x).2 hx
  obtain ⟨z, hz⟩ := hnorm
  refine
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (_root_.relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z), ?_⟩
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.norm K L
          (_root_.relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L) z)) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.finitePlaceIdele v x)
  rw [IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv, hz]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ConductorSupport
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Support of the narrow finite conductor

There are two source statements in the ramification criterion:

* a prime belongs to the support of the narrow finite conductor exactly
  when its one-place finite local conductor exponent is nonzero;
* a finite abelian local extension is ramified exactly when its concrete
  local conductor exponent is nonzero.

The local conductor criterion itself is public in
`LocalClassFieldTheory.Finite.UnramifiedConductor`.  The global
reciprocity identity `N(C_L) ∩ K_vˣ = N(L_vˣ)` identifies the two
exponents for a global extension, yielding the global conductor-support
corollary.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

/-- At an unramified chosen completion, the zeroth local higher-unit
class subgroup consists of global idele-class norms. -/
theorem localHigherUnitClassSubgroup_zero_le_ideleClassNorm_range_of_chosenUnramified
    {L : Type}
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    RayClass.localHigherUnitClassSubgroup v 0 ≤
      (_root_.ideleClassNorm K L).range := by
  rintro _ ⟨x, hx, rfl⟩
  apply
    Reciprocity.finitePlaceIdeleClass_mem_ideleClassNorm_range_of_mem_chosenLocalNorm
      (K := K) (L := L) v x
  apply
    _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v hunram
  rw [← RayClass.localHigherUnitGroup_zero]
  exact hx

/-- Algebraic unramifiedness at a finite prime forces the zeroth local
higher-unit class subgroup into the global norm subgroup. -/
theorem localHigherUnitClassSubgroup_zero_le_ideleClassNorm_range_of_isUnramifiedAt
    {L : Type}
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v)).asIdeal) :
    RayClass.localHigherUnitClassSubgroup v 0 ≤
      (_root_.ideleClassNorm K L).range :=
  localHigherUnitClassSubgroup_zero_le_ideleClassNorm_range_of_chosenUnramified
    (K := K) (L := L) v
    (_root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := L) v hunram)

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_KummerNormDescent
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Descent of power-local-unit idèle subgroups

For a finite extension `L / K`, the norm of a local `n`-th power is again
an `n`-th power.  At a finite place outside a prescribed support, the norm
of an integral unit is an integral unit.  Combining these statements over
all places above a place of `K` shows that the ordinary idèle norm carries
the power-local-unit subgroup for the full inverse-image support on `L`
into the corresponding subgroup on `K`.

Passing to principal-idèle quotients gives the idèle-class norm descent
needed when a Kummer extension is first constructed after a finite base
extension and then viewed over the original number field.
-/

open scoped BigOperators NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open AlgebraicNumberTheory.Valuations
open GlobalClassFieldTheory.ClassFieldAxiom

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- If `S'` is exactly the set of finite places of `L` above `S`, the
ordinary idèle norm carries the power-local-unit subgroup over `L` into
the corresponding subgroup over `K`. -/
theorem ideleNorm_mem_powerLocalUnitSubgroup_of_supports_above
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (S' : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ W : HeightOneSpectrum (𝓞 L),
      W ∈ S' ↔ _root_.finitePlaceBelow (K := K) W ∈ S)
    {a : IdeleGroup L}
    (ha :
      a ∈ idelePowerLocalUnitSubgroup (K := L) n S' ∅) :
    IdeleGroup.norm K L a ∈
      idelePowerLocalUnitSubgroup (K := K) n S ∅ := by
  classical
  rw [mem_idelePowerLocalUnitSubgroup_iff] at ha ⊢
  obtain ⟨haInfinite, haSupported, haAway⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · intro w
    let : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = w},
        W.1.1.LiesOver w.1 :=
      fun W =>
        ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    rw [IdeleGroup.infiniteComponent_norm_eq_prod]
    apply Subgroup.prod_mem
    intro W _
    obtain ⟨x, hx⟩ :=
      (MonoidHom.mem_range
        (G := W.1.Completionˣ)).mp
        (haInfinite W.1)
    apply
      (MonoidHom.mem_range
        (G := w.Completionˣ)).mpr
    refine
      ⟨LocalFieldTheory.normUnits
          w.Completion W.1.Completion x, ?_⟩
    rw [powMonoidHom_apply] at hx ⊢
    rw [← hx, map_pow]
  · intro v₀ hv₀
    let vK := HeightOneSpectrum.adicAbv K v₀
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v₀
    let eAbove :=
      finitePlaceExtensionEquivAbove
        (K := K) (L := L) v₀
    let :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    let : Fintype {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀} :=
      Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
    let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀},
        Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      fun W =>
        (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
    rw [IdeleGroup.finiteComponent_norm_eq_prod]
    apply Subgroup.prod_mem
    intro W _
    have hWS : W.1 ∈ S' :=
      (hS W.1).2 (by simpa only [W.2] using hv₀)
    obtain ⟨x, hx⟩ :=
      (MonoidHom.mem_range
        (G := (W.1.adicCompletion L)ˣ)).mp
        (haSupported W.1 hWS)
    apply
      (MonoidHom.mem_range
        (G := (v₀.adicCompletion K)ˣ)).mpr
    refine
      ⟨LocalFieldTheory.normUnits
          (v₀.adicCompletion K) (W.1.adicCompletion L) x, ?_⟩
    rw [powMonoidHom_apply] at hx ⊢
    rw [← hx, map_pow]
  · intro v₀ hv₀
    simp only [Finset.union_empty] at hv₀
    let vK := HeightOneSpectrum.adicAbv K v₀
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v₀
    let eAbove :=
      finitePlaceExtensionEquivAbove
        (K := K) (L := L) v₀
    let :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    let : Fintype {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀} :=
      Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
    let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀},
        Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      fun W =>
        (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
    rw [IdeleGroup.finiteComponent_norm_eq_prod]
    apply Subgroup.prod_mem
    intro W _
    have hWaway : W.1 ∉ S' := by
      intro hWS
      have hbelow := (hS W.1).1 hWS
      exact hv₀ (by simpa only [W.2] using hbelow)
    have hWunit :
        IdeleGroup.finiteComponent W.1 a ∈
          (W.1.adicCompletionIntegers L).units :=
      haAway W.1 (by
        simpa only [Finset.union_empty] using hWaway)
    let z : (W.1.adicCompletionIntegers L).units :=
      ⟨IdeleGroup.finiteComponent W.1 a, hWunit⟩
    simpa only [z, Subgroup.coe_subtype] using
      IdeleGroup.finitePlace_normUnits_mem_integerUnits
        (K := K) (L := L) v₀ W z

/-- Under exact compatibility of the finite supports, the ordinary
idèle-class norm maps the power-local-unit idèle-class subgroup over `L`
into the corresponding subgroup over `K`. -/
theorem ideleClassNorm_map_powerLocalUnitSubgroup_le_of_supports_above
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (S' : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ W : HeightOneSpectrum (𝓞 L),
      W ∈ S' ↔ _root_.finitePlaceBelow (K := K) W ∈ S) :
    (ideleClassPowerLocalUnitSubgroup (K := L) n S' ∅).map
        (_root_.ideleClassNorm K L) ≤
      ideleClassPowerLocalUnitSubgroup (K := K) n S ∅ := by
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨a, ha, rfl⟩ :=
    (mem_ideleClassPowerLocalUnitSubgroup_iff
      (K := L) n S' ∅ c).mp hc
  rw [_root_.ideleClassNorm_mk]
  exact
    (mem_ideleClassPowerLocalUnitSubgroup_iff
      (K := K) n S ∅ _).2
      ⟨IdeleGroup.norm K L a,
        ideleNorm_mem_powerLocalUnitSubgroup_of_supports_above
          (K := K) (L := L) n S S' hS ha,
        rfl⟩

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SUnitKummerNormCore
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The full S-unit Kummer norm core

Starting from a prescribed finite set of finite places, we enlarge it by
a fixed idelic support and by a chosen support of the exponent.  For this
enlarged set, a principal idele satisfies the local power conditions exactly
when it is the power of an `S`-unit.  Consequently the associated idele-class
power quotient has the same cardinality as the Galois group of the full
`S`-unit Kummer extension.

These are the two concrete cardinal ingredients in the class-field existence
argument.
-/

open scoped NumberField Classical BigOperators

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain
open GlobalClassFieldTheory.ClassFieldAxiom
open KummerTheory

variable {K : Type} [Field K] [NumberField K]

/-- Away from the chosen Kummer norm support, the exponent is a local
unit.  This is the local input needed for the unramifiedness of the full
`S`-unit Kummer extension. -/
theorem valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {w : HeightOneSpectrum (𝓞 K)}
    (hw : w ∉ sUnitKummerNormSupport (K := K) n S) :
    w.valuation K ((n : ℕ) : K) = 1 := by
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let nUnit : Kˣ := Units.mk0 ((n : ℕ) : K) hnK
  have hwSupport :
      w ∉ chosenUnitFiniteSupport (K := K) nUnit := by
    intro hwSupport
    apply hw
    exact Finset.mem_union_right _ hwSupport
  have hnUnitVal :
      w.valuation K (nUnit : K) = 1 :=
    (mem_SUnitGroup_iff
      (K := K)
      (chosenUnitFiniteSupport (K := K) nUnit) nUnit).mp
        (mem_sUnitGroup_chosenUnitFiniteSupport
          (K := K) nUnit)
        w hwSupport
  change w.valuation K ((n : ℕ) : K) = 1 at hnUnitVal
  exact hnUnitVal

/-- Every finite place dividing the exponent belongs to the chosen
Kummer norm support. -/
theorem mem_sUnitKummerNormSupport_of_asIdeal_dvd_natCast
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {w : HeightOneSpectrum (𝓞 K)}
    (hw : w.asIdeal ∣ Ideal.span {((n : ℕ) : 𝓞 K)}) :
    w ∈ sUnitKummerNormSupport (K := K) n S := by
  by_contra hwSupport
  have hnValLt :
      w.valuation K ((n : ℕ) : K) < 1 := by
    simpa using
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_dvd
        (K := K) w ((n : ℕ) : 𝓞 K)).2 hw
  exact
    (ne_of_lt hnValLt)
      (valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport
        (K := K) n S hwSupport)

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitAbstractFixedField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional_over_extension _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

/-- Scalar extension between finite rational intermediate fields becomes
the literal inclusion between their fixed parts in the absolute
idele-class representation. -/
theorem rationalIdeleClassEquivFixed_extension_coe
    {F E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ E]
    (hFE : F ≤ E)
    (c : RelativeIdeleGroup.ClassGroup ℚ F) :
    (rationalIdeleClassEquivFixed E
        (Additive.ofMul
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E)
            (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
              (IntermediateField.inclusion hFE) c)))).1 =
      (rationalIdeleClassEquivFixed F
        (Additive.ofMul
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) c))).1 := by
  change
    Additive.ofMul
        (rationalIntermediateIdeleClassToDirectLimit E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E)
            (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
              (IntermediateField.inclusion hFE) c))) =
      Additive.ofMul
        (rationalIntermediateIdeleClassToDirectLimit F
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) c))
  exact congrArg Additive.ofMul
    (rationalIntermediateIdeleClassToDirectLimit_extension hFE c)

/-- The distinguished base fixed-part equivalence sends an ordinary
rational idele class to its diagonal class at every finite Galois level
of the absolute direct limit. -/
theorem rationalIdeleClassEquivBaseFixed_coe
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (c : IdeleClassGroup ℚ) :
    (rationalIdeleClassEquivBaseFixed
        (Additive.ofMul c)).1 =
      Additive.ofMul
        (rationalRelativeIdeleClassToDirectLimit E
          (RelativeIdeleGroup.classInclusion ℚ E c)) := by
  let B := (⊥ :
    IntermediateField ℚ (SeparableClosure ℚ))
  let : FiniteDimensional ℚ B :=
    (IntermediateField.botEquiv
      ℚ (SeparableClosure ℚ)).symm.toLinearEquiv.finiteDimensional
  let : NumberField B :=
    NumberField.of_module_finite ℚ B
  let e : ℚ ≃ₐ[ℚ] B :=
    (IntermediateField.botEquiv
      ℚ (SeparableClosure ℚ)).symm
  let hBE :
      B ≤ (E : IntermediateField ℚ (SeparableClosure ℚ)) :=
    bot_le
  let cB : RelativeIdeleGroup.ClassGroup ℚ B :=
    RelativeIdeleGroup.classInclusion ℚ B c
  have hbaseChange :
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := B) cB =
        ideleClassCongr e c := by
    calc
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := B) cB =
          ideleClassExtension ℚ B c := by
        simpa only [cB] using
          (_root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion
            (K := ℚ) (L := B) c)
      _ = ideleClassCongr e c :=
        DFunLike.congr_fun
          (rationalIdeleClassExtension_eq_ideleClassCongr e) c
  have hclassEmbedding :
      RelativeIdeleGroup.classEmbedding (K := ℚ) (L := B) (M := E)
          (IntermediateField.inclusion hBE) cB =
        RelativeIdeleGroup.classInclusion ℚ E c := by
    simpa only [cB] using
      (rationalRelativeIdeleClassEmbedding_classInclusion hBE c)
  have h0 :
      (rationalIdeleClassEquivBaseFixed (Additive.ofMul c)).1 =
        (rationalIdeleClassEquivFixed B
          (Additive.ofMul (ideleClassCongr e c))).1 := by
    rfl
  have h1 :
      (rationalIdeleClassEquivFixed B
          (Additive.ofMul (ideleClassCongr e c))).1 =
        (rationalIdeleClassEquivFixed B
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := B) cB))).1 :=
    congrArg
      (fun x : IdeleClassGroup B =>
        (rationalIdeleClassEquivFixed B (Additive.ofMul x)).1)
      hbaseChange.symm
  have h2 :
      (rationalIdeleClassEquivFixed B
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := B) cB))).1 =
        (rationalIdeleClassEquivFixed E
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E)
              (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := B) (M := E)
                (IntermediateField.inclusion hBE) cB)))).1 :=
    (rationalIdeleClassEquivFixed_extension_coe hBE cB).symm
  have h3 :
      (rationalIdeleClassEquivFixed E
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E)
              (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := B) (M := E)
                (IntermediateField.inclusion hBE) cB)))).1 =
        Additive.ofMul
          (rationalIntermediateIdeleClassToDirectLimit E
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E)
              (RelativeIdeleGroup.classInclusion ℚ E c))) := by
    change
      Additive.ofMul
          (rationalIntermediateIdeleClassToDirectLimit E
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E)
              (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := B) (M := E)
                (IntermediateField.inclusion hBE) cB))) = _
    rw [hclassEmbedding]
  have h4 :
      Additive.ofMul
          (rationalIntermediateIdeleClassToDirectLimit E
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E)
              (RelativeIdeleGroup.classInclusion ℚ E c))) =
        Additive.ofMul
          (rationalRelativeIdeleClassToDirectLimit E
            (RelativeIdeleGroup.classInclusion ℚ E c)) :=
    congrArg Additive.ofMul
      (rationalFiniteGaloisIdeleClassToDirectLimit_baseChange
        E (RelativeIdeleGroup.classInclusion ℚ E c))
  exact Eq.trans h0 (Eq.trans h1 (Eq.trans h2 (Eq.trans h3 h4)))

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicTorsionFixedField
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.closedFixingSubgroup_normal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.LubinTate.standardLubinTateUnitParameter_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The cyclotomic torsion fixed field

`rationalCyclotomicField` now denotes the actual field `ℚ(μ∞)` inside
`SeparableClosure ℚ`.  Its actual Galois group is therefore the standard
mathlib type
`rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField`; its finite
cyclotomic levels form a divisibility-directed system with supremum the
whole field.  The torsion fixed field is the actual
intermediate field `rationalCyclotomicTorsionFixedField`.

The actual continuous cyclotomic character identifies the full Galois
group with `ℤ̂ˣ`.  Applying infinite Galois correspondence to the actual
torsion closure and the group-theoretic decomposition of `ℤ̂ˣ` gives the
cyclotomic `ℤ̂`-extension.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped IsMulCommutative
open KummerTheory
open ClassFormation

theorem rationalCyclotomicTorsionCoordinate_restrictNormal
    (σ :
      rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField) :
    torsionQuotientEquivOfZHatMulDecomposition
        (rationalCyclotomicField ≃ₐ[ℚ]
          rationalCyclotomicField)
        CyclotomicFinitePart
        (rationalCyclotomicCharacterContinuousMulEquiv.trans
          zHatUnitsDecomposition)
        dense_torsion_cyclotomicFinitePart
        (rationalCyclotomicTorsionRestrictionEquiv.symm
          (AlgEquiv.restrictNormalHom
            rationalCyclotomicTorsionFixedField σ)) =
      (zHatUnitsDecomposition
        (rationalCyclotomicCharacterContinuousMulEquiv σ)).1 := by
  rw [rationalCyclotomicTorsionRestrictionEquiv_symm_restrictNormal]
  exact
    torsionQuotientEquivOfZHatMulDecomposition_mk
      (rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
      CyclotomicFinitePart
      (rationalCyclotomicCharacterContinuousMulEquiv.trans
        zHatUnitsDecomposition)
      dense_torsion_cyclotomicFinitePart σ

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_CyclotomicKummerNormDescent
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.idealNormExponentMap_apply _root_.RayClass.idealNormLiftedModulusExponent_eq_zero_of_not_mem _root_.RayClass.mem_idealNormLiftedModulus_support_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Cyclotomic descent for full S-unit Kummer norms

This file implements the roots-of-unity descent in the existence proof of
global class field theory.  Starting from a finite seed of finite places of
`K`, it enlarges the seed just enough that its full inverse image in
`CyclotomicField n K` is a chosen Kummer norm support.  Thus the full
S-unit Kummer extension over the cyclotomic field has its concrete norm
subgroup described by Kummer theory, while the support is still exactly a
full inverse image and hence descends through the cyclotomic norm.

The final normal-closure step turns the resulting finite extension of `K`
into a genuine finite Galois extension without enlarging its norm subgroup.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

attribute [local instance] GlobalClassFieldTheory.GlobalClassFields.cyclotomicKummerNormDescent_neZero
attribute [local instance] GlobalClassFieldTheory.GlobalClassFields.cyclotomicKummerNormDescent_cyclotomicFiniteDimensional
noncomputable local instance
    cyclotomicKummerNormDescent_cyclotomicIsGalois_r86d1f4_1
    (n : ℕ+) :
    IsGalois K (CyclotomicField (n : ℕ) K) :=
  IsCyclotomicExtension.isGalois
    {(n : ℕ)} K (CyclotomicField (n : ℕ) K)
/-- A finite support on `K` whose full inverse image in
`CyclotomicField n K` contains the chosen Kummer norm support upstairs.

The construction first forms the chosen support above the prescribed
seed and then adds the places below it.  Taking all places above this enlarged
base support saturates every fibre without losing the largeness and exponent
support required by the full S-unit Kummer calculation. -/
noncomputable def cyclotomicKummerNormSupport
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  let C := CyclotomicField (n : ℕ) K
  let seedAbove :=
    finitePlacesAbove (K := K) (L := C) seed
  let canonicalAbove :=
    sUnitKummerNormSupport (K := C) n seedAbove
  exact seed ∪ canonicalAbove.image
    (fun W => finitePlaceBelow (K := K) W)

/-- The prescribed finite seed is contained in its cyclotomic Kummer norm
support. -/
theorem subset_cyclotomicKummerNormSupport
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    seed ⊆ cyclotomicKummerNormSupport (K := K) n seed := by
  classical
  intro v hv
  simp only [cyclotomicKummerNormSupport]
  exact Finset.mem_union_left _ hv

/-- All finite places of the cyclotomic field above the enlarged base
support.  This is the fibre-saturated support used by norm descent. -/
noncomputable def cyclotomicKummerNormSupportAbove
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset
      (HeightOneSpectrum
        (𝓞 (CyclotomicField (n : ℕ) K))) := by
  let C := CyclotomicField (n : ℕ) K
  exact finitePlacesAbove (K := K) (L := C)
    (cyclotomicKummerNormSupport (K := K) n seed)

/-- Membership in the upstairs support is exactly membership of the place
below in the enlarged base support. -/
@[simp]
theorem mem_cyclotomicKummerNormSupportAbove_iff
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K)))
    (W :
      HeightOneSpectrum
        (𝓞 (CyclotomicField (n : ℕ) K))) :
    W ∈ cyclotomicKummerNormSupportAbove (K := K) n seed ↔
      finitePlaceBelow (K := K) W ∈
        cyclotomicKummerNormSupport (K := K) n seed := by
  let C := CyclotomicField (n : ℕ) K
  simpa only [cyclotomicKummerNormSupportAbove] using
    (mem_finitePlacesAbove_iff
      (K := K) (L := C)
      (cyclotomicKummerNormSupport (K := K) n seed) W)

/-- The fibre-saturated support upstairs is already fixed by the chosen
Kummer-support enlargement. -/
theorem sUnitKummerNormSupport_cyclotomicKummerNormSupportAbove
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnitKummerNormSupport
        (K := CyclotomicField (n : ℕ) K) n
        (cyclotomicKummerNormSupportAbove (K := K) n seed) =
      cyclotomicKummerNormSupportAbove (K := K) n seed := by
  classical
  let C := CyclotomicField (n : ℕ) K
  let seedAbove :=
    finitePlacesAbove (K := K) (L := C) seed
  let canonicalAbove :=
    sUnitKummerNormSupport (K := C) n seedAbove
  let baseSupport :=
    cyclotomicKummerNormSupport (K := K) n seed
  let saturatedAbove :=
    cyclotomicKummerNormSupportAbove (K := K) n seed
  have hcanonical :
      canonicalAbove ⊆ saturatedAbove := by
    intro W hW
    rw [show saturatedAbove =
      finitePlacesAbove (K := K) (L := C) baseSupport by
        rfl]
    rw [mem_finitePlacesAbove_iff]
    change finitePlaceBelow (K := K) W ∈
      seed ∪ canonicalAbove.image
        (fun V => finitePlaceBelow (K := K) V)
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨W, hW, rfl⟩)
  apply Finset.Subset.antisymm
  · intro W hW
    have hW' :
        (W ∈ saturatedAbove ∨
          W ∈ IdeleGroup.sufficientlyLargeFiniteSet (K := C)) ∨
          W ∈ chosenUnitFiniteSupport
            (K := C)
            (Units.mk0 ((n : ℕ) : C)
              (cyclotomicKummerNormDescent_natCast_ne_zero
                (K := K) n)) := by
      simpa only [sUnitKummerNormSupport, Finset.mem_union] using hW
    rcases hW' with (hWsat | hWlarge) | hWexp
    · exact hWsat
    · apply hcanonical
      simp only [canonicalAbove, sUnitKummerNormSupport,
        Finset.mem_union]
      exact Or.inl (Or.inr hWlarge)
    · apply hcanonical
      simp only [canonicalAbove, sUnitKummerNormSupport,
        Finset.mem_union]
      exact Or.inr hWexp
  · exact subset_sUnitKummerNormSupport
      (K := C) n saturatedAbove

/-- Enlarging a support by the cyclotomic Kummer requirements is
idempotent.  In particular, downstream neighbourhood arguments may choose a
support containing these requirements from the outset without a second
change of support. -/
@[simp]
theorem cyclotomicKummerNormSupport_idem
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    cyclotomicKummerNormSupport (K := K) n
        (cyclotomicKummerNormSupport (K := K) n seed) =
      cyclotomicKummerNormSupport (K := K) n seed := by
  classical
  let C := CyclotomicField (n : ℕ) K
  let S := cyclotomicKummerNormSupport (K := K) n seed
  let SAbove :=
    cyclotomicKummerNormSupportAbove (K := K) n seed
  have hstable :
      sUnitKummerNormSupport (K := C) n SAbove = SAbove := by
    simpa only [C, SAbove] using
      sUnitKummerNormSupport_cyclotomicKummerNormSupportAbove
        (K := K) n seed
  apply Finset.Subset.antisymm
  · intro v hv
    change v ∈
      S ∪
        (sUnitKummerNormSupport (K := C) n SAbove).image
          (fun W => finitePlaceBelow (K := K) W) at hv
    rcases Finset.mem_union.mp hv with hvS | hvAbove
    · exact hvS
    · rw [hstable] at hvAbove
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hvAbove
      exact
        (mem_cyclotomicKummerNormSupportAbove_iff
          (K := K) n seed W).mp hW
  · exact subset_cyclotomicKummerNormSupport (K := K) n S

/-- The actual full S-unit Kummer extension over the cyclotomic base,
formed inside its fixed separable closure and using the chosen enlargement
of the fibre-saturated support above `K`.  The preceding stability theorem
shows that this enlargement is equal to the fibre-saturated support; retaining
it in the definition keeps the extension definitionally aligned with the
exact Kummer norm-realization theorem. -/
noncomputable abbrev cyclotomicFullSUnitKummerExtension
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    IntermediateField
      (CyclotomicField (n : ℕ) K)
      (SeparableClosure (CyclotomicField (n : ℕ) K)) :=
  KummerTheory.fullSUnitKummerExtension
    (K := CyclotomicField (n : ℕ) K)
    (Omega := SeparableClosure (CyclotomicField (n : ℕ) K))
    n (sUnitKummerNormSupport
      (K := CyclotomicField (n : ℕ) K) n
      (cyclotomicKummerNormSupportAbove (K := K) n seed))

/-- The cyclotomic full S-unit Kummer extension is finite over the
cyclotomic base. -/
theorem cyclotomicFullSUnitKummerExtension_finiteDimensional
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    FiniteDimensional
      (CyclotomicField (n : ℕ) K)
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) := by
  let C := CyclotomicField (n : ℕ) K
  have hmu : (primitiveRoots (n : ℕ) C).Nonempty :=
    cyclotomicKummerNormDescent_primitiveRoots_nonempty
      (K := K) n
  have hnC : ((n : ℕ) : C) ≠ 0 :=
    cyclotomicKummerNormDescent_natCast_ne_zero
      (K := K) n
  simpa only [C, cyclotomicFullSUnitKummerExtension] using
    (KummerTheory.fullSUnitKummerExtension_finiteDimensional
      (K := C) (Omega := SeparableClosure C)
      n hnC hmu
      (sUnitKummerNormSupport (K := C) n
        (cyclotomicKummerNormSupportAbove (K := K) n seed)))

noncomputable local instance
    cyclotomicKummerNormDescent_kummerFiniteDimensional
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    FiniteDimensional
      (CyclotomicField (n : ℕ) K)
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  cyclotomicFullSUnitKummerExtension_finiteDimensional
    (K := K) n seed

/-- The Kummer layer is a number field via its finite extension of the
cyclotomic number field.  This is deliberately a named, non-instance boundary:
downstream base-tower instances must not make every `NumberField` search unfold
the full S-unit Kummer construction. -/
theorem cyclotomicKummerNormDescent_kummerNumberField
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    NumberField
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  NumberField.of_module_finite
    (CyclotomicField (n : ℕ) K)
    (cyclotomicFullSUnitKummerExtension (K := K) n seed)

@[reducible]
noncomputable local instance
    cyclotomicKummerNormDescent_kummerAlgebraOverBase
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    Algebra K
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  ((algebraMap
      (CyclotomicField (n : ℕ) K)
      (cyclotomicFullSUnitKummerExtension (K := K) n seed)).comp
    (algebraMap K (CyclotomicField (n : ℕ) K))).toAlgebra

@[reducible]
noncomputable def
    cyclotomicKummerNormDescent_kummerSMulOverBase
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    SMul K
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  Algebra.toSMul
    (self := cyclotomicKummerNormDescent_kummerAlgebraOverBase
      (K := K) n seed)

@[reducible]
noncomputable def
    cyclotomicKummerNormDescent_kummerModuleOverBase
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    Module K
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  Algebra.toModule

theorem
    cyclotomicKummerNormDescent_kummerScalarTower
    (n : ℕ+)
    (seed : Finset (HeightOneSpectrum (𝓞 K))) :
    IsScalarTower K
      (CyclotomicField (n : ℕ) K)
      (cyclotomicFullSUnitKummerExtension (K := K) n seed) :=
  IsScalarTower.of_algebraMap_eq' rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_NormConductor
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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

attribute [local instance] GlobalClassFieldTheory.GlobalClassFields.normConductorIdeleClassGroupIsMulCommutative
/-- The actual idele-class norm subgroup has finite index. -/
instance ideleClassNorm_rangeFiniteIndex :
    ((_root_.ideleClassNorm K L).range).FiniteIndex :=
  ConductorialSubgroup.finiteIndex
    (ideleClassNormConductorialSubgroup (K := K) (L := L))

/-- If the zeroth one-place higher-unit class subgroup lies in the
actual idèle-class norm range, then that finite place is absent from
the narrow finite conductor support. -/
theorem
    not_mem_ideleClassNorm_narrowFiniteConductor_support_of_localHigherUnitClassSubgroup_zero_le
    (v : HeightOneSpectrum (𝓞 K))
    (hlocal :
      RayClass.localHigherUnitClassSubgroup v 0 ≤
        (_root_.ideleClassNorm K L).range) :
    v ∉
      (ideleClassNormNarrowFiniteConductor
        (K := K) (L := L)).support := by
  change v ∉
    (ideleClassNormConductorialSubgroup
      (K := K) (L := L)).narrowFiniteConductor.support
  rw [Finsupp.notMem_support_iff,
    (ideleClassNormConductorialSubgroup
      (K := K) (L := L)).narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent v]
  exact
    Nat.eq_zero_of_le_zero
      ((ideleClassNormConductorialSubgroup
        (K := K) (L := L)).narrowFiniteLocalConductorExponent_le v hlocal)

/-- If the chosen prime of `L` above `v` is algebraically unramified,
then `v` does not occur in the conductor of the actual idele-class norm
subgroup. -/
theorem
    not_mem_ideleClassNorm_narrowFiniteConductor_support_of_isUnramifiedAt
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v)).asIdeal) :
    v ∉
      (ideleClassNormNarrowFiniteConductor
        (K := K) (L := L)).support := by
  apply
    not_mem_ideleClassNorm_narrowFiniteConductor_support_of_localHigherUnitClassSubgroup_zero_le
      (K := K) (L := L) v
  exact
    localHigherUnitClassSubgroup_zero_le_ideleClassNorm_range_of_isUnramifiedAt
      (K := K) (L := L) v hunram

/-- The narrow finite conductor of an actual finite Galois idèle-class norm
subgroup is supported only at ramified finite places of the base field. -/
theorem ideleClassNorm_narrowFiniteConductor_support_subset_ramifiedBaseFinitePlaces :
    (ideleClassNormNarrowFiniteConductor
      (K := K) (L := L)).support ⊆
      _root_.ramifiedBaseFinitePlaces
        (K := K) (L := L) := by
  intro v hv
  by_contra hvRamified
  have hunram :
      Algebra.IsUnramifiedAt (𝓞 K)
        (_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v)).asIdeal := by
    by_contra hram
    apply hvRamified
    rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
    exact
      ⟨_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v),
        _root_.finitePlaceExtensionCentre_liesOver
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v),
        hram⟩
  exact
    (not_mem_ideleClassNorm_narrowFiniteConductor_support_of_isUnramifiedAt
      (K := K) (L := L) v hunram) hv

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_HilbertNormCharacterization
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.idealNormLiftedModulus_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.rationalFiniteModulus_apply _root_.RayClass.rationalModulus_finitePart_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Hilbert norm subgroups and unramified extensions

For a finite Galois extension with no ramified finite prime, the actual
idele-class narrow finite conductor is zero.  Consequently its norm subgroup
contains the big-Hilbert norm subgroup.  This is the norm-subgroup form
of the maximality of the big Hilbert class field.

The inclusion yields a canonical surjection from the narrow class group
onto the actual norm quotient, together with the exact kernel
factorization and the resulting divisibility of orders.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Keep norm-range quotient normality out of exported declaration types. -/
local instance
    hilbertNormCharacterization_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- If no finite prime of the base ramifies in the extension, then the
narrow finite conductor of the actual idele-class norm subgroup is zero. -/
theorem ideleClassNorm_narrowFiniteConductor_eq_zero_of_no_ramifiedFinitePlaces
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    ideleClassNormNarrowFiniteConductor (K := K) (L := L) = 0 := by
  ext v
  rw [Finsupp.zero_apply]
  apply Finsupp.notMem_support_iff.mp
  intro hv
  have hramified :=
    ideleClassNorm_narrowFiniteConductor_support_subset_ramifiedBaseFinitePlaces
      (K := K) (L := L) hv
  rw [hunramified] at hramified
  simp at hramified

/-- The norm subgroup of every finite Galois extension unramified at all
finite primes contains the big-Hilbert norm subgroup. -/
theorem
    bigHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_no_ramifiedFinitePlaces
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    bigHilbertClassFieldNormSubgroup (K := K) ≤
      (_root_.ideleClassNorm K L).range := by
  apply
    (bigHilbertClassFieldNormSubgroup_le_iff_narrowFiniteConductor_eq_zero
      (ideleClassNormConductorialSubgroup (K := K) (L := L))).2
  exact
    ideleClassNorm_narrowFiniteConductor_eq_zero_of_no_ramifiedFinitePlaces
      (K := K) (L := L) hunramified

/-- The canonical transition from the big-Hilbert reciprocity quotient
to the actual norm quotient of an everywhere finite-unramified
extension. -/
def bigHilbertClassFieldQuotientToIdeleClassNormQuotient
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    (IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K)) →*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  QuotientGroup.map
    (bigHilbertClassFieldNormSubgroup (K := K))
    ((_root_.ideleClassNorm K L).range)
    (MonoidHom.id _)
    (fun _ hx =>
      bigHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_no_ramifiedFinitePlaces
        (K := K) (L := L) hunramified hx)

/-- The big-Hilbert quotient transition sends an idele class to the
same class modulo the actual norm subgroup. -/
@[simp]
theorem bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk
    (hunramified :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (x : IdeleClassGroup K) :
    bigHilbertClassFieldQuotientToIdeleClassNormQuotient
        (K := K) (L := L) hunramified
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K)) x) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K L).range) x :=
  rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SmallHilbertNormCharacterization
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalFiniteGaloisIdeleClassMulDistribMulAction _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Small Hilbert norm subgroups and everywhere-unramified extensions

For a finite Galois extension which is unramified at both finite and
infinite places, every idele integral at all finite places is an actual
relative-idele norm.  It follows that the actual idele-class norm range
contains the small-Hilbert norm subgroup.

This realizes the maximality of the small Hilbert class field on the
norm-subgroup side.  The resulting quotient transition gives a canonical
surjection from the ordinary class group, its exact kernel
factorization, and the divisibility of the extension norm quotient order
by the class number.
-/

open scoped IsMulCommutative NumberField NumberField.LiesOver

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Keep norm-range quotient normality out of exported declaration types. -/
local instance
    smallHilbertNormCharacterization_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- In an extension unramified at every finite and infinite place,
every idele integral at all finite places is an actual relative-idele
norm. -/
theorem
    integralAtFinitePlaces_le_relativeIdeleNorm_range_of_everywhereUnramified
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    IdeleGroup.integralAtFinitePlaces (K := K) ≤
      (RelativeIdeleGroup.norm K L).range := by
  intro a ha
  refine
    (_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms
      (K := K) (L := L) a).2 ⟨?_, ?_⟩
  · intro v
    rw [
      infiniteTensorNormSubgroup_eq_top_of_isUnramifiedAtInfinitePlaces
        (K := K) (L := L) v]
    exact Subgroup.mem_top _
  · intro v
    rw [
      _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
    apply
      _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v
        (chosenFinitePlaceIsUnramified_of_no_ramifiedFinitePlaces
          (K := K) (L := L) hunramifiedFinite v)
    change a.2 v ∈ (v.adicCompletionIntegers K).units
    exact
      (FiniteIdeleGroup.mem_integralSubgroup_iff a.2).1 ha v

theorem integralIdeleClass_mem_ideleClassNorm_range_of_everywhereUnramified
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    {a : IdeleGroup K}
    (ha : a ∈ IdeleGroup.integralAtFinitePlaces (K := K)) :
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a ∈
      (_root_.ideleClassNorm K L).range := by
  obtain ⟨z, hz⟩ :=
    integralAtFinitePlaces_le_relativeIdeleNorm_range_of_everywhereUnramified
      (K := K) (L := L) hunramifiedFinite ha
  refine
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (_root_.relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z),
      ?_⟩
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (IdeleGroup.norm K L
          (_root_.relativeIdeleBaseChangeMulEquiv
            (K := K) (L := L) z)) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a
  rw [IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv, hz]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem principalIdeleClass_mem_ideleClassNorm_range
    {a : IdeleGroup K}
    (ha : a ∈ IdeleGroup.principalSubgroup K) :
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a ∈
      (_root_.ideleClassNorm K L).range := by
  have haOne :
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a = 1 :=
    (QuotientGroup.eq_one_iff a).2 ha
  rw [haOne]
  exact ((_root_.ideleClassNorm K L).range).one_mem

/-- The norm subgroup of an everywhere-unramified finite Galois
extension contains the small-Hilbert norm subgroup. -/
theorem
    smallHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_everywhereUnramified
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    smallHilbertClassFieldNormSubgroup (K := K) ≤
      (_root_.ideleClassNorm K L).range := by
  rw [smallHilbertClassFieldNormSubgroup,
    Subgroup.map_le_iff_le_comap]
  apply sup_le
  · intro a ha
    exact
      integralIdeleClass_mem_ideleClassNorm_range_of_everywhereUnramified
        (K := K) (L := L) hunramifiedFinite ha
  · intro a ha
    exact
      principalIdeleClass_mem_ideleClassNorm_range
        (K := K) (L := L) ha

/-- The canonical transition from the small-Hilbert reciprocity
quotient to the actual norm quotient of an everywhere-unramified
extension. -/
def smallHilbertClassFieldQuotientToIdeleClassNormQuotient
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅) :
    (IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K)) →*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  QuotientGroup.map
    (smallHilbertClassFieldNormSubgroup (K := K))
    ((_root_.ideleClassNorm K L).range)
    (MonoidHom.id _)
    (fun _ hx =>
      smallHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_everywhereUnramified
        (K := K) (L := L) hunramifiedFinite hx)

/-- The small-Hilbert quotient transition sends an idele class to the
same class modulo the actual norm subgroup. -/
@[simp]
theorem smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (x : IdeleClassGroup K) :
    smallHilbertClassFieldQuotientToIdeleClassNormQuotient
        (K := K) (L := L) hunramifiedFinite
        (QuotientGroup.mk'
          (smallHilbertClassFieldNormSubgroup (K := K)) x) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K L).range) x :=
  rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_HilbertClassFieldMaximality
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Maximality criteria for Hilbert class fields

An unramified cyclic extension reaches the big or small Hilbert norm
subgroup exactly when its degree reaches the corresponding narrow or
ordinary class number.  Thus a maximal-degree unramified cyclic
extension has the canonical Hilbert reciprocity quotient.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

theorem hilbertClassFieldMaximalityIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] hilbertClassFieldMaximalityIdeleClassGroupIsMulCommutative

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_NormRayClassMaximality
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Exact narrow finite ray-class presentations of norm quotients

For every finite Galois extension, the ray class group at the exact narrow
finite conductor surjects onto the actual idèle-class norm quotient.  This
file characterizes when that presentation has no residual kernel: the norm
subgroup is then exactly the congruence subgroup at its narrow finite
conductor, equivalently the two finite quotient groups have the same order.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

/-- Canonical class-group commutativity supplies normality for the quotient. -/
theorem normRayClassMaximalityClassGroupIsMulCommutative
    (F : Type*) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] normRayClassMaximalityClassGroupIsMulCommutative

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_NormTowerConductor
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Norm quotients and narrow finite conductors in a field tower

For a finite tower `K ⊂ M ⊂ L`, norm transitivity places the actual
idele-class norms from `L` inside those from `M`.  This produces the
canonical quotient transition

`C_K / N_{L/K} C_L → C_K / N_{M/K} C_M`.

The transition is surjective, its kernel is the image of
`N_{M/K} C_M` modulo `N_{L/K} C_L`, and its orders satisfy the
corresponding exact factorization.  When both extensions over `K` are
Galois, the narrow finite conductor is contravariant under this
inclusion and the conductor support of the intermediate extension is
contained in that of the top extension.  This is the finite part in the
all-real-positive convention, not a claim about the full archimedean
conductor.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

/-- The canonical commutativity witness used to form ordinary norm quotients. -/
theorem normTowerIdeleClassIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] normTowerIdeleClassIsMulCommutative

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_SeparableClosurePadicLift
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.GlobalClassFieldTheory.GlobalClassFields.mem_cyclotomicKummerNormSupportAbove_iff _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.idealNormExponentMap_apply _root_.RayClass.idealNormLiftedModulusExponent_eq_zero_of_not_mem _root_.RayClass.mem_idealNormLiftedModulus_support_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Separable-closure p-adic lifts for local-global Artin compatibility

This module constructs the finite-place decomposition restriction maps and
the positive p-adic cyclotomic lifts used in the local-global comparison.
-/

open scoped NumberField
open AlgebraicNumberTheory IsDedekindDomain NumberField
open IdeleGroup RelativeIdeleGroup
open AlgebraicNumberTheory.Valuations
open HilbertRamification

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_6
attribute [local instance] GlobalClassFieldTheory.Reciprocity.automorphismCyclicFixedFieldNumberField
omit [NumberField L] in
/-- The finite place induced on the cyclic fixed field lies above the original
base-field place. -/
@[simp]
theorem finitePlaceBelow_automorphismCyclicFixedPlace
    (v : HeightOneSpectrum (𝓞 K))
    (σ : Gal(L / K)) :
    finitePlaceBelow (K := K)
        (automorphismCyclicFixedPlace v σ) =
      v := by
  let M := automorphismCyclicFixedField σ
  exact
    finitePlaceBelow_finitePlaceExtensionCentre
      (K := K) (L := M) v
      (restrictFinitePlaceExtension
        (K := K) (L := L) (E := M) v
        (chosenFinitePlaceExtension (L := L) v))

end Reciprocity
end GlobalClassFieldTheory
end
end


