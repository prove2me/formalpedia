-- Prove2me | Definitions.Def_OAIQ244Duke087
-- name    : OAIQ244Duke087
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T01:33:26.855701+00:00
-- url     : https://prove2.me/theorems/c58dfe6e-415a-4b1a-9c72-9e0eb5fa33ac
-- title:
--   Definitions bundle OAIQ244Duke087 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 9 definitions, 8 instances and 20 theorems. The definitions and types are `GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap`, `GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards`, `GlobalClassFieldTheory.Reciprocity.arithmeticChosenInfinitePlaceArtinMonoidHom`, `GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceLocalArithmeticFrobenius`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceLocalArtinNegOneValue`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionConjugation`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverfieldConjugation`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedFieldEmbedding`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_GlobalClassFields_CyclicRayClassMaximality`, `GlobalClassFieldTheory_GlobalClassFields_HilbertClassFieldMaximality`, `GlobalClassFieldTheory_GlobalClassFields_NormRayClassMaximality`, `GlobalClassFieldTheory_GlobalClassFields_NormTowerConductor`, `GlobalClassFieldTheory_GlobalClassFields_SUnitKummerNormCore`, `GlobalClassFieldTheory_Reciprocity_ArithmeticNormalization`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceCompatibility`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RamifiedOverextension`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_UnramifiedNormalization`, `GlobalClassFieldTheory_Reciprocity_InfiniteLocalGlobalArtinCompatibility`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_Factorization`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke080`, `OAIQ244Duke081` and `OAIQ244Duke082` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke094`; the statement `GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceLocalArtin_eq_arithmeticFrobenius_inv_of_unramified`; the proof of `GlobalClassFieldTheory.Reciprocity.chosenFinitePlaceLocalArtin_eq_arithmeticFrobenius_inv_of_unramified`.
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
import Mathlib.NumberTheory.NumberField.CMField
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
import Definitions.Def_OAIQ244Duke080
import Definitions.Def_OAIQ244Duke081
import Definitions.Def_OAIQ244Duke082

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_NormRayClassMaximality
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_ideleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.idealNormLiftedModulus_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.rationalFiniteModulus_apply _root_.RayClass.rationalModulus_finitePart_apply _root_.RayClass.signToNarrow_mk
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

attribute [local instance] normRayClassMaximalityClassGroupIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual idèle-class norm subgroup is exactly the ray congruence
subgroup at its narrow finite conductor if and only if the conductor ray
class group and the actual norm quotient have the same order. -/
theorem
    ideleClassNorm_range_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_normQuotient_card :
    (_root_.ideleClassNorm K L).range =
        RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) ↔
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) := by
  constructor
  · intro hnorm
    calc
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) =
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))).index :=
        (Subgroup.index_eq_card _).symm
      _ = ((_root_.ideleClassNorm K L).range).index := by
        rw [← hnorm]
      _ =
          Nat.card
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range) :=
        Subgroup.index_eq_card _
  · intro hcard
    refine
      (eq_of_le_of_not_lt
        (ideleClassNorm_narrowFiniteConductor_isDefiningModulus
          (K := K) (L := L))
        ?_).symm
    intro hlt
    have hstrict := Subgroup.index_strictAnti hlt
    have hstrict' :
        Nat.card
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range) <
          Nat.card
            (RayClass.RayClassGroup
              (RayClass.Modulus.narrowOfFinite
                (ideleClassNormNarrowFiniteConductor
                  (K := K) (L := L)))) := by
      simpa only [Subgroup.index_eq_card] using hstrict
    rw [hcard] at hstrict'
    exact lt_irrefl _ hstrict'

/-- Two finite Galois extensions with the same exact narrow finite
conductor and maximal ray-class presentations have the same actual
idèle-class norm subgroup. -/
theorem
    ideleClassNorm_ranges_eq_of_narrowFiniteConductors_eq_of_rayClassGroup_cards_eq_normQuotient_cards
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (hconductor :
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) =
        ideleClassNormNarrowFiniteConductor (K := K) (L := M))
    (hLcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range))
    (hMcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := M)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K M).range)) :
    (_root_.ideleClassNorm K L).range =
      (_root_.ideleClassNorm K M).range := by
  calc
    (_root_.ideleClassNorm K L).range =
        RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := L))) :=
      (ideleClassNorm_range_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_normQuotient_card
        (K := K) (L := L)).2 hLcard
    _ =
        RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite
            (ideleClassNormNarrowFiniteConductor (K := K) (L := M))) :=
      congrArg
        (fun f => RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite f))
        hconductor
    _ = (_root_.ideleClassNorm K M).range :=
      ((ideleClassNorm_range_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_normQuotient_card
        (K := K) (L := M)).2 hMcard).symm

/-- The actual norm quotients of two maximal narrow finite conductor
ray-class presentations with the same conductor are canonically equivalent.
-/
def normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (hconductor :
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) =
        ideleClassNormNarrowFiniteConductor (K := K) (L := M))
    (hLcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range))
    (hMcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := M)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K M).range)) :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K M).range) :=
  QuotientGroup.quotientMulEquivOfEq
    (ideleClassNorm_ranges_eq_of_narrowFiniteConductors_eq_of_rayClassGroup_cards_eq_normQuotient_cards
      (K := K) (L := L) (M := M)
      hconductor hLcard hMcard)

/-- The canonical equivalence between maximal narrow finite conductor
ray-class norm quotients preserves every idèle-class representative. -/
@[simp]
theorem
    normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (hconductor :
      ideleClassNormNarrowFiniteConductor (K := K) (L := L) =
        ideleClassNormNarrowFiniteConductor (K := K) (L := M))
    (hLcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := L)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range))
    (hMcard :
      Nat.card
          (RayClass.RayClassGroup
            (RayClass.Modulus.narrowOfFinite
              (ideleClassNormNarrowFiniteConductor
                (K := K) (L := M)))) =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K M).range))
    (c : IdeleClassGroup K) :
    normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards
        (K := K) (L := L) (M := M)
        hconductor hLcard hMcard
        (QuotientGroup.mk'
          ((_root_.ideleClassNorm K L).range) c) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K M).range) c :=
  rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_CyclicRayClassMaximality
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Maximal cyclic quotients at the narrow finite conductor

For a finite cyclic extension, the actual idèle-class norm quotient has
order equal to the extension degree.  The ray class group at the exact
narrow finite conductor surjects onto this norm quotient.  This file
identifies the case in which that surjection is an isomorphism: precisely
when the ray class number already equals the extension degree.

Equivalently, the actual norm subgroup is then exactly the ray congruence
subgroup at its narrow finite conductor.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

/-- The canonical idèle-class multiplication makes every subgroup normal. -/
theorem cyclicRayClassMaximalityClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] cyclicRayClassMaximalityClassGroupIsMulCommutative

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_HilbertClassFieldMaximality
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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

attribute [local instance] hilbertClassFieldMaximalityIdeleClassGroupIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]

instance narrowClassGroup_finite :
    Finite (RayClass.NarrowClassGroup K) :=
  Finite.of_equiv
    (RayClass.RayClassGroup
      (RayClass.Modulus.narrowOfFinite
        (0 : RayClass.FiniteModulus K)))
    (RayClass.rayClassGroupNarrowZeroEquivNarrowClassGroup
      (K := K)).toEquiv

instance bigHilbertNormQuotient_finite :
    Finite
      (IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K)) :=
  Finite.of_equiv
    (RayClass.NarrowClassGroup K)
    (bigHilbertClassFieldQuotientEquivNarrowClassGroup
      (K := K)).symm.toEquiv

instance bigHilbertNormSubgroup_finiteIndex :
    (bigHilbertClassFieldNormSubgroup
      (K := K)).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_NormTowerConductor
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalFiniteGaloisIdeleClassMulDistribMulAction _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.instDirectedSystemFiniteGaloisIntermediateFieldRatSeparableClosureClassGroupSubtypeMemIntermediateFieldCoeMulDistribMulActionHomAlgEquivIdRationalRelativeIdeleClassTransition _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instMulDistribMulActionAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_ideleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
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

attribute [local instance] normTowerIdeleClassIsMulCommutative

variable {K : Type} [Field K] [NumberField K]

section Tower

variable
    {M L : Type}
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [IsGalois K M] [IsGalois K L]

omit [IsGalois K M] [IsGalois K L] in
/-- Norm transitivity puts every idele-class norm from the top field
inside the idele-class norm subgroup of the intermediate field. -/
theorem ideleClassNorm_range_le_of_tower :
    (_root_.ideleClassNorm K L).range ≤
      (_root_.ideleClassNorm K M).range := by
  calc
    (_root_.ideleClassNorm K L).range =
        (RelativeIdeleGroup.classNorm K L).range :=
      ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := L)
    _ ≤
        (RelativeIdeleGroup.classNorm K M).range := by
      rw [← towerCompositeClassNorm_range_eq K M L]
      rintro _ ⟨c, rfl⟩
      exact
        ⟨TowerRelativeIdeleGroup.classNorm K M L c, rfl⟩
    _ = (_root_.ideleClassNorm K M).range :=
      (ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := M)).symm

/-- The quotient transition induced by norm transitivity in a finite
field tower. -/
def ideleClassNormQuotientTowerMap :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) →*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K M).range) :=
  QuotientGroup.map
    ((_root_.ideleClassNorm K L).range)
    ((_root_.ideleClassNorm K M).range)
    (MonoidHom.id _)
    (fun _ hx =>
      ideleClassNorm_range_le_of_tower
        (K := K) (M := M) (L := L) hx)

omit [IsGalois K M] [IsGalois K L] in
/-- The tower norm-quotient transition sends an idele class to the same
class modulo the intermediate norm subgroup. -/
@[simp]
theorem ideleClassNormQuotientTowerMap_mk
    (x : IdeleClassGroup K) :
    ideleClassNormQuotientTowerMap
        (K := K) (M := M) (L := L)
        (QuotientGroup.mk'
          ((_root_.ideleClassNorm K L).range) x) =
      QuotientGroup.mk'
        ((_root_.ideleClassNorm K M).range) x :=
  rfl

end Tower

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SUnitKummerNormCore
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalFiniteGaloisIdeleClassMulDistribMulAction _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.instDirectedSystemFiniteGaloisIntermediateFieldRatSeparableClosureClassGroupSubtypeMemIntermediateFieldCoeMulDistribMulActionHomAlgEquivIdRationalRelativeIdeleClassTransition _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instMulDistribMulActionAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.finitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_ideleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHom_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalAbsoluteGaloisIdeleClass_smul_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same
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

/-- On the chosen Kummer norm support, the principal part of the
local power subgroup consists exactly of powers of `S`-units. -/
theorem
    principalIdelePowerLocalUnitSubgroup_eq_sUnitNthPowers_on_kummerNormSupport
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let S' := sUnitKummerNormSupport (K := K) n S
    principalIdelePowerLocalUnitSubgroup (K := K) n S' ∅ =
      sUnitNthPowersInField (K := K) n S' := by
  classical
  dsimp only
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let S' := sUnitKummerNormSupport (K := K) n S
  change
    principalIdelePowerLocalUnitSubgroup (K := K) n S' ∅ =
      sUnitNthPowersInField (K := K) n S'
  have hLarge :
      IdeleGroup.supportedAt
            (K := K) (S' : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤ := by
    simpa only [S'] using
      supportedAt_sUnitKummerNormSupport_sup_principalSubgroup_eq_top
        (K := K) n S
  apply le_antisymm
  · intro b hb
    have hbData :=
      (mem_idelePowerLocalUnitSubgroup_iff
        (K := K) n S' ∅
        (IdeleGroup.principalIdele K b)).mp hb
    have hbSUnit :
        b ∈ SUnitGroup (K := K) S' := by
      simpa only [Finset.union_empty] using
        (principalIdelePowerLocalUnitSubgroup_le_sUnitGroup
          (K := K) n S' ∅ hb)
    let M := KummerTheory.chosenSimpleKummerExtension K n hnK b
    let : FiniteDimensional K M :=
      KummerTheory.chosenSimpleKummerExtension_finiteDimensional
        K n hnK b
    let : IsAbelianGalois K M :=
      KummerTheory.chosenSimpleKummerExtension_isAbelianGalois
        K n hnK hmu b
    let : NumberField M :=
      NumberField.of_module_finite K M
    let : (RelativeIdeleGroup.principalSubgroup K M).Normal :=
      ⟨fun x hx g => by
        have hconj : g * x * g⁻¹ = x := by
          rw [mul_comm g x, mul_assoc, mul_inv_cancel, mul_one]
        rwa [hconj]⟩
    have hSplitS :
        ∀ w : HeightOneSpectrum (𝓞 K), w ∈ S' →
          _root_.FinitePlaceSplitsCompletely
            (K := K) (L := M) w := by
      intro w hw
      have hbLocal := hbData.2.1 w hw
      have hprincipal :
          IdeleGroup.finiteComponent w
              (IdeleGroup.principalIdele K b) =
            Units.map
              (algebraMap K (w.adicCompletion K)).toMonoidHom b := by
        apply Units.ext
        rfl
      rw [hprincipal] at hbLocal
      simpa only [M] using
        KummerTheory.chosenSimpleKummerExtension_finitePlaceSplitsCompletely_of_mem_nthPowerSubgroup
          (K := K) n hnK hmu b w hbLocal
    have hInfiniteTop :
        ∀ w : InfinitePlace K,
          _root_.infiniteTensorNormSubgroup
            (K := K) (L := M) w = ⊤ := by
      intro w
      have hbLocal := hbData.1 w
      have hprincipal :
          IdeleGroup.infiniteComponent w
              (IdeleGroup.principalIdele K b) =
            Units.map
              (algebraMap K w.Completion).toMonoidHom b := by
        apply Units.ext
        rfl
      rw [hprincipal] at hbLocal
      simpa only [M] using
        KummerTheory.chosenSimpleKummerExtension_infiniteTensorNormSubgroup_eq_top_of_mem_nthPowerSubgroup
          (K := K) n hnK hmu b w hbLocal
    have hAway :
        ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S' →
          _root_.ChosenFinitePlaceIsUnramified
            (K := K) (L := M) w := by
      intro w hw
      have hbVal :
          w.valuation K (b : K) = 1 :=
        (mem_SUnitGroup_iff
          (K := K) S' b).mp hbSUnit w hw
      have hnVal :
          w.valuation K ((n : ℕ) : K) = 1 := by
        exact
          valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport
            (K := K) n S hw
      simpa only [M] using
        KummerTheory.chosenSimpleKummerExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
          (K := K) n hnK hmu b w hbVal hnVal
    have hNormTop :
        (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range =
          ⊤ := by
      apply top_unique
      intro c _
      obtain ⟨a, rfl⟩ :=
        QuotientGroup.mk'_surjective
          (IdeleGroup.principalSubgroup K) c
      have ha :
          a ∈
            IdeleGroup.supportedAt
                (K := K)
                (S' : Set (HeightOneSpectrum (𝓞 K))) ⊔
              IdeleGroup.principalSubgroup K := by
        rw [hLarge]
        exact Subgroup.mem_top a
      rcases Subgroup.mem_sup.mp ha with
        ⟨u, hu, q, hq, huq⟩
      have hInfinite :
          ∀ w : InfinitePlace K,
            IdeleGroup.infiniteComponent w u ∈
              _root_.infiniteTensorNormSubgroup
                (K := K) (L := M) w := by
        intro w
        rw [hInfiniteTop w]
        exact Subgroup.mem_top _
      have hFinite :
          ∀ w : HeightOneSpectrum (𝓞 K),
            IdeleGroup.finiteComponent w u ∈
              (localTensorNorm
                (K := K) (L := M) w).range := by
        intro w
        rw [
          _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
            (K := K) (L := M) w]
        by_cases hwS : w ∈ S'
        · rw [
            _root_.chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely
              (K := K) (L := M) w (hSplitS w hwS)]
          exact Subgroup.mem_top _
        · apply
            _root_.adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup
              (K := K) (L := M) w (hAway w hwS)
          exact
            (IdeleGroup.mem_supportedAt_iff
              (K := K)
              (S' : Set (HeightOneSpectrum (𝓞 K))) u).mp
                hu w (by simpa using hwS)
      have huNorm :
          u ∈ (RelativeIdeleGroup.norm K M).range :=
        (_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms
          (K := K) (L := M) u).2
            ⟨hInfinite, hFinite⟩
      obtain ⟨z, hz⟩ := huNorm
      refine
        ⟨QuotientGroup.mk'
            (RelativeIdeleGroup.principalSubgroup K M) z, ?_⟩
      rw [RelativeIdeleGroup.Cohomology.ideleClassNorm_mk, hz]
      change
        QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) u =
          QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K) a
      have hqOne :
          QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K) q = 1 :=
        (QuotientGroup.eq_one_iff q).mpr hq
      rw [← huq, map_mul, hqOne]
      exact
        (mul_one
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) u :
            IdeleClassGroup K)).symm
    let : IsCyclic (M ≃ₐ[K] M) := by
      simpa only [M] using
        KummerTheory.chosenSimpleKummerExtension_isCyclic
          K n hnK hmu b
    obtain ⟨sigma, hsigma⟩ :=
      IsCyclic.exists_generator (α := M ≃ₐ[K] M)
    have hLower :
        Module.finrank K M ≤
          (RelativeIdeleGroup.Cohomology.ideleClassNorm K M).range.index :=
      Cohomology.finrank_le_ideleClassNorm_index
        (K := K) (L := M) sigma hsigma
    have hDegreeLe :
        Module.finrank K M ≤ 1 := by
      simpa only [hNormTop, Subgroup.index_top] using hLower
    have hDegree :
        Module.finrank K M = 1 :=
      le_antisymm hDegreeLe Module.finrank_pos
    have hAlgMap :
        Function.Bijective (algebraMap K M) :=
      (Algebra.finrank_eq_one_iff_bijective_algebraMap).mp
        hDegree
    let beta : Mˣ :=
      KummerTheory.chosenSimpleKummerRootUnit K n hnK b
    have hbeta :
        beta ^ (n : ℕ) =
          Units.map (algebraMap K M).toMonoidHom b := by
      simpa only [M, beta] using
        KummerTheory.chosenSimpleKummerRootUnit_pow K n hnK b
    obtain ⟨x, hx⟩ := hAlgMap.2 (beta : M)
    have hx_ne : x ≠ 0 := by
      intro hx_zero
      apply beta.ne_zero
      calc
        (beta : M) = algebraMap K M x := hx.symm
        _ = 0 := by rw [hx_zero, map_zero]
    let xUnit : Kˣ := Units.mk0 x hx_ne
    have hbPower :
        b ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
      apply (MonoidHom.mem_range (G := Kˣ)).mpr
      refine ⟨xUnit, ?_⟩
      rw [powMonoidHom_apply]
      apply Units.ext
      apply (algebraMap K M).injective
      change
        algebraMap K M (x ^ (n : ℕ)) =
          algebraMap K M (b : K)
      calc
        algebraMap K M (x ^ (n : ℕ)) =
            (beta : M) ^ (n : ℕ) := by
          rw [map_pow, hx]
        _ = algebraMap K M (b : K) := by
          simpa using congrArg Units.val hbeta
    exact
      (mem_sUnitNthPowersInField_iff
        (K := K) n S' b).2
          ⟨hbSUnit, hbPower⟩
  · simpa only [Finset.union_empty] using
      sUnitNthPowersInField_le_principalIdelePowerLocalUnitSubgroup
        (K := K) n S' ∅

/-- The idele-class power quotient attached to the chosen Kummer norm
support has cardinality `n` to the number of supported places. -/
theorem card_ideleClassPowerLocalUnitQuotient_on_kummerNormSupport
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let S' := sUnitKummerNormSupport (K := K) n S
    Nat.card
        (IdeleClassPowerLocalUnitQuotient
          (K := K) n S' ∅) =
      (n : ℕ) ^ totalPlaceCard (K := K) S' := by
  classical
  dsimp only
  let S' := sUnitKummerNormSupport (K := K) n S
  change
    Nat.card
        (IdeleClassPowerLocalUnitQuotient
          (K := K) n S' ∅) =
      (n : ℕ) ^ totalPlaceCard (K := K) S'
  have hPrincipal :
      principalIdelePowerLocalUnitSubgroup
          (K := K) n S' ∅ =
        sUnitNthPowersInField (K := K) n S' := by
    simpa only [S'] using
      principalIdelePowerLocalUnitSubgroup_eq_sUnitNthPowers_on_kummerNormSupport
        (K := K) n hmu S
  have hDen :
      sUnitPrincipalIdelePowerSubgroup
          (K := K) n S' ∅ =
        (powMonoidHom (n : ℕ) :
          SUnitGroup (K := K) (S' ∪ ∅) →*
            SUnitGroup (K := K) (S' ∪ ∅)).range := by
    unfold sUnitPrincipalIdelePowerSubgroup
    rw [Finset.union_empty]
    rw [hPrincipal, sUnitNthPowersInField]
    exact
      Subgroup.comap_map_eq_self_of_injective
        (SUnitGroup (K := K) S').subtype_injective _
  have hDiv :
      ∀ w : HeightOneSpectrum (𝓞 K),
        w.asIdeal ∣
            Ideal.span {((n : ℕ) : 𝓞 K)} →
          w ∈ S' := by
    intro w hwDvd
    exact
      mem_sUnitKummerNormSupport_of_asIdeal_dvd_natCast
        (K := K) n S hwDvd
  have hLarge :
      IdeleGroup.supportedAt
            (K := K) (S' : Set (HeightOneSpectrum (𝓞 K))) ⊔
          IdeleGroup.principalSubgroup K =
        ⊤ := by
    simpa only [S'] using
      supportedAt_sUnitKummerNormSupport_sup_principalSubgroup_eq_top
        (K := K) n S
  have hProduct :=
    card_sUnitPrincipalQuotient_mul_card_ideleClassQuotient_eq_power_two_totalPlaceCard
      (K := K) n hmu S' ∅ hDiv
      (by
        simpa only [Finset.coe_empty, Set.union_empty] using hLarge)
  rw [hDen,
    card_sUnit_nthPowerQuotient
      (K := K) (S' ∪ ∅) n hmu] at hProduct
  simp only [Finset.union_empty] at hProduct
  have hPower :
      (n : ℕ) ^ (2 * totalPlaceCard (K := K) S') =
        (n : ℕ) ^ totalPlaceCard (K := K) S' *
          (n : ℕ) ^ totalPlaceCard (K := K) S' := by
    rw [two_mul, pow_add]
  exact
    Nat.eq_of_mul_eq_mul_left
      (pow_pos n.pos (totalPlaceCard (K := K) S'))
      (hProduct.trans hPower)

/-- The power quotient on the chosen support has the same cardinality
as the degree of the full `S`-unit Kummer extension. -/
theorem
    card_ideleClassPowerLocalUnitQuotient_eq_finrank_fullSUnitKummerExtension
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let S' := sUnitKummerNormSupport (K := K) n S
    let E :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S'
    letI : FiniteDimensional K E :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n
        (by exact_mod_cast n.ne_zero) hmu S'
    Nat.card
        (IdeleClassPowerLocalUnitQuotient
          (K := K) n S' ∅) =
      Module.finrank K E := by
  classical
  dsimp only
  let S' := sUnitKummerNormSupport (K := K) n S
  let E :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K E :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  let : IsGalois K E :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  calc
    Nat.card
          (IdeleClassPowerLocalUnitQuotient
            (K := K) n S' ∅) =
        (n : ℕ) ^ totalPlaceCard (K := K) S' := by
      simpa only [S'] using
        card_ideleClassPowerLocalUnitQuotient_on_kummerNormSupport
          (K := K) n hmu S
    _ = Nat.card Gal(E/K) := by
      symm
      simpa only [E] using
        card_fullSUnitKummerExtension_galois
          (K := K) (Omega := Omega) n hnK hmu S'
    _ = Module.finrank K E :=
      IsGalois.card_aut_eq_finrank K E

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The complex-conjugation overfield at an infinite place

This module realizes the embedded field `L(i)` inside `ℂ`, constructs its
complex place, and identifies ambient complex conjugation on that field.
-/

open scoped Classical IsMulCommutative
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K]
    [Field L] [NumberField L] [Algebra K L]

variable
    [NumberField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance] GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfieldRationalAlgebra
omit [NumberField K] [FiniteDimensional K L] in
/-- Complex conjugation preserves the concrete overfield `L(i)` at a
ramified chosen place.  Preservation of the `L`-factor is the actual
local Artin value being a conjugation; preservation of the fourth-root
factor is intrinsic. -/
theorem infinitePlaceComplexificationOverfield_map_complexConjugation
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v).map
        (Complex.conjAe.restrictScalars ℚ).toAlgHom =
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v := by
  rw [infinitePlaceComplexificationOverfield,
    IntermediateField.map_sup,
    complexEmbeddingFieldRange_map_complexConjugation
      (K := K)
      (L := L)
      (φ :=
        InfinitePlace.embedding
          (chosenInfinitePlaceAbove (L := L) v))
      (σ :=
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (-1 : v.Completionˣ))
      (hσ :=
        chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
          (K := K) (L := L) v hRamified),
    complexFourthRootField_map_complexConjugation]

/-- Complex conjugation restricted to the actual overfield `L(i)`. -/
noncomputable def ramifiedInfinitePlaceOverfieldConjugation
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    infinitePlaceComplexificationOverfield
          (K := K) (L := L) v ≃ₐ[ℚ]
      infinitePlaceComplexificationOverfield
          (K := K) (L := L) v :=
  (IntermediateField.equivMap
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)
      (Complex.conjAe.restrictScalars ℚ).toAlgHom).trans
    (IntermediateField.equivOfEq
      (infinitePlaceComplexificationOverfield_map_complexConjugation
        (K := K) (L := L) v hRamified))

omit [NumberField K] [FiniteDimensional K L] in
/-- The restricted overfield automorphism acts by ambient complex
conjugation. -/
@[simp]
theorem ramifiedInfinitePlaceOverfieldConjugation_apply
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (z :
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :
    (ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified z : ℂ) =
      star (z : ℂ) := by
  rfl

omit [NumberField K] [FiniteDimensional K L] in
/-- The restricted overfield complex conjugation is an involution. -/
@[simp]
theorem ramifiedInfinitePlaceOverfieldConjugation_sq
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceOverfieldConjugation
          (K := K) (L := L) v hRamified *
        ramifiedInfinitePlaceOverfieldConjugation
          (K := K) (L := L) v hRamified =
      1 := by
  apply AlgEquiv.ext
  intro z
  apply Subtype.ext
  change
    (ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified
        (ramifiedInfinitePlaceOverfieldConjugation
          (K := K) (L := L) v hRamified z) : ℂ) =
      (z : ℂ)
  simp only [ramifiedInfinitePlaceOverfieldConjugation_apply,
    star_star]

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RamifiedOverextension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The quadratic overextension at a ramified real place

This module constructs the real fixed field of complex conjugation, the
quadratic overextension above it, and the faithful cyclotomic restriction.
-/

open scoped Classical IsMulCommutative
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance]
  infinitePlaceComplexificationOverfieldRationalAlgebra

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The base `K'` in the archimedean overextension: the fixed field
of complex conjugation in `L(i)`. -/
def ramifiedInfinitePlaceRealFixedField
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IntermediateField ℚ
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IntermediateField.fixedField
    (Subgroup.zpowers
      (ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified))

omit [FiniteDimensional K L] in
/-- Ambient complex conjugation on the overfield fixes the embedded base
field at a ramified real place. -/
theorem ramifiedInfinitePlaceOverfieldConjugation_fixes_base
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (x : K) :
    ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified
        (algebraMap K
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v) x) =
      algebraMap K
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) x := by
  apply Subtype.ext
  let w := chosenInfinitePlaceAbove (L := L) v
  let σ :=
    chosenInfinitePlaceArtinMonoidHom
      (K := K) (L := L) v
      (-1 : v.Completionˣ)
  have hσ :
      NumberField.ComplexEmbedding.IsConj
        (InfinitePlace.embedding w) σ :=
    chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
      (K := K) (L := L) v hRamified
  change
    star
        (InfinitePlace.embedding w
          (algebraMap K L x)) =
      InfinitePlace.embedding w
        (algebraMap K L x)
  calc
    star
        (InfinitePlace.embedding w
          (algebraMap K L x)) =
        InfinitePlace.embedding w
          (σ (algebraMap K L x)) :=
      (hσ.eq (algebraMap K L x)).symm
    _ =
        InfinitePlace.embedding w
          (algebraMap K L x) := by
      exact
        congrArg (InfinitePlace.embedding w)
          (σ.commutes x)

/-- The compatible embedding `K → K'` into the real fixed field. -/
noncomputable def ramifiedInfinitePlaceRealFixedFieldEmbedding
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    K →ₐ[ℚ]
      ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified :=
  (IsScalarTower.toAlgHom ℚ K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)).codRestrict
    (ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified).toSubalgebra
    (fun x => by
      apply
        (IntermediateField.mem_fixedField_iff _ _).2
      intro g hg
      have hc :
          ramifiedInfinitePlaceOverfieldConjugation
                (K := K) (L := L) v hRamified ∈
            MulAction.stabilizer
              ((infinitePlaceComplexificationOverfield
                  (K := K) (L := L) v) ≃ₐ[ℚ]
                infinitePlaceComplexificationOverfield
                  (K := K) (L := L) v)
              (algebraMap K
                (infinitePlaceComplexificationOverfield
                  (K := K) (L := L) v) x) := by
        exact
          MulAction.mem_stabilizer_iff.mpr
            (ramifiedInfinitePlaceOverfieldConjugation_fixes_base
              (K := K) (L := L) v hRamified x)
      exact
        MulAction.mem_stabilizer_iff.mp
          ((Subgroup.zpowers_le).2 hc hg))

omit [FiniteDimensional K L] in
/-- The fixed-field embedding agrees with the original base-field
algebra map after coercion to the overfield. -/
@[simp]
theorem ramifiedInfinitePlaceRealFixedFieldEmbedding_coe
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (x : K) :
    ((ramifiedInfinitePlaceRealFixedFieldEmbedding
        (K := K) (L := L) v hRamified x :
      ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) =
      algebraMap K
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) x := by
  calc
    ((ramifiedInfinitePlaceRealFixedFieldEmbedding
        (K := K) (L := L) v hRamified x :
      ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) =
        (IsScalarTower.toAlgHom ℚ K
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)) x := by
      exact
        AlgHom.coe_codRestrict
          (IsScalarTower.toAlgHom ℚ K
            (infinitePlaceComplexificationOverfield
              (K := K) (L := L) v))
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified).toSubalgebra _ x
    _ = algebraMap K
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) x :=
      IsScalarTower.toAlgHom_apply ℚ K
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) x

@[reducible]
noncomputable instance
    ramifiedInfinitePlaceRealFixedField_algebra
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Algebra K
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  (ramifiedInfinitePlaceRealFixedFieldEmbedding
    (K := K) (L := L) v hRamified).toRingHom.toAlgebra

instance ramifiedInfinitePlaceRealFixedField_ratScalarTower
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsScalarTower ℚ K
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  IsScalarTower.of_algHom
    (ramifiedInfinitePlaceRealFixedFieldEmbedding
      (K := K) (L := L) v hRamified)

instance ramifiedInfinitePlaceRealFixedField_scalarTower
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsScalarTower K
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IsScalarTower.of_algHom
    { (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified).val.toRingHom with
      commutes' := fun x =>
        ramifiedInfinitePlaceRealFixedFieldEmbedding_coe
          (K := K) (L := L) v hRamified x }

omit [NumberField K] [FiniteDimensional K L] in
theorem
    ramifiedInfinitePlaceRealFixedField_finiteDimensional
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    FiniteDimensional ℚ
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  FiniteDimensional.left ℚ
    (ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified)
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)

noncomputable instance ramifiedInfinitePlaceRealFixedField_numberField
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    NumberField
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  by
    let : FiniteDimensional ℚ
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified) :=
      ramifiedInfinitePlaceRealFixedField_finiteDimensional
        (K := K) (L := L) v hRamified
    exact
      NumberField.of_module_finite ℚ
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)

omit [NumberField K] [FiniteDimensional K L] in
theorem ramifiedInfinitePlaceOverextension_isGalois
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsGalois
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) := by
  unfold ramifiedInfinitePlaceRealFixedField
  exact
    IsGalois.of_fixed_field
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)
      (Subgroup.zpowers
        (ramifiedInfinitePlaceOverfieldConjugation
          (K := K) (L := L) v hRamified))

noncomputable instance
    ramifiedInfinitePlaceOverextension_isAbelianGalois
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsAbelianGalois
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) := by
  let : IsGalois
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
    ramifiedInfinitePlaceOverextension_isGalois
      (K := K) (L := L) v hRamified
  let H :=
    Subgroup.zpowers
      (ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified)
  let e :=
    IntermediateField.subgroupEquivAlgEquiv H
  let :
      IsCyclic
        Gal(
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v) /
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)) :=
    e.isCyclic.mp
      (Subgroup.isCyclic_zpowers
        (ramifiedInfinitePlaceOverfieldConjugation
          (K := K) (L := L) v hRamified))
  exact IsAbelianGalois.of_isCyclic _ _

/-- The distinguished nontrivial automorphism of the quadratic
overextension `L(i)/K'`, obtained from ambient complex conjugation. -/
noncomputable def ramifiedInfinitePlaceOverextensionConjugation
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal(
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) /
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)) :=
  IntermediateField.subgroupEquivAlgEquiv
    (Subgroup.zpowers
      (ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified))
    ⟨ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified,
      Subgroup.mem_zpowers
        (ramifiedInfinitePlaceOverfieldConjugation
          (K := K) (L := L) v hRamified)⟩

omit [NumberField K] [FiniteDimensional K L] in
/-- The distinguished overextension automorphism is the restriction
of ambient complex conjugation. -/
@[simp]
theorem ramifiedInfinitePlaceOverextensionConjugation_apply
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (z :
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :
    ramifiedInfinitePlaceOverextensionConjugation
        (K := K) (L := L) v hRamified z =
      ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified z := by
  rfl

omit [NumberField K] [FiniteDimensional K L] in
/-- Every automorphism of the overextension is either the identity or
the distinguished complex conjugation. -/
theorem ramifiedInfinitePlaceOverextension_eq_one_or_conjugation
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (σ :
      Gal(
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) /
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified))) :
    σ = 1 ∨
      σ =
        ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified := by
  let c :=
    ramifiedInfinitePlaceOverfieldConjugation
      (K := K) (L := L) v hRamified
  let H := Subgroup.zpowers c
  let e :=
    IntermediateField.subgroupEquivAlgEquiv H
  let cH : H :=
    ⟨c, Subgroup.mem_zpowers c⟩
  have hcSq : c ^ 2 = 1 :=
    (pow_two c).trans
      (ramifiedInfinitePlaceOverfieldConjugation_sq
        (K := K) (L := L) v hRamified)
  have hσCases :
      (e.symm σ).1 = 1 ∨
        (e.symm σ).1 = c := by
    obtain ⟨n, hσ⟩ :=
      Subgroup.mem_zpowers_iff.mp (e.symm σ).property
    have hσPower :
        (e.symm σ).1 = c ^ (n % (2 : ℤ)) :=
      hσ.symm.trans
        (zpow_eq_zpow_emod' n hcSq)
    rcases Int.emod_two_eq_zero_or_one n with hn | hn
    · left
      exact
        hσPower.trans
          ((congrArg (fun m : ℤ => c ^ m) hn).trans
            (zpow_zero c))
    · right
      exact
        hσPower.trans
          ((congrArg (fun m : ℤ => c ^ m) hn).trans
            (zpow_one c))
  rcases hσCases with hσ | hσ
  · left
    have hσSub : e.symm σ = 1 :=
      Subtype.ext hσ
    exact
      e.symm.injective
        (hσSub.trans
          (map_one e.symm).symm)
  · right
    have hσSub : e.symm σ = cH :=
      Subtype.ext hσ
    change σ = e cH
    exact
      (e.apply_symm_apply σ).symm.trans
        (congrArg e hσSub)

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceCompatibility
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Infinite-place local-global Artin compatibility

This module compares the real fixed place and the original ramified place,
then transports the special overextension computation through global
norm-residue naturality.
-/

open scoped Classical IsMulCommutative
open NumberField
open IdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

local instance
    infinitePlaceCompatibilityIdeleClassGroupIsMulCommutative_r76684b_1
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
/-- The chosen local Artin value at negative one at `v`. -/
noncomputable def ramifiedInfinitePlaceLocalArtinNegOneValue
    (v : InfinitePlace K) :
    Gal(L / K) :=
  chosenInfinitePlaceArtinMonoidHom
    (K := K) (L := L) v (-1 : v.Completionˣ)

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfiniteLocalGlobalArtinCompatibility
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Archimedean local-global compatibility of Artin homomorphisms

This file compares the actual Artin homomorphism at an infinite place
with the global norm-residue homomorphism on idele classes.  The
one-place norm statements are proved from genuine relative ideles
supported at the chosen archimedean place.
-/

open scoped NumberField
open NumberField
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

omit [FiniteDimensional K L] in
/-- Triviality of the actual chosen infinite-place Artin symbol is
equivalent to membership in the corresponding determinant-norm
subgroup. -/
@[simp]
theorem chosenInfinitePlaceArtinMonoidHom_eq_one_iff_infiniteTensorNorm
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v x = 1 ↔
      x ∈ infiniteTensorNormSubgroup
        (K := K) (L := L) v := by
  change
    x ∈ (chosenInfinitePlaceArtinMonoidHom
      (K := K) (L := L) v).ker ↔ _
  rw [chosenInfinitePlaceArtinMonoidHom_ker
    (K := K) (L := L) v]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_Factorization
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Factorization of the global Artin map through local Artin maps

This module completes the auxiliary-field argument, factors the global
norm-residue map through each local Artin quotient, and proves the
finite-place local-global compatibility theorem.
-/

open scoped IsMulCommutative NumberField
open NumberField
open AlgebraicNumberTheory.Valuations
open HilbertRamification

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open CyclicCohomology
open KummerTheory

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

omit [NumberField L] in
/-- Triviality of the actual chosen finite-place Artin symbol is
equivalent to membership in the actual chosen local norm subgroup. -/
@[simp]
theorem chosenFinitePlaceArtinMonoidHom_eq_one_iff_chosenLocalNorm
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x = 1 ↔
      x ∈ chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  change
    x ∈ (chosenFinitePlaceArtinMonoidHom
      (K := K) (L := L) v).ker ↔ _
  rw [chosenFinitePlaceArtinMonoidHom_ker
    (K := K) (L := L) v]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ArithmeticNormalization
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Arithmetic normalization of global reciprocity

The valuation used by the local class-formation implementation is the
logarithm of the multiplicative absolute value.  Consequently its
distinguished element of value `1` is the inverse of a DVR uniformizer.
The resulting field-facing reciprocity map sends a usual uniformizer to
geometric Frobenius.

The arithmetic global norm-residue symbol uses the opposite
normalization: a DVR uniformizer maps to arithmetic Frobenius and a
ramified cyclotomic unit `u` acts by `u⁻¹`.  For an abelian target the two
normalizations differ by the canonical inversion automorphism.  This file
records that normalization explicitly, including its topology and its
local-global compatibility.  Thus no sign convention is hidden in an
unbundled equality.
-/

open scoped IsMulCommutative NumberField
open NumberField IsDedekindDomain
open IdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

section FiniteAbelian

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The chosen infinite-place Artin homomorphism in arithmetic
normalization. -/
noncomputable def arithmeticChosenInfinitePlaceArtinMonoidHom
    (v : InfinitePlace K) :
    v.Completionˣ →* Gal(L / K) :=
  (MulEquiv.inv (Gal(L / K))).toMonoidHom.comp
    (chosenInfinitePlaceArtinMonoidHom
      (K := K) (L := L) v)

end FiniteAbelian

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_UnramifiedNormalization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramified normalization of the chosen finite-place Artin map

The chosen order-one input has normalized local valuation `-1` in the
geometric finite-place construction. Its local Artin image is therefore
inverse arithmetic Frobenius in the actual chosen completion.
-/

open scoped Classical NumberField ValuativeRel
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]

/-- Arithmetic Frobenius of the actual chosen unramified local extension. -/
noncomputable def chosenFinitePlaceLocalArithmeticFrobenius
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v]
      ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v := by
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  letI : IsGalois C E :=
    chosenFinitePlaceLocalizedIsGalois (K := K) (L := L) v
  letI : Valuation.HasExtension
      (ValuativeRel.valuation C) (ValuativeRel.valuation E) :=
    chosenFinitePlaceLocalizedValuationHasExtension (K := K) (L := L) v
  letI : IsIntegralClosure 𝒪[E] 𝒪[C] E :=
    chosenFinitePlaceLocalizedIsIntegralClosure (K := K) (L := L) v
  letI : Module.Finite 𝒪[C] 𝒪[E] :=
    chosenFinitePlaceLocalizedIntegerModuleFinite (K := K) (L := L) v
  letI : IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      C E := hunram
  exact arithmeticFrobeniusOfUnramifiedValuation C E

end Reciprocity
end GlobalClassFieldTheory
end
end


