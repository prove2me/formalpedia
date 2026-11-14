-- Prove2me | Definitions.Def_OAIQ244Duke073
-- name    : OAIQ244Duke073
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T23:01:16.696427+00:00
-- url     : https://prove2.me/theorems/eb5e2e4d-e2fc-4a62-94ca-33afc96237f8
-- title:
--   Definitions bundle OAIQ244Duke073 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 3 definitions, 2 instances and 24 theorems. The definitions and types are `GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr`, `GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr`, `GlobalClassFieldTheory.Reciprocity.automorphismCyclicFixedPlace`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_ClassGroup_NormalClosureNorm`, `AlgebraicNumberTheory_Idele_ClassGroup_TowerBaseChange`, `AlgebraicNumberTheory_Idele_Extension_OnePlaceBaseNorm`, `GlobalClassFieldTheory_GlobalClassFields_BigHilbertClassFieldNaturality`, `GlobalClassFieldTheory_GlobalClassFields_PowerCongruenceCore`, `GlobalClassFieldTheory_GlobalClassFields_SmallHilbertClassFieldNaturality`, `GlobalClassFieldTheory_GlobalClassFields_SmallHilbertNormCharacterization`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitCore`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_SeparableClosurePadicLift`, `KummerTheory_Concrete_SUnitKummerUnramified`, `LocalClassFieldTheory_Finite_Existence_UnramifiedNormSubgroup`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke062`, `OAIQ244Duke064`, `OAIQ244Duke065`, `OAIQ244Duke066`, `OAIQ244Duke067` and `OAIQ244Duke068` of this split.
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
import Definitions.Def_OAIQ244Duke062
import Definitions.Def_OAIQ244Duke064
import Definitions.Def_OAIQ244Duke065
import Definitions.Def_OAIQ244Duke066
import Definitions.Def_OAIQ244Duke067
import Definitions.Def_OAIQ244Duke068

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_TowerBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The fixed-bottom tower model and the actual intermediate-field model

For a tower `K ⊂ M ⊂ L`, `IdeleClassTower` presents the ideles of `L`
as units of `(𝔸_K ⊗[K] M) ⊗[M] L`.  Here we compare that presentation
with the actual relative idele group `𝔸_M ⊗[M] L`, by passing through
the ordinary ideles of `L`.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u

variable
    (K M L : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]

section IdeleComparison

attribute [local instance] towerBaseChange_towerRelativeIdeleGroupIsMulCommutative
attribute [local instance] towerBaseChange_relativeIdeleClassGroupIsMulCommutative
attribute [local instance] towerBaseChange_ideleClassGroupIsMulCommutative
/-- The ring-level tower coherence identifies the direct
tower-to-actual comparison with the comparison through ordinary ideles. -/
theorem towerRelativeIdeleBaseChangeMulEquiv_eq_viaOrdinary
    (a : TowerRelativeIdeleGroup K M L) :
    towerRelativeIdeleBaseChangeMulEquiv K M L a =
      towerRelativeIdeleViaOrdinaryMulEquiv K M L a := by
  apply
    (relativeIdeleBaseChangeMulEquiv
      (K := M) (L := L)).injective
  rw [towerRelativeIdeleViaOrdinaryMulEquiv_apply,
    (relativeIdeleBaseChangeMulEquiv
      (K := M) (L := L)).apply_symm_apply]
  apply (IdeleGroup.equivAdeleRingUnits (K := L)).injective
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits
      (K := M) (L := L),
    relativeIdeleBaseChangeMulEquiv_eq_ringUnits
      (K := K) (L := L)]
  apply Units.ext
  exact
    relativeAdeleBaseChangeRingEquiv_tower
      K M L (a : TowerRelativeAdeleRing K M L)

/-- Scalar extension from the tower presentation to ordinary ideles is
the same along the direct and intermediate-field routes. -/
theorem relativeIdeleBaseChangeMulEquiv_tower
    (a : TowerRelativeIdeleGroup K M L) :
    relativeIdeleBaseChangeMulEquiv
        (K := M) (L := L)
        (towerRelativeIdeleBaseChangeMulEquiv K M L a) =
      relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)
        (towerRelativeIdeleEquiv K M L a) := by
  rw [towerRelativeIdeleBaseChangeMulEquiv_eq_viaOrdinary,
    towerRelativeIdeleViaOrdinaryMulEquiv_apply,
    (relativeIdeleBaseChangeMulEquiv
      (K := M) (L := L)).apply_symm_apply]

/-- Scalar extension from a fixed-bottom tower class group to the
ordinary top-field idele class group is independent of the intermediate
presentation. -/
theorem relativeIdeleClassBaseChangeMulEquiv_tower
    (c : RelativeIdeleGroup.ClassGroup K L) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := M) (L := L)
        (towerRelativeIdeleClassBaseChangeMulEquiv K M L
          ((TowerRelativeIdeleGroup.classGroupEquiv
            K M L).symm c)) =
      relativeIdeleClassBaseChangeMulEquiv
        (K := K) (L := L) c := by
  obtain ⟨d, hd⟩ :=
    (TowerRelativeIdeleGroup.classGroupEquiv
      K M L).surjective c
  rw [← hd]
  rw [(TowerRelativeIdeleGroup.classGroupEquiv
    K M L).symm_apply_apply]
  refine QuotientGroup.induction_on d ?_
  intro a
  change
    QuotientGroup.mk' (IdeleGroup.principalSubgroup L)
        (relativeIdeleBaseChangeMulEquiv
          (K := M) (L := L)
          (towerRelativeIdeleBaseChangeMulEquiv K M L a)) =
      QuotientGroup.mk' (IdeleGroup.principalSubgroup L)
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L)
          (towerRelativeIdeleEquiv K M L a))
  exact
    congrArg
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L))
      (relativeIdeleBaseChangeMulEquiv_tower K M L a)

end IdeleComparison

section OrdinaryNormTower

attribute [local instance] towerBaseChange_towerRelativeIdeleGroupIsMulCommutative
attribute [local instance] towerBaseChange_relativeIdeleClassGroupIsMulCommutative
attribute [local instance] towerBaseChange_ideleClassGroupIsMulCommutative
/-- Ordinary idele-class norms are pointwise transitive in an arbitrary
finite tower of number fields.  This is determinant-norm transitivity,
transported through the actual relative-idele presentations over the
bottom and intermediate fields. -/
theorem ordinaryIdeleClassNorm_tower
    (c : IdeleClassGroup L) :
    _root_.ideleClassNorm K M
        (_root_.ideleClassNorm M L c) =
      _root_.ideleClassNorm K L c := by
  let d : RelativeIdeleGroup.ClassGroup K L :=
    (relativeIdeleClassBaseChangeMulEquiv
      (K := K) (L := L)).symm c
  let t : TowerRelativeIdeleGroup.ClassGroup K M L :=
    (TowerRelativeIdeleGroup.classGroupEquiv
      K M L).symm d
  have htop :
      relativeIdeleClassBaseChangeMulEquiv
          (K := M) (L := L)
          (towerRelativeIdeleClassBaseChangeMulEquiv
            K M L t) =
        c := by
    calc
      relativeIdeleClassBaseChangeMulEquiv
          (K := M) (L := L)
          (towerRelativeIdeleClassBaseChangeMulEquiv
            K M L t) =
          relativeIdeleClassBaseChangeMulEquiv
            (K := K) (L := L) d := by
        change
          relativeIdeleClassBaseChangeMulEquiv
              (K := M) (L := L)
              (towerRelativeIdeleClassBaseChangeMulEquiv K M L
                ((TowerRelativeIdeleGroup.classGroupEquiv
                  K M L).symm d)) =
            relativeIdeleClassBaseChangeMulEquiv
              (K := K) (L := L) d
        exact relativeIdeleClassBaseChangeMulEquiv_tower K M L d
      _ = c := by
        exact
          (relativeIdeleClassBaseChangeMulEquiv
            (K := K) (L := L)).apply_symm_apply c
  calc
    _root_.ideleClassNorm K M
        (_root_.ideleClassNorm M L c) =
      _root_.ideleClassNorm K M
        (_root_.ideleClassNorm M L
          (relativeIdeleClassBaseChangeMulEquiv
            (K := M) (L := L)
            (towerRelativeIdeleClassBaseChangeMulEquiv
              K M L t))) := by
                rw [htop]
    _ = _root_.ideleClassNorm K M
        (RelativeIdeleGroup.classNorm M L
          (towerRelativeIdeleClassBaseChangeMulEquiv
            K M L t)) := by
      exact congrArg
        (_root_.ideleClassNorm K M)
        (ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
          (K := M) (L := L)
          (towerRelativeIdeleClassBaseChangeMulEquiv
            K M L t))
    _ = _root_.ideleClassNorm K M
        (relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M)
          (TowerRelativeIdeleGroup.classNorm K M L t)) := by
              rw [
                towerRelativeIdeleClassBaseChangeMulEquiv_classNorm]
    _ = RelativeIdeleGroup.classNorm K M
        (TowerRelativeIdeleGroup.classNorm K M L t) := by
      exact
        ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
          (K := K) (L := M)
          (TowerRelativeIdeleGroup.classNorm K M L t)
    _ = towerCompositeClassNorm K M L t := rfl
    _ = RelativeIdeleGroup.classNorm K L
        (TowerRelativeIdeleGroup.classGroupEquiv K M L t) :=
      towerCompositeClassNorm_eq_ideleClassNorm K M L t
    _ = RelativeIdeleGroup.classNorm K L d := by
      exact congrArg
        (RelativeIdeleGroup.classNorm K L)
        ((TowerRelativeIdeleGroup.classGroupEquiv
          K M L).apply_symm_apply d)
    _ = _root_.ideleClassNorm K L
        (relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L) d) := by
      exact
        (ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
          (K := K) (L := L) d).symm
    _ = _root_.ideleClassNorm K L c := by
      exact congrArg
        (_root_.ideleClassNorm K L)
        ((relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L)).apply_symm_apply c)

/-- In an arbitrary finite tower of number fields, every ordinary
idele-class norm from the top field is already a norm from the
intermediate field.  No normality hypothesis is needed: this is
determinant-norm transitivity transported from the fixed-bottom tower
presentation to the ordinary idele class groups. -/
theorem ordinaryIdeleClassNorm_range_le_of_tower :
    (_root_.ideleClassNorm K L).range ≤
      (_root_.ideleClassNorm K M).range := by
  rw [
    ordinaryIdeleClassNorm_range_eq_relative
      (K := K) (L := L),
    ordinaryIdeleClassNorm_range_eq_relative
      (K := K) (L := M),
    ← towerCompositeClassNorm_range_eq K M L]
  rintro _ ⟨c, rfl⟩
  exact
    ⟨TowerRelativeIdeleGroup.classNorm K M L c, rfl⟩

end OrdinaryNormTower
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_NormalClosureNorm
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional_over_extension _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Idèle-class norms from a finite normal closure

The distinguished copy of a finite extension inside its normal closure
is an intermediate field.  Norm transitivity therefore puts every norm
from the normal closure inside the norm subgroup of that copy.  Transport
across the canonical algebra equivalence identifies the latter subgroup
with the norm subgroup of the original extension.
-/

open scoped NumberField
open NumberField

noncomputable section

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Every idèle-class norm from the finite normal closure of `L / K` is
already an idèle-class norm from `L / K`.  This supplies a genuine
finite Galois norm neighbourhood inside the norm subgroup of an
arbitrary finite extension. -/
theorem finiteNormalClosure_ideleClassNorm_range_le_source :
    (_root_.ideleClassNorm K (finiteNormalClosure K L)).range ≤
      (_root_.ideleClassNorm K L).range := by
  let N := finiteNormalClosure K L
  let : Algebra (finiteNormalClosureOriginalField K L) N :=
    (finiteNormalClosureOriginalField K L).val.toRingHom.toAlgebra
  let : IsScalarTower K (finiteNormalClosureOriginalField K L) N :=
    by infer_instance
  let : FiniteDimensional (finiteNormalClosureOriginalField K L) N :=
    FiniteDimensional.right K (finiteNormalClosureOriginalField K L) N
  let : IsMulCommutative
      (RelativeIdeleGroup K
        (finiteNormalClosureOriginalField K L)) :=
    ⟨⟨fun a b => mul_comm a b⟩⟩
  let : Group
      (RelativeIdeleGroup.ClassGroup K
        (finiteNormalClosureOriginalField K L)) :=
    QuotientGroup.Quotient.group
      (RelativeIdeleGroup.principalSubgroup K
        (finiteNormalClosureOriginalField K L))
  calc
    (_root_.ideleClassNorm K N).range ≤
        (_root_.ideleClassNorm K (finiteNormalClosureOriginalField K L)).range :=
      ordinaryIdeleClassNorm_range_le_of_tower
        (K := K) (M := finiteNormalClosureOriginalField K L) (L := N)
    _ = (RelativeIdeleGroup.classNorm K (finiteNormalClosureOriginalField K L)).range :=
      ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := finiteNormalClosureOriginalField K L)
    _ = (RelativeIdeleGroup.classNorm K L).range :=
      (ideleClassNorm_range_algEquiv
        (K := K) (L := L)
        (M := finiteNormalClosureOriginalField K L)
        (finiteNormalClosureOriginalFieldEquiv K L) :
          (RelativeIdeleGroup.classNorm K
            (finiteNormalClosureOriginalField K L)).range =
            (RelativeIdeleGroup.classNorm K L).range)
    _ = (_root_.ideleClassNorm K L).range :=
      (ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := L)).symm

end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_OnePlaceBaseNorm
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceBaseUnitExtension_neg_one _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.idealNormExponentMap_apply _root_.RayClass.idealNormLiftedModulusExponent_eq_zero_of_not_mem _root_.RayClass.mem_idealNormLiftedModulus_support_iff _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_mk _root_.ideleClassCongr_refl _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.mem_finitePlaceDecompositionGroup_iff _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms of base units supported at one finite place

For a finite place `v` of an extension field, embed a unit of the
completion at the place below `v` into the completion at `v`, and
support it only at `v`.  Its ordinary idele norm is supported only at
the place below `v`; the surviving component is the corresponding
local-degree power.
-/

open scoped BigOperators NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- The idele norm of a base-completion unit supported at one extension
place is the corresponding local-degree power supported at the place
below it. -/
theorem norm_finitePlaceIdele_finitePlaceBaseUnitExtension
    (v : HeightOneSpectrum (𝓞 L))
    (x :
      ((_root_.finitePlaceBelow (K := K) v).adicCompletion K)ˣ) :
    norm K L
        (finitePlaceIdele v
          (finitePlaceBaseUnitExtension
            (K := K) (L := L) v x)) =
      finitePlaceIdele
        (_root_.finitePlaceBelow (K := K) v)
        (x ^ finitePlaceCompletionDegree
          (K := K) (L := L) v) := by
  classical
  let q := _root_.finitePlaceBelow (K := K) v
  let W₀ :
      {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = q} :=
    ⟨v, rfl⟩
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change
      infiniteComponent w
          (norm K L
            (finitePlaceIdele v
              (finitePlaceBaseUnitExtension
                (K := K) (L := L) v x))) =
        infiniteComponent w
          (finitePlaceIdele q
            (x ^ finitePlaceCompletionDegree
              (K := K) (L := L) v))
    rw [infiniteComponent_norm_eq_prod]
    rw [finitePlaceIdele_infiniteComponent]
    apply Finset.prod_eq_one
    intro W _
    rw [finitePlaceIdele_infiniteComponent]
    exact map_one _
  · apply Subtype.ext
    funext r
    change
      finiteComponent r
          (norm K L
            (finitePlaceIdele v
              (finitePlaceBaseUnitExtension
                (K := K) (L := L) v x))) =
        finiteComponent r
          (finitePlaceIdele q
            (x ^ finitePlaceCompletionDegree
              (K := K) (L := L) v))
    by_cases hr : r = q
    · subst r
      rw [finiteComponent_norm_eq_prod,
        finitePlaceIdele_finiteComponent_same]
      rw [Finset.prod_eq_single W₀]
      · rw [finitePlaceIdele_finiteComponent_same]
        let :
            Algebra (q.adicCompletion K) (v.adicCompletion L) :=
          (finitePlaceAdicCompletionMap K L q W₀).toAlgebra
        let : Module.Finite (q.adicCompletion K) (v.adicCompletion L) :=
          finitePlaceAdicCompletionMap_moduleFinite K L q W₀
        have hmap :
            algebraMap (q.adicCompletion K) (v.adicCompletion L) =
              finitePlaceAdicCompletionMap K L q W₀ :=
          RingHom.algebraMap_toAlgebra _
        change
          LocalFieldTheory.normUnits
              (q.adicCompletion K) (v.adicCompletion L)
              (Units.map
                (finitePlaceAdicCompletionMap K L q W₀).toMonoidHom x) =
            x ^ Module.finrank (q.adicCompletion K) (v.adicCompletion L)
        rw [← hmap]
        simpa [
          LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits,
          MonoidHom.id_apply] using
          (LocalFieldTheory.IsNonarchimedeanLocalField.normUnits_algebraMap_base
            (K := q.adicCompletion K) (L := v.adicCompletion L) x)
      · intro W _ hW
        have hWv : W.1 ≠ v := by
          intro h
          apply hW
          exact Subtype.ext h
        rw [
          finitePlaceIdele_finiteComponent_of_ne
            v W.1
            (finitePlaceBaseUnitExtension
              (K := K) (L := L) v x)
            hWv,
          map_one]
      · simp
    · rw [
        finiteComponent_norm_eq_prod,
        finitePlaceIdele_finiteComponent_of_ne
          q r
          (x ^ finitePlaceCompletionDegree
            (K := K) (L := L) v)
          hr]
      apply Finset.prod_eq_one
      intro W _
      have hWv : W.1 ≠ v := by
        intro h
        apply hr
        calc
          r = _root_.finitePlaceBelow (K := K) W.1 :=
            W.2.symm
          _ = q := by rw [h]
      rw [
        finitePlaceIdele_finiteComponent_of_ne
          v W.1
          (finitePlaceBaseUnitExtension
            (K := K) (L := L) v x)
          hWv,
        map_one]

omit [FiniteDimensional K L] in
/-- The ordinary idele norm of an arbitrary unit supported at one
upper finite place is supported at the place below, with surviving
component equal to the genuine completed local norm. -/
theorem norm_finitePlaceIdele_eq_finitePlaceIdele_normUnits
    (v : HeightOneSpectrum (𝓞 K))
    (W :
      {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v})
    (y : (W.1.adicCompletion L)ˣ) :
    letI :
        Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v W).toAlgebra
    norm K L (finitePlaceIdele W.1 y) =
      finitePlaceIdele v
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.1.adicCompletion L) y) := by
  classical
  let :
      Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L v W).toAlgebra
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change
      infiniteComponent w
          (norm K L (finitePlaceIdele W.1 y)) =
        infiniteComponent w
          (finitePlaceIdele v
            (LocalFieldTheory.normUnits
              (v.adicCompletion K) (W.1.adicCompletion L) y))
    rw [infiniteComponent_norm_eq_prod]
    rw [finitePlaceIdele_infiniteComponent]
    apply Finset.prod_eq_one
    intro W' _
    rw [finitePlaceIdele_infiniteComponent]
    exact map_one _
  · apply Subtype.ext
    funext r
    change
      finiteComponent r
          (norm K L (finitePlaceIdele W.1 y)) =
        finiteComponent r
          (finitePlaceIdele v
            (LocalFieldTheory.normUnits
              (v.adicCompletion K) (W.1.adicCompletion L) y))
    by_cases hr : r = v
    · subst r
      rw [finiteComponent_norm_eq_prod,
        finitePlaceIdele_finiteComponent_same]
      rw [Finset.prod_eq_single W]
      · rw [finitePlaceIdele_finiteComponent_same]
      · intro W' _ hW'
        have hne : W'.1 ≠ W.1 := by
          intro h
          apply hW'
          exact Subtype.ext h
        rw [
          finitePlaceIdele_finiteComponent_of_ne W.1 W'.1 y hne,
          map_one]
      · simp
    · rw [
        finiteComponent_norm_eq_prod,
        finitePlaceIdele_finiteComponent_of_ne
          v r
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.1.adicCompletion L) y)
          hr]
      apply Finset.prod_eq_one
      intro W' _
      have hne : W'.1 ≠ W.1 := by
        intro h
        apply hr
        calc
          r = _root_.finitePlaceBelow (K := K) W'.1 :=
            W'.2.symm
          _ = v := by rw [h, W.2]
      rw [
        finitePlaceIdele_finiteComponent_of_ne W.1 W'.1 y hne,
        map_one]

omit [FiniteDimensional K L] in
/-- Passing the preceding one-place norm identity to ordinary idele
classes gives the norm--restriction input used in the global
reciprocity square. -/
theorem ideleClassNorm_finitePlaceIdeleClass_eq_normUnits
    (v : HeightOneSpectrum (𝓞 K))
    (W :
      {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v})
    (y : (W.1.adicCompletion L)ˣ) :
    letI :
        Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v W).toAlgebra
    _root_.ideleClassNorm K L
        (finitePlaceIdeleClass W.1 y) =
      finitePlaceIdeleClass v
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.1.adicCompletion L) y) := by
  classical
  let :
      Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L v W).toAlgebra
  rw [
    finitePlaceIdeleClass,
    MonoidHom.coe_comp,
    Function.comp_apply,
    _root_.ideleClassNorm_mk,
    norm_finitePlaceIdele_eq_finitePlaceIdele_normUnits]
  rfl

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_BigHilbertClassFieldNaturality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.IdeleGroup.idealClass_classRepresentative _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_refl _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Naturality of the big Hilbert class field

An equivalence of number fields preserves both finite integrality and
positivity at the real infinite places.  Consequently the actual
idele-class transport carries the big-Hilbert norm subgroup exactly onto
the corresponding subgroup of the target field.  This gives canonical
transport on the big-Hilbert reciprocity quotient and on the narrow class
group, with formulas on genuine idele representatives.
-/

open scoped NumberField NumberField.LiesOver Classical TensorProduct

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M]

theorem
    relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr_infiniteComponent_tmul
    (e : K ≃ₐ[ℚ] M)
    (b : NumberField.AdeleRing (𝓞 ℚ) ℚ)
    (x : K)
    (W : InfinitePlace M) :
    (relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M) (b ⊗ₜ[ℚ] e x)).1 W =
      infinitePlaceCompletionCongrHom e W
        ((relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) (b ⊗ₜ[ℚ] x)).1
            (W.comap e.toRingHom)) := by
  let : Algebra K M :=
    e.toRingHom.toAlgebra
  let v : InfinitePlace K :=
    W.comap e.toRingHom
  let : W.1.LiesOver v.1 :=
    ⟨rfl⟩
  change
    (relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M) (b ⊗ₜ[ℚ] e x)).1 W =
      NumberField.LiesOver.completionMap
        (v := v) (w := W)
        ((relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) (b ⊗ₜ[ℚ] x)).1 v)
  let qv :=
    infinitePlaceBelow (K := ℚ) v
  let qW :=
    infinitePlaceBelow (K := ℚ) W
  have hW :
      infinitePlaceBelow (K := K) W = v :=
    rfl
  have hq : qv = qW := by
    dsimp only [qv, qW]
    rw [← hW]
    exact
      infinitePlaceBelow_infinitePlaceBelow
        (K := ℚ) (M := K) (L := M) W
  let : v.1.LiesOver qv.1 :=
    ⟨rfl⟩
  let : W.1.LiesOver qW.1 :=
    ⟨rfl⟩
  let : W.1.LiesOver qv.1 :=
    ⟨congrArg (fun q : InfinitePlace ℚ => q.1) hq.symm⟩
  have hxMap :
      NumberField.LiesOver.completionMap
          (v := v) (w := W)
          (algebraMap K v.Completion x) =
        algebraMap M W.Completion (e x) := by
    simpa only [infinitePlaceCompletionCongrHom] using
      infinitePlaceCompletionCongrHom_algebraMap e W x
  have hcomponent
      (qv' : InfinitePlace ℚ)
      (h : qv' = qW)
      [v.1.LiesOver qv'.1] :
      NumberField.LiesOver.completionMap
            (v := qW) (w := W) (b.1 qW) *
          algebraMap M W.Completion (e x) =
        NumberField.LiesOver.completionMap
            (v := v) (w := W)
            (NumberField.LiesOver.completionMap
                (v := qv') (w := v) (b.1 qv') *
              algebraMap K v.Completion x) := by
    subst qv'
    have hcomp :
        NumberField.LiesOver.completionMap
            (v := v) (w := W)
            (NumberField.LiesOver.completionMap
              (v := qW) (w := v) (b.1 qW)) =
          NumberField.LiesOver.completionMap
            (v := qW) (w := W) (b.1 qW) := by
      convert
        (infinitePlaceCompletionMap_comp_apply
          (K := ℚ) (M := K) (L := M) W (b.1 qW)) using 1
      all_goals try with_reducible_and_instances rfl
      rfl
    rw [map_mul, hcomp, hxMap]
  rw [relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul,
    relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul]
  exact hcomponent qv hq

theorem adeleCongr_infiniteComponent
    (e : K ≃ₐ[ℚ] M)
    (a : NumberField.AdeleRing (𝓞 K) K)
    (W : InfinitePlace M) :
    (adeleCongr e a).1 W =
      infinitePlaceCompletionCongrHom e W
        (a.1 (W.comap e.toRingHom)) := by
  let v : InfinitePlace K :=
    W.comap e.toRingHom
  let componentK :=
    (infiniteAdeleComponentAlgHom v).toAddMonoidHom
  let componentM :=
    (infiniteAdeleComponentAlgHom W).toAddMonoidHom
  change
    componentM (adeleCongr e a) =
      infinitePlaceCompletionCongrHom e W (componentK a)
  let z :=
    (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).symm a
  have ha :
      relativeAdeleBaseChangeRingEquiv
          (K := ℚ) (L := K) z = a :=
    (relativeAdeleBaseChangeRingEquiv
      (K := ℚ) (L := K)).apply_symm_apply a
  have htransport :
      componentM
          (relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := M)
            (relativeAdeleCongr (K := ℚ) e z)) =
        componentM
          (adeleCongr e
            (relativeAdeleBaseChangeRingEquiv
              (K := ℚ) (L := K) z)) :=
    congrArg componentM
      (relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr e z)
  rw [← ha, ← htransport]
  induction z using OAI.tensorInductionOn with
  | add x y hx hy =>
      simpa only [map_add, Prod.fst_add, Pi.add_apply] using
        congrArg₂ (· + ·) hx hy
  | tmul b x =>
      exact
        relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr_infiniteComponent_tmul
          e b x W

theorem ideleCongr_infiniteComponent
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K)
    (W : InfinitePlace M) :
    IdeleGroup.infiniteComponent W (ideleCongr e a) =
      Units.map
        (infinitePlaceCompletionCongrHom e W).toMonoidHom
        (IdeleGroup.infiniteComponent
          (W.comap e.toRingHom) a) := by
  apply Units.ext
  exact
    adeleCongr_infiniteComponent e
      (((IdeleGroup.equivAdeleRingUnits
        (K := K) a :
          (NumberField.AdeleRing (𝓞 K) K)ˣ) :
        NumberField.AdeleRing (𝓞 K) K)) W

theorem ideleCongr_mem_infiniteCongruenceSubgroup_iff
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K) :
    (ideleCongr e a).1 ∈
        RayClass.narrowInfiniteCongruenceSubgroup (K := M) ↔
      a.1 ∈
        RayClass.narrowInfiniteCongruenceSubgroup (K := K) := by
  rw [RayClass.mem_narrowInfiniteCongruenceSubgroup_iff,
    RayClass.mem_narrowInfiniteCongruenceSubgroup_iff]
  constructor
  · intro h v
    let W : InfinitePlace M :=
      v.comap e.symm.toRingHom
    have hcomap :
        W.comap e.toRingHom = v := by
      change
        (v.comap e.symm.toRingHom).comap e.toRingHom = v
      rw [← InfinitePlace.comap_comp]
      convert InfinitePlace.comap_id v using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      change v.1 (e.symm (e x)) = v.1 x
      exact congrArg v.1 (e.symm_apply_apply x)
    have hW :
        IdeleGroup.infiniteComponent W (ideleCongr e a) ∈
          RayClass.infinitePositiveSubgroup W := by
      simpa only [IdeleGroup.infiniteComponent_apply] using h W
    rw [ideleCongr_infiniteComponent] at hW
    have hv :=
      (infinitePlaceCompletionCongrHom_mem_infinitePositiveSubgroup_iff
        e W
        (IdeleGroup.infiniteComponent
          (W.comap e.toRingHom) a)).1 hW
    rw [hcomap] at hv
    simpa only [IdeleGroup.infiniteComponent_apply] using hv
  · intro h W
    have hW :
        IdeleGroup.infiniteComponent W (ideleCongr e a) ∈
          RayClass.infinitePositiveSubgroup W := by
      rw [ideleCongr_infiniteComponent]
      apply
        (infinitePlaceCompletionCongrHom_mem_infinitePositiveSubgroup_iff
          e W
          (IdeleGroup.infiniteComponent
            (W.comap e.toRingHom) a)).2
      simpa only [IdeleGroup.infiniteComponent_apply] using
        h (W.comap e.toRingHom)
    simpa only [IdeleGroup.infiniteComponent_apply] using hW

theorem ideleCongr_mem_ideleCongruenceSubgroup_zero_iff
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K) :
    ideleCongr e a ∈
        (RayClass.Modulus.narrowOfFinite
          (0 : RayClass.FiniteModulus M)).ideleCongruenceSubgroup ↔
      a ∈
        (RayClass.Modulus.narrowOfFinite
          (0 : RayClass.FiniteModulus K)).ideleCongruenceSubgroup := by
  have hfinite :=
    ideleCongr_mem_integralAtFinitePlaces_iff e a
  change
    (ideleCongr e a).2 ∈
          FiniteIdeleGroup.integralSubgroup (K := M) ↔
      a.2 ∈
        FiniteIdeleGroup.integralSubgroup (K := K) at hfinite
  have hfiniteZero :
      (ideleCongr e a).2 ∈
            RayClass.finiteCongruenceSubgroup
              (0 : RayClass.FiniteModulus M) ↔
        a.2 ∈
          RayClass.finiteCongruenceSubgroup
            (0 : RayClass.FiniteModulus K) := by
    simpa only [RayClass.finiteCongruenceSubgroup_zero] using
      hfinite
  rw [RayClass.Modulus.ideleCongruenceSubgroup_narrowOfFinite,
    RayClass.Modulus.ideleCongruenceSubgroup_narrowOfFinite]
  exact
    and_congr
      (ideleCongr_mem_infiniteCongruenceSubgroup_iff e a)
      hfiniteZero

theorem ideleCongruenceSubgroup_zero_map_ideleCongr
    (e : K ≃ₐ[ℚ] M) :
    ((RayClass.Modulus.narrowOfFinite
        (0 : RayClass.FiniteModulus K)).ideleCongruenceSubgroup).map
          (ideleCongr e).toMonoidHom =
      (RayClass.Modulus.narrowOfFinite
        (0 : RayClass.FiniteModulus M)).ideleCongruenceSubgroup := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact
      (ideleCongr_mem_ideleCongruenceSubgroup_zero_iff
        e a).2 ha
  · intro hb
    let a : IdeleGroup K :=
      (ideleCongr e).symm b
    refine ⟨a, ?_, ?_⟩
    · apply
        (ideleCongr_mem_ideleCongruenceSubgroup_zero_iff
          e a).1
      simpa only [a, (ideleCongr e).apply_symm_apply] using hb
    · exact
        (ideleCongr e).apply_symm_apply b

theorem narrowDenominator_map_ideleCongr
    (e : K ≃ₐ[ℚ] M) :
    (RayClass.narrowDenominator (K := K)).map
        (ideleCongr e).toMonoidHom =
      RayClass.narrowDenominator (K := M) := by
  rw [RayClass.narrowDenominator,
    RayClass.narrowDenominator,
    Subgroup.map_sup,
    ideleCongruenceSubgroup_zero_map_ideleCongr]
  apply congrArg
    (fun H =>
      (RayClass.Modulus.narrowOfFinite
        (0 : RayClass.FiniteModulus M)).ideleCongruenceSubgroup ⊔ H)
  change
    (IdeleGroup.principalSubgroup K).map
        (ideleCongr e) =
      IdeleGroup.principalSubgroup M
  exact idelePrincipalSubgroup_map_congr e

/-- Transport of actual idele classes along a number-field equivalence
carries the big-Hilbert norm subgroup exactly onto the big-Hilbert norm
subgroup of the target field. -/
theorem bigHilbertClassFieldNormSubgroup_map_ideleClassCongr
    (e : K ≃ₐ[ℚ] M) :
    (bigHilbertClassFieldNormSubgroup (K := K)).map
        (ideleClassCongr e).toMonoidHom =
      bigHilbertClassFieldNormSubgroup (K := M) := by
  have hcomp :
      (ideleClassCongr e).toMonoidHom.comp
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)) =
        (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup M)).comp
          (ideleCongr e).toMonoidHom := by
    ext a
    exact ideleClassCongr_mk e a
  rw [bigHilbertClassFieldNormSubgroup,
    bigHilbertClassFieldNormSubgroup,
    RayClass.Modulus.congruenceSubgroup,
    RayClass.Modulus.congruenceSubgroup,
    Subgroup.map_map, hcomp,
    ← Subgroup.map_map]
  rw [show
      ((RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus K)).ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K).map
            (ideleCongr e).toMonoidHom =
        (RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus M)).ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup M by
    simpa only [RayClass.narrowDenominator] using
      narrowDenominator_map_ideleCongr e]

/-- The canonical equivalence of big-Hilbert reciprocity quotients
induced by an equivalence of number fields. -/
noncomputable def bigHilbertClassFieldQuotientCongr
    (e : K ≃ₐ[ℚ] M) :
    (IdeleClassGroup K ⧸
        bigHilbertClassFieldNormSubgroup (K := K)) ≃*
      (IdeleClassGroup M ⧸
        bigHilbertClassFieldNormSubgroup (K := M)) :=
  QuotientGroup.congr
    (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup (K := M))
    (ideleClassCongr e)
    (bigHilbertClassFieldNormSubgroup_map_ideleClassCongr e)

/-- The big-Hilbert quotient equivalence is induced on representatives
by the actual transport of idele classes. -/
@[simp]
theorem bigHilbertClassFieldQuotientCongr_mk
    (e : K ≃ₐ[ℚ] M)
    (c : IdeleClassGroup K) :
    bigHilbertClassFieldQuotientCongr e
        (QuotientGroup.mk'
          (bigHilbertClassFieldNormSubgroup (K := K)) c) =
      QuotientGroup.mk'
        (bigHilbertClassFieldNormSubgroup (K := M))
        (ideleClassCongr e c) :=
  rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Existence_UnramifiedNormSubgroup
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramified norm subgroups

For a nonarchimedean local field, the norm subgroup of an unramified
extension of degree n is characterized by divisibility of the normalized
valuation by n. This file packages that subgroup, its quotient map, and
the canonical identification of the quotient with ZMod n.
-/

noncomputable section

universe u

namespace LocalClassFieldTheory

/-- A nonzero valuation modulus gives a finite norm quotient. -/
noncomputable instance finiteUnramifiedNormQuotient (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) [NeZero n] : Finite (Kˣ ⧸ unramifiedNormSubgroup K n) :=
  Finite.of_equiv (Multiplicative (ZMod n))
    (unramifiedNormQuotientEquivZMod K n).symm.toEquiv


end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_PowerCongruenceCore
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductor_apply _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.idealNormLiftedModulusExponent_eq_zero_of_not_mem _root_.RayClass.idealNormLiftedModulus_apply _root_.RayClass.mem_idealNormLiftedModulus_support_iff _root_.RayClass.primeToModulusIdealNorm_coe _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.rationalFiniteModulus_apply _root_.RayClass.rationalModulus_finitePart_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Power congruence subgroups inside finite-index idele-class subgroups

Let `H` be a closed finite-index subgroup of the idele class group and let
`n = [C_K : H]`.  Every `n`-th power belongs to `H`.  If a finite set of
finite places contains the support of a congruence subgroup lying in `H`,
the ideles which are local `n`-th powers on that set and integral units
away from it therefore also map into `H`.

This is the concrete power-congruence core used in the existence proof for
global class fields.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain
open GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- Let `n = [C_K : H]`.  If `S` contains the support of the canonical
congruence subgroup lying in a closed finite-index subgroup `H`, then the
idele-class power-congruence subgroup `C_K(n, S, ∅)` is contained in `H`.

The proof assembles the finitely many prescribed local `n`-th roots into
one idele.  Dividing by its `n`-th power leaves an idele in the canonical
ray congruence subgroup. -/
theorem ideleClassPowerLocalUnitSubgroup_le_closedFiniteIndexSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS :
      (RayClass.modulusInsideClosedFiniteIndex H hclosed).finitePart.support ⊆ S) :
    ideleClassPowerLocalUnitSubgroup
        (K := K)
        ⟨H.index,
          Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩
        S ∅ ≤
      H := by
  let n : ℕ+ :=
    ⟨H.index,
      Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩
  let m : RayClass.Modulus K :=
    RayClass.modulusInsideClosedFiniteIndex H hclosed
  let q : IdeleGroup K →* IdeleClassGroup K :=
    QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
  rintro _ ⟨a, ha, rfl⟩
  have ha' :=
    (mem_idelePowerLocalUnitSubgroup_iff
      (K := K) n S ∅ a).1 ha
  choose bInf hbInf using ha'.1
  choose bS hbS using
    fun v : ↥S => ha'.2.1 v.1 v.2
  let b : IdeleGroup K :=
    (ContinuousMulEquiv.piUnits.symm bInf,
      IdeleGroup.finiteIdeleOfFinset S bS)
  let u : IdeleGroup K :=
    a * (b ^ (n : ℕ))⁻¹
  have hbInfComponent (w : InfinitePlace K) :
      IdeleGroup.infiniteComponent w b = bInf w := by
    change
      ContinuousMulEquiv.piUnits
          (ContinuousMulEquiv.piUnits.symm bInf) w =
        bInf w
    exact congrFun
      (ContinuousMulEquiv.piUnits.apply_symm_apply bInf) w
  have hbInfPow (w : InfinitePlace K) :
      (bInf w) ^ (n : ℕ) =
        IdeleGroup.infiniteComponent w a := by
    exact hbInf w
  have hbFiniteComponent
      (v : ↥S) :
      IdeleGroup.finiteComponent v.1 b = bS v := by
    exact IdeleGroup.finiteIdeleOfFinset_apply_mem S bS v
  have hbFinitePow
      (v : ↥S) :
      (bS v) ^ (n : ℕ) =
        IdeleGroup.finiteComponent v.1 a := by
    exact hbS v
  have huInfinite :
      u.1 ∈ m.infiniteCongruenceSubgroup := by
    rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff_local]
    intro w
    have huComponent :
        IdeleGroup.infiniteComponent w u = 1 := by
      calc
        IdeleGroup.infiniteComponent w u =
            IdeleGroup.infiniteComponent w a *
              (IdeleGroup.infiniteComponent w b ^
                (n : ℕ))⁻¹ := by
          simp only [u, map_mul, map_inv, map_pow]
        _ = 1 := by
           rw [hbInfComponent, hbInfPow]
           simp
    change IdeleGroup.infiniteComponent w u ∈
      m.localInfiniteCongruenceSubgroup w
    rw [huComponent]
    exact Subgroup.one_mem _
  have huFinite :
      u.2 ∈ RayClass.finiteCongruenceSubgroup m.finitePart := by
    rw [RayClass.mem_finiteCongruenceSubgroup_iff]
    intro v
    by_cases hv : v ∈ S
    · let vS : ↥S := ⟨v, hv⟩
      have huComponent :
          IdeleGroup.finiteComponent v u = 1 := by
        calc
          IdeleGroup.finiteComponent v u =
              IdeleGroup.finiteComponent v a *
                (IdeleGroup.finiteComponent v b ^
                  (n : ℕ))⁻¹ := by
            simp only [u, map_mul, map_inv, map_pow]
          _ = 1 := by
            change
              IdeleGroup.finiteComponent vS.1 a *
                (IdeleGroup.finiteComponent vS.1 b ^
                  (n : ℕ))⁻¹ = 1
            rw [hbFiniteComponent vS, hbFinitePow vS]
            simp
      change IdeleGroup.finiteComponent v u ∈
        RayClass.localHigherUnitGroup v (m.finitePart v)
      rw [huComponent]
      exact Subgroup.one_mem _
    · have hmv : m.finitePart v = 0 := by
        by_contra hmv
        exact hv (hS (Finsupp.mem_support_iff.mpr hmv))
      have hbComponent :
          IdeleGroup.finiteComponent v b = 1 := by
        exact
          IdeleGroup.finiteIdeleOfFinset_apply_notMem
            S bS v hv
      have huComponent :
          IdeleGroup.finiteComponent v u =
            IdeleGroup.finiteComponent v a := by
        simp only [u, map_mul, map_inv, map_pow,
          hbComponent, one_pow, inv_one, mul_one]
      change IdeleGroup.finiteComponent v u ∈
        RayClass.localHigherUnitGroup v (m.finitePart v)
      rw [hmv, RayClass.localHigherUnitGroup_zero,
        huComponent]
      exact ha'.2.2 v (by simpa only [Finset.union_empty] using hv)
  have huCongruence :
      u ∈ RayClass.Modulus.ideleCongruenceSubgroup m :=
    ⟨huInfinite, huFinite⟩
  have hquCongruence :
      q u ∈ RayClass.Modulus.congruenceSubgroup m := by
    exact
      ⟨u, Subgroup.mem_sup_left huCongruence, rfl⟩
  have hquH : q u ∈ H := by
    apply
      RayClass.modulusInsideClosedFiniteIndex_spec
        H hclosed
    simpa only [m] using hquCongruence
  have hbPowH : q (b ^ (n : ℕ)) ∈ H := by
    change q (b ^ H.index) ∈ H
    rw [map_pow]
    let : IsMulCommutative (IdeleClassGroup K) :=
      ⟨⟨fun x y => mul_comm x y⟩⟩
    let : H.Normal := H.normal_of_isMulCommutative
    exact H.pow_index_mem (q b)
  have haDecomposition :
      a = b ^ (n : ℕ) * u := by
    dsimp only [u]
    calc
      a = a *
          ((b ^ (n : ℕ)) * (b ^ (n : ℕ))⁻¹) := by
        simp
      _ = b ^ (n : ℕ) *
          (a * (b ^ (n : ℕ))⁻¹) := by
        ac_rfl
  rw [haDecomposition, map_mul]
  exact H.mul_mem hbPowH hquH

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SmallHilbertClassFieldNaturality
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.IdeleGroup.idealClass_classRepresentative _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_refl _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Naturality of the small Hilbert class field

An equivalence of number fields carries the small-Hilbert norm subgroup
exactly onto the small-Hilbert norm subgroup.  Consequently it induces the
canonical equivalence of the corresponding reciprocity quotients.  Transport
of ordinary ideal classes is obtained from this quotient equivalence and is
therefore compatible with the canonical quotient--class-group equivalences.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

/-- Supply the canonical commutativity used by both small-Hilbert quotients. -/
theorem smallHilbertNaturalityIdeleClassIsMulCommutative
    {F : Type*} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] smallHilbertNaturalityIdeleClassIsMulCommutative

variable
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M]

/-- Transport of ordinary idele classes along an equivalence of number
fields carries the small-Hilbert norm subgroup exactly onto the
small-Hilbert norm subgroup of the target. -/
theorem smallHilbertClassFieldNormSubgroup_map_ideleClassCongr
    (e : K ≃ₐ[ℚ] M) :
    (smallHilbertClassFieldNormSubgroup (K := K)).map
        (ideleClassCongr e).toMonoidHom =
      smallHilbertClassFieldNormSubgroup (K := M) := by
  simpa only [smallHilbertClassFieldNormSubgroup,
    IdeleGroup.ordinaryIdealClassSubgroup] using
    ordinaryIdealClassSubgroup_image_map_ideleClassCongr e

/-- The canonical equivalence of small-Hilbert reciprocity quotients induced
by an equivalence of number fields. -/
noncomputable def smallHilbertClassFieldQuotientCongr
    (e : K ≃ₐ[ℚ] M) :
    (IdeleClassGroup K ⧸
        smallHilbertClassFieldNormSubgroup (K := K)) ≃*
      (IdeleClassGroup M ⧸
        smallHilbertClassFieldNormSubgroup (K := M)) :=
  QuotientGroup.congr
    (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup (K := M))
    (ideleClassCongr e)
    (smallHilbertClassFieldNormSubgroup_map_ideleClassCongr e)

/-- On representatives, the small-Hilbert quotient transport is induced by
the existing transport of ordinary idele classes. -/
@[simp]
theorem smallHilbertClassFieldQuotientCongr_mk
    (e : K ≃ₐ[ℚ] M)
    (c : IdeleClassGroup K) :
    smallHilbertClassFieldQuotientCongr e
        (QuotientGroup.mk'
          (smallHilbertClassFieldNormSubgroup (K := K)) c) =
      QuotientGroup.mk'
        (smallHilbertClassFieldNormSubgroup (K := M))
        (ideleClassCongr e c) :=
  rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SmallHilbertNormCharacterization
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
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
    smallHilbertNormCharacterization_ideleClassGroupIsMulCommutative_rbba406_1 :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
/-- If the finite ramification support is empty, the chosen completion
above every finite base place is unramified. -/
theorem chosenFinitePlaceIsUnramified_of_no_ramifiedFinitePlaces
    (hunramifiedFinite :
      _root_.ramifiedBaseFinitePlaces
          (K := K) (L := L) = ∅)
    (v : HeightOneSpectrum (𝓞 K)) :
    _root_.ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  apply
    _root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := L) v
  by_contra hramified
  have hv :
      v ∈ _root_.ramifiedBaseFinitePlaces
        (K := K) (L := L) := by
    rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
    exact
      ⟨_root_.finitePlaceExtensionCentre
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v),
        _root_.finitePlaceExtensionCentre_liesOver
          (K := K) (L := L) v
          (_root_.chosenFinitePlaceExtension (L := L) v),
        hramified⟩
  rw [hunramifiedFinite] at hv
  simp at hv

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitCore
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
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

/-- A finite quotient of nested closed rational absolute Galois
subgroups carries its canonical finite type. -/
noncomputable instance rationalClosedSubgroupQuotientFintype
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Fintype (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
  Fintype.ofFinite _

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_SeparableClosurePadicLift
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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
/-- The finite place of the cyclic fixed field obtained by restricting
the chosen extension of `v` to that field and taking its centre. -/
noncomputable def automorphismCyclicFixedPlace
    (v : HeightOneSpectrum (𝓞 K))
    (σ : Gal(L / K)) :
    let M := automorphismCyclicFixedField σ
    HeightOneSpectrum (𝓞 M) := by
  dsimp only
  let M := automorphismCyclicFixedField σ
  exact
    finitePlaceExtensionCentre
      (K := K) (L := M) v
      (restrictFinitePlaceExtension
        (K := K) (L := L) (E := M) v
        (chosenFinitePlaceExtension (L := L) v))

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitKummerUnramified
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramifiedness of the full `S`-unit Kummer extension

This file supplies the ramification input in the existence proof for the
global norm topology.  Every defining root of

`K(√[n]{Kˢ}) / K`

is first rescaled to the root of an actual `S`-unit.  Its simple
intermediate field is then identified with the chosen simple Kummer
extension attached to that unit.  The finite set of such simple fields
generating the full extension is used to kill the full inertia group away
from `S`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open HilbertRamification.Dedekind

noncomputable section

namespace KummerTheory

variable {K : Type} [Field K] [NumberField K]

/-- Away from `S`, and away from the residue characteristics dividing the
exponent, the full `S`-unit Kummer extension is unramified at the chosen
finite completion.  This is proved on the actual full extension: a finite
set of defining roots generates it, every associated simple field is
unramified by the derivative criterion, and restriction kills the full
inertia group. -/
theorem
    fullSUnitKummerExtension_chosenFinitePlaceIsUnramified_of_not_mem
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K))
    (hvS : v ∉ S)
    (hnv : v.valuation K ((n : ℕ) : K) = 1) :
    let E :=
      fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S
    letI : FiniteDimensional K E :=
      fullSUnitKummerExtension_finiteDimensional
        (K := K) (Omega := Omega) n hn hmu S
    letI : IsGalois K E :=
      fullSUnitKummerExtension_isGalois
        (K := K) (Omega := Omega) n S
    letI : NumberField E :=
      NumberField.of_module_finite K E
    ChosenFinitePlaceIsUnramified
      (K := K) (L := E) v := by
  classical
  dsimp only
  let E :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S
  let : FiniteDimensional K E :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hn hmu S
  let : IsGalois K E :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S
  let : NumberField E :=
    NumberField.of_module_finite K E
  let w := chosenFinitePlaceExtension (L := E) v
  let Q :=
    finitePlaceExtensionCentre
      (K := K) (L := E) v w
  obtain ⟨T, hTroot, hTgenerate⟩ :=
    exists_finset_fullSUnitKummerExtensionRoots_adjoin_eq_top
      (K := K) (Omega := Omega) n hn hmu S
  have hnormal :
      ∀ x : E, x ∈ T →
        Normal K (IntermediateField.adjoin K {x}) := by
    intro x hx
    let B := IntermediateField.adjoin K {x}
    let : IsGalois K B :=
      fullSUnitKummerRoot_internalAdjoin_isGalois
        (K := K) E n hn hmu S x (hTroot x hx)
    exact inferInstance
  have hsimpleInertia :
      ∀ (x : E) (hx : x ∈ T),
        inertiaGroup
            (Q.asIdeal.under
              (𝓞 (IntermediateField.adjoin K {x})))
            Gal((IntermediateField.adjoin K {x})/K) =
          ⊥ := by
    intro x hx
    let B := IntermediateField.adjoin K {x}
    let : IsGalois K B :=
      fullSUnitKummerRoot_internalAdjoin_isGalois
        (K := K) E n hn hmu S x (hTroot x hx)
    let : NumberField B :=
      NumberField.of_module_finite K B
    obtain ⟨u, alpha, _, halpha, hgenerate⟩ :=
      exists_sUnitRootUnit_generating_internalAdjoin
        (K := K) E n hn hmu S x (hTroot x hx)
    have huvaluation :
        v.valuation K (u.1 : K) = 1 :=
      (mem_SUnitGroup_iff (K := K) S u.1).mp
        u.2 v hvS
    have hunramifiedB :
        ChosenFinitePlaceIsUnramified
          (K := K) (L := B) v :=
      kummerGeneratedExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
        (K := K) n u.1 alpha halpha hgenerate
        v huvaluation hnv
    let P : HeightOneSpectrum (𝓞 B) :=
      finitePlaceBelow (K := B) Q
    have hPbelow :
        finitePlaceBelow (K := K) P = v := by
      calc
        finitePlaceBelow (K := K) P =
            finitePlaceBelow (K := K) Q := by
          exact
            finitePlaceBelow_finitePlaceBelow
              (K := K) (M := B) (L := E) Q
        _ = v :=
          finitePlaceBelow_finitePlaceExtensionCentre
            (K := K) (L := E) v w
    have hunramifiedP :
        Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal :=
      isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified
        (K := K) (L := B) v P hPbelow hunramifiedB
    have hIP :
        inertiaGroup P.asIdeal Gal(B/K) = ⊥ :=
      inertiaGroup_eq_bot_of_isUnramifiedAt
        (K := K) (M := B) P.asIdeal hunramifiedP
    simpa only [P, finitePlaceBelow_asIdeal] using hIP
  have hIQ :
      inertiaGroup Q.asIdeal Gal(E/K) = ⊥ :=
    inertiaGroup_eq_bot_of_finset_adjoin_eq_top
      (K := K) (M := E) T Q.asIdeal
      hnormal hsimpleInertia hTgenerate
  have hunramifiedQ :
      Algebra.IsUnramifiedAt (𝓞 K) Q.asIdeal :=
    isUnramifiedAt_of_inertiaGroup_eq_bot
      (K := K) (M := E) Q.asIdeal hIQ
  exact
    chosenFinitePlaceIsUnramified_of_isUnramifiedAt
      (K := K) (L := E) v
      (by simpa only [Q] using hunramifiedQ)

end KummerTheory
end
end


