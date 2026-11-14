-- Prove2me | Definitions.Def_OAIQ244Duke067
-- name    : OAIQ244Duke067
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:24:17.816654+00:00
-- url     : https://prove2.me/theorems/45d998c0-defb-425b-9b86-871ce5894c19
-- title:
--   Definitions bundle OAIQ244Duke067 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 105 declarations of OpenAI's Lean: 17 definitions, 1 instance and 87 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele`, `GlobalClassFieldTheory.Reciprocity.ideleNormSubgroup`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeFinitePlaceFieldUnit`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeFinitePlaceInteger`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitFinitePlaceIntegerUnit`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit`, `IdeleGroup.infinitePlaceFiberEquivPlacesOver`, `LocalClassFieldTheory.unramifiedNormQuotientEquivZMod`, `LubinTate.padicMultiplicativeLevelAutomorphismIntegerRingEquiv`, `LubinTate.padicMultiplicativeLevelCoefficientUniformSpace`, `LubinTate.padicMultiplicativeLevelTargetTopologicalSpace`, `LubinTate.padicMultiplicativeLevelTargetWithIdeal`, `LubinTate.padicMultiplicativeLubinTateSeries`, `LubinTate.padicMultiplicativePrimitivePoint`, `LubinTate.padicMultiplicativePrimitiveRoot`, `LubinTate.padicMultiplicativeToStandardIntertwiner`, `LubinTate.padicStandardToMultiplicativeIntertwiner`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_ClassGroup_AlgEquiv`, `AlgebraicNumberTheory_Idele_ClassGroup_NormComparison`, `AlgebraicNumberTheory_Idele_ClassGroup_TowerBaseChange`, `AlgebraicNumberTheory_Idele_NormTopology_ExtensionBehavior`, `AlgebraicNumberTheory_Idele_NormTopology_FiniteNormArithmetic`, `GlobalClassFieldTheory_GlobalClassFields_ClassFieldRealization`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_TowerRestriction`, `GlobalClassFieldTheory_Reciprocity_NormQuotient`, `GlobalClassFieldTheory_Reciprocity_OnePlaceNormKernel`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlace`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalPrincipalLocalUnit`, `LocalClassFieldTheory_Finite_Existence_UnramifiedNormSubgroup`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormComparison`, `LubinTate_FiniteLevel_CompletedIterates`, `LubinTate_Padic_MultiplicativeEvaluation_FiniteLevelEvaluation`, `LubinTate_Padic_MultiplicativeEvaluation_FiniteLevelPrimitiveRoot`, `LubinTate_Padic_MultiplicativeIntertwiner`, `LubinTate_Padic_MultiplicativeSeries`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke054`, `OAIQ244Duke055`, `OAIQ244Duke056`, `OAIQ244Duke059`, `OAIQ244Duke060` and `OAIQ244Duke061` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke072`, `OAIQ244Duke073` and `OAIQ244Duke113`.
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
import Mathlib.Algebra.Group.Subgroup.Pointwise
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
import Mathlib.Topology.Algebra.Group.Pointwise
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
import Definitions.Def_OAIQ244Duke054
import Definitions.Def_OAIQ244Duke055
import Definitions.Def_OAIQ244Duke056
import Definitions.Def_OAIQ244Duke059
import Definitions.Def_OAIQ244Duke060
import Definitions.Def_OAIQ244Duke061

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_NormComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Relative and ordinary idele-class norms

The determinant norm on relative ideles and the ordinary idele norm give
the same map after the canonical scalar-extension equivalence
`C(𝔸_K ⊗_K L) ≃ C_L`.  This comparison lets the cohomological results
proved in relative coordinates be stated with the usual norm
`N_{L/K} : C_L → C_K`.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace RelativeIdeleGroup

universe u v w

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]

/-- The Galois product formula after descent to relative idele classes. -/
theorem classInclusion_ideleClassNorm_eq_prod_conjugates
    [IsGalois K L]
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classInclusion K L
        (RelativeIdeleGroup.classNorm K L c) =
      ∏ σ : L ≃ₐ[K] L, σ • c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L)
        (RelativeIdeleGroup.inclusion K L
          (RelativeIdeleGroup.norm K L a)) =
      ∏ σ : L ≃ₐ[K] L,
        QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (σ • a)
  rw [RelativeIdeleGroup.inclusion_norm_eq_prod_conjugates]
  exact map_prod
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K L))
    (fun σ : L ≃ₐ[K] L => σ • a)
    Finset.univ

variable [Algebra L M] [IsScalarTower K L M] [IsGalois K M]

/-- The embedded-subextension norm formula after descent to relative
idele classes.  No normality of `L / K` is assumed. -/
theorem classInclusion_ideleClassNorm_eq_prod_embeddings
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classInclusion K M
        (RelativeIdeleGroup.classNorm K L c) =
      ∏ f : L →ₐ[K] M,
        RelativeIdeleGroup.classEmbedding f c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (RelativeIdeleGroup.inclusion K M
          (RelativeIdeleGroup.norm K L a)) =
      ∏ f : L →ₐ[K] M,
        QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K M)
          (RelativeIdeleGroup.ideleEmbedding f a)
  rw [RelativeIdeleGroup.inclusion_norm_eq_prod_embeddings]
  exact map_prod
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K M))
    (fun f : L →ₐ[K] M =>
      RelativeIdeleGroup.ideleEmbedding f a)
    Finset.univ

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_AlgEquiv
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Relative idele classes under an isomorphic realization

If two finite extensions of a number field are isomorphic over the base,
their tensor-product presentations of the relative adeles are canonically
isomorphic.  This file descends that canonical isomorphism to relative
ideles and idele classes and records compatibility with the determinant
norm.

The construction is the direct tensor-product congruence

`𝔸_K ⊗[K] L ≃ 𝔸_K ⊗[K] M`

induced by an algebra equivalence `L ≃ₐ[K] M`.  In particular, no second
model of relative adeles or of the idele-class norm is introduced.
-/

open scoped NumberField TensorProduct
open NumberField
open IsDedekindDomain

noncomputable section

open RelativeIdeleGroup.Cohomology


universe u v w

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [Field M] [Algebra K M]

/-- For an automorphism of the top field, canonical relative-idele
transport is the actual Galois action. -/
theorem relativeIdeleCongr_eq_smul
    (σ : L ≃ₐ[K] L)
    (a : RelativeIdeleGroup K L) :
    relativeIdeleCongr (K := K) σ a = σ • a :=
  rfl

/-- Transporting a relative idèle class along an equivalence and then
embedding it into a third relative idèle class group is the same as
embedding along the composite field embedding. -/
theorem RelativeIdeleGroup.classEmbedding_relativeIdeleClassCongr
    {N : Type*} [Field N] [Algebra K N]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [FiniteDimensional K N]
    (e : L ≃ₐ[K] M)
    (f : M →ₐ[K] N)
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classEmbedding f
        (relativeIdeleClassCongr (K := K) e c) =
      RelativeIdeleGroup.classEmbedding
        (f.comp e.toAlgHom) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    RelativeIdeleGroup.classEmbedding f
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K M)
          (relativeIdeleCongr (K := K) e a)) =
      RelativeIdeleGroup.classEmbedding
        (f.comp e.toAlgHom)
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a)
  rw [RelativeIdeleGroup.classEmbedding_mk,
    RelativeIdeleGroup.classEmbedding_mk]
  apply congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K N))
  apply Units.ext
  change
    RelativeIdeleGroup.adeleEmbedding f
        (relativeAdeleCongr (K := K) e
          (a : RelativeAdeleRing K L)) =
      RelativeIdeleGroup.adeleEmbedding
        (f.comp e.toAlgHom)
        (a : RelativeAdeleRing K L)
  induction (a : RelativeAdeleRing K L) using
      OAI.tensorInductionOn with
  | tmul x y =>
      simp only [relativeAdeleCongr_tmul,
        RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul,
        AlgHom.coe_comp, Function.comp_apply]
      rfl
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

section Absolute

variable
    {K : Type u} {M : Type w}
    [Field K] [NumberField K] [Algebra ℚ K]
    [Field M] [NumberField M] [Algebra ℚ M]

/-- The relative-to-ordinary scalar-extension comparison is natural for
transport of relative ideles along an equivalence of their top fields. -/
theorem relativeIdeleBaseChangeMulEquiv_relativeIdeleCongr
    (e : K ≃ₐ[ℚ] M)
    (a : RelativeIdeleGroup ℚ K) :
    relativeIdeleBaseChangeMulEquiv
        (K := ℚ) (L := M)
        (relativeIdeleCongr (K := ℚ) e a) =
      ideleCongr e
        (relativeIdeleBaseChangeMulEquiv
          (K := ℚ) (L := K) a) := by
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := M)).injective
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  simp only [ideleCongr, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply,
    relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  apply Units.ext
  exact
    relativeAdeleBaseChangeRingEquiv_relativeAdeleCongr
      e (a : RelativeAdeleRing ℚ K)

/-- Under the actual Galois action on relative ideles, the
relative-to-ordinary scalar-extension comparison is equivariant for the
canonical transport of ordinary ideles. -/
theorem relativeIdeleBaseChangeMulEquiv_smul_congr
    {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
    (σ : E ≃ₐ[ℚ] E)
    (a : RelativeIdeleGroup ℚ E) :
    relativeIdeleBaseChangeMulEquiv
        (K := ℚ) (L := E) (σ • a) =
      ideleCongr σ
        (relativeIdeleBaseChangeMulEquiv
          (K := ℚ) (L := E) a) := by
  rw [← relativeIdeleCongr_eq_smul (K := ℚ) σ a]
  exact
    relativeIdeleBaseChangeMulEquiv_relativeIdeleCongr
      σ a

/-- The relative-to-ordinary scalar-extension comparison is natural for
transport of relative idèle classes along an equivalence of their top
fields. -/
theorem
    relativeIdeleClassBaseChangeMulEquiv_relativeIdeleClassCongr
    (e : K ≃ₐ[ℚ] M)
    (c : RelativeIdeleGroup.ClassGroup ℚ K) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := M)
        (relativeIdeleClassCongr (K := ℚ) e c) =
      ideleClassCongr e
        (relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := M)
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup ℚ M)
          (relativeIdeleCongr (K := ℚ) e a)) =
      ideleClassCongr e
        (relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K)
          (QuotientGroup.mk'
            (RelativeIdeleGroup.principalSubgroup ℚ K) a))
  rw [relativeIdeleClassBaseChangeMulEquiv_mk,
    relativeIdeleClassBaseChangeMulEquiv_mk,
    ideleClassCongr_mk,
    relativeIdeleBaseChangeMulEquiv_relativeIdeleCongr]

section GaloisBaseChangeNaturality

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]

local instance instMulDistribMulActionAlgEquivRatClassGroup_rb40e56_1 :
    MulDistribMulAction (E ≃ₐ[ℚ] E)
      (RelativeIdeleGroup.ClassGroup ℚ E) :=
  RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction ℚ E
/-- The actual Galois action on relative idele classes becomes canonical
ordinary idele-class transport under the relative-to-ordinary
scalar-extension comparison. -/
theorem relativeIdeleClassBaseChangeMulEquiv_smul_congr
    (σ : E ≃ₐ[ℚ] E)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E) (σ • c) =
      ideleClassCongr σ
        (relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E)
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup ℚ E)
          (σ • a)) =
      ideleClassCongr σ
        (relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E)
          (QuotientGroup.mk'
            (RelativeIdeleGroup.principalSubgroup ℚ E) a))
  rw [relativeIdeleClassBaseChangeMulEquiv_mk,
    relativeIdeleClassBaseChangeMulEquiv_mk,
    ideleClassCongr_mk,
    relativeIdeleBaseChangeMulEquiv_smul_congr]

end GaloisBaseChangeNaturality

omit [Algebra ℚ K] in
theorem
    relativeAdeleBaseChangeRingEquiv_self_tmul_one
    (a : NumberField.AdeleRing (𝓞 K) K) :
    relativeAdeleBaseChangeRingEquiv
        (K := K) (L := K) (a ⊗ₜ[K] (1 : K)) =
      a := by
  apply Prod.ext
  · funext W
    rw [relativeAdeleBaseChangeRingEquiv_infiniteComponent_tmul]
    simp only [map_one, mul_one]
    let V := infinitePlaceBelow (K := K) W
    have hV : V = W :=
      infinitePlaceBelow_self (K := K) W
    let : W.1.LiesOver V.1 := ⟨rfl⟩
    change
      NumberField.LiesOver.completionMap
          (v := V) (w := W) (a.1 V) =
        a.1 W
    subst V
    exact
      infinitePlaceCompletionMap_self_apply
        (K := K) W (a.1 W)
  · apply DFunLike.coe_injective
    funext W
    rw [relativeAdeleBaseChangeRingEquiv_finiteComponent_tmul]
    simp only [map_one, mul_one]
    let v := finitePlaceBelow (K := K) W
    have hv : v = W :=
      finitePlaceBelow_self (K := K) W
    change
      finitePlaceAdicCompletionMap K K v
          ⟨W, by rfl⟩ (a.2 v) =
        a.2 W
    subst v
    exact
      finitePlaceAdicCompletionMap_self_apply
        K W (a.2 W)

omit [Algebra ℚ K] in
theorem
    relativeAdeleBaseChangeRingEquiv_self_symm_apply
    (a : NumberField.AdeleRing (𝓞 K) K) :
    (relativeAdeleBaseChangeRingEquiv
        (K := K) (L := K)).symm a =
      a ⊗ₜ[K] (1 : K) := by
  apply
    (relativeAdeleBaseChangeRingEquiv
      (K := K) (L := K)).injective
  rw [RingEquiv.apply_symm_apply,
    relativeAdeleBaseChangeRingEquiv_self_tmul_one]

/-- Scalar extension from `ℚ` to a realization algebra-equivalent to
`ℚ` is the canonical transport of ordinary adele rings. -/
theorem rationalAdeleExtension_eq_adeleCongr
    (e : ℚ ≃ₐ[ℚ] M)
    (a : NumberField.AdeleRing (𝓞 ℚ) ℚ) :
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (RelativeIdeleGroup.adeleInclusion ℚ M a) =
      adeleCongr e a := by
  change
    relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (a ⊗ₜ[ℚ] (1 : M)) =
      relativeAdeleBaseChangeRingEquiv
        (K := ℚ) (L := M)
        (relativeAdeleCongr (K := ℚ) e
          ((relativeAdeleBaseChangeRingEquiv
            (K := ℚ) (L := ℚ)).symm a))
  rw [relativeAdeleBaseChangeRingEquiv_self_symm_apply]
  simp only [relativeAdeleCongr_tmul, map_one]

/-- Scalar extension from `ℚ` to a realization algebra-equivalent to
`ℚ` is the canonical transport of ordinary ideles. -/
theorem rationalIdeleExtension_eq_ideleCongr
    (e : ℚ ≃ₐ[ℚ] M) :
    IdeleGroup.extension ℚ M =
      (ideleCongr e).toMonoidHom := by
  apply MonoidHom.ext
  intro a
  change
    relativeIdeleBaseChangeMulEquiv
        (K := ℚ) (L := M)
        (RelativeIdeleGroup.inclusion ℚ M a) =
      ideleCongr e a
  apply
    (IdeleGroup.equivAdeleRingUnits
      (K := M)).injective
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  apply Units.ext
  exact
    rationalAdeleExtension_eq_adeleCongr e
      ((IdeleGroup.equivAdeleRingUnits
        (K := ℚ) a :
          (NumberField.AdeleRing (𝓞 ℚ) ℚ)ˣ) :
        NumberField.AdeleRing (𝓞 ℚ) ℚ)

/-- Scalar extension from `ℚ` to a realization algebra-equivalent to
`ℚ` is the canonical transport of ordinary idele classes. -/
theorem rationalIdeleClassExtension_eq_ideleClassCongr
    (e : ℚ ≃ₐ[ℚ] M) :
    ideleClassExtension ℚ M =
      (ideleClassCongr e).toMonoidHom := by
  apply MonoidHom.ext
  intro c
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup M)
        (IdeleGroup.extension ℚ M a) =
      QuotientGroup.mk'
        (IdeleGroup.principalSubgroup M)
        (ideleCongr e a)
  exact congrArg
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup M))
    (DFunLike.congr_fun
      (rationalIdeleExtension_eq_ideleCongr e) a)
end Absolute
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_TowerBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_of_ne _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_finiteComponent_same _root_.RelativeIdeleGroup.relativeFinitePlaceIdele_infiniteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_finiteComponent _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_of_ne _root_.RelativeIdeleGroup.relativeInfinitePlaceIdele_infiniteComponent_same _root_.relativeAdeleMapOfCompatibleEquiv_tmul _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.relativeAdeleCongr_tmul _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleClassCongr_mk _root_.relativeIdeleCongr_coe _root_.relativeIdeleCongr_norm _root_.relativeIdeleCongr_principalIdele
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

section RingComparison

attribute [local instance] towerBaseChange_towerRelativeIdeleGroupIsMulCommutative
attribute [local instance] towerBaseChange_relativeIdeleClassGroupIsMulCommutative
attribute [local instance] towerBaseChange_ideleClassGroupIsMulCommutative
omit [NumberField L] [FiniteDimensional M L] in
/-- Passing from the fixed-bottom tower presentation to the actual
relative adele ring over the intermediate field intertwines
conjugation by an automorphism of the top field. -/
theorem towerActualRelativeAdeleRingEquiv_unflatten_conjugation
    (σ : L ≃ₐ[M] L)
    (z : RelativeAdeleRing K L) :
    towerActualRelativeAdeleRingEquiv K M L
        (towerRelativeAdeleUnflatten K M L
          (RelativeIdeleGroup.conjugation K L
            (σ.restrictScalars K) z)) =
      RelativeIdeleGroup.conjugation M L σ
        (towerActualRelativeAdeleRingEquiv K M L
          (towerRelativeAdeleUnflatten K M L z)) := by
  induction z using OAI.tensorInductionOn with
  | tmul a x =>
      simp [RelativeIdeleGroup.conjugation_tmul,
        towerRelativeAdeleUnflatten_tmul,
        bottomAdeleToTower_apply, topFieldToTower_apply,
        towerActualRelativeAdeleRingEquiv_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

end RingComparison

section IdeleComparison

attribute [local instance] towerBaseChange_towerRelativeIdeleGroupIsMulCommutative
attribute [local instance] towerBaseChange_relativeIdeleClassGroupIsMulCommutative
attribute [local instance] towerBaseChange_ideleClassGroupIsMulCommutative
omit [NumberField L] [FiniteDimensional M L] in
/-- The tower-to-actual comparison transports the restricted
bottom-field conjugation to conjugation over the intermediate field. -/
theorem towerRelativeIdeleBaseChangeMulEquiv_unflatten_conjugation
    (σ : L ≃ₐ[M] L)
    (a : RelativeIdeleGroup K L) :
    towerRelativeIdeleBaseChangeMulEquiv K M L
        ((towerRelativeIdeleEquiv K M L).symm
          (RelativeIdeleGroup.conjugationIdele K L
            (σ.restrictScalars K) a)) =
      RelativeIdeleGroup.conjugationIdele M L σ
        (towerRelativeIdeleBaseChangeMulEquiv K M L
          ((towerRelativeIdeleEquiv K M L).symm a)) := by
  apply Units.ext
  exact
    towerActualRelativeAdeleRingEquiv_unflatten_conjugation
      K M L σ (a : RelativeAdeleRing K L)

omit [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional M L] in
/-- Extending an idele from the intermediate relative adele ring into
the tower and then passing to the actual `M`-relative presentation is
the ordinary relative class-field-theoretic inclusion. -/
theorem towerRelativeIdeleBaseChangeMulEquiv_includeLeft
    (a : RelativeIdeleGroup K M) :
    towerRelativeIdeleBaseChangeMulEquiv K M L
        (Units.map
          (Algebra.TensorProduct.includeLeft
            (R := M) (S := M)
            (A := RelativeAdeleRing K M) (B := L)).toRingHom a) =
      RelativeIdeleGroup.inclusion M L
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := M) a) := by
  apply Units.ext
  change
    towerActualRelativeAdeleRingEquiv K M L
        ((a : RelativeAdeleRing K M) ⊗ₜ[M] (1 : L)) =
      ((IdeleGroup.equivAdeleRingUnits (K := M)
          (relativeIdeleBaseChangeMulEquiv
            (K := K) (L := M) a) :
        (NumberField.AdeleRing (𝓞 M) M)ˣ) :
          NumberField.AdeleRing (𝓞 M) M) ⊗ₜ[M] (1 : L)
  rw [towerActualRelativeAdeleRingEquiv_tmul]
  congr 1
  simpa [intermediateRelativeAdeleBaseChangeAlgEquiv] using
    congrArg Units.val
      (relativeIdeleBaseChangeMulEquiv_eq_ringUnits
        (K := K) (L := M) a).symm

omit [NumberField L] [FiniteDimensional M L] in
/-- The class-group comparison transports the Galois action obtained
by restricting scalars from the bottom field to the natural action
over the intermediate field. -/
theorem towerRelativeIdeleClassBaseChangeMulEquiv_smul
    (σ : L ≃ₐ[M] L)
    (c : RelativeIdeleGroup.ClassGroup K L) :
    towerRelativeIdeleClassBaseChangeMulEquiv K M L
        ((TowerRelativeIdeleGroup.classGroupEquiv K M L).symm
          ((σ.restrictScalars K) • c)) =
      σ •
        towerRelativeIdeleClassBaseChangeMulEquiv K M L
          ((TowerRelativeIdeleGroup.classGroupEquiv K M L).symm c) := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup M L)
        (towerRelativeIdeleBaseChangeMulEquiv K M L
          ((towerRelativeIdeleEquiv K M L).symm
            (RelativeIdeleGroup.conjugationIdele K L
              (σ.restrictScalars K) a))) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup M L)
        (RelativeIdeleGroup.conjugationIdele M L σ
          (towerRelativeIdeleBaseChangeMulEquiv K M L
            ((towerRelativeIdeleEquiv K M L).symm a)))
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup M L))
    (towerRelativeIdeleBaseChangeMulEquiv_unflatten_conjugation
      K M L σ a)

end IdeleComparison
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Existence_UnramifiedNormSubgroup
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
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

/-- A unit maps to one exactly when its valuation is divisible by `n`. -/
theorem valuationModDegreeMulHom_eq_one_iff_dvd (K : Type u) [Field K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x : Kˣ) :
    valuationModDegreeMulHom K n x = 1 ↔
      (n : Int) ∣
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) := by
  change valuationModDegree K n (Additive.ofMul x) = 0 ↔ _
  exact valuationModDegree_eq_zero_iff_dvd K n (Additive.ofMul x)

/-- Every unramified norm class is represented by a field unit. -/
theorem unramifiedNormClass_surjective (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) :
    Function.Surjective (unramifiedNormClass K n) :=
  QuotientGroup.mk'_surjective (unramifiedNormSubgroup K n)

/-- A unit has trivial norm class exactly when its valuation is divisible by the degree. -/
theorem unramifiedNormClass_eq_one_iff (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x : Kˣ) :
    unramifiedNormClass K n x = 1 ↔
      (n : Int) ∣ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) := by
  exact (QuotientGroup.eq_one_iff (N := unramifiedNormSubgroup K n) x).trans
    (mem_unramifiedNormSubgroup_iff K n x)

/-- A unit has trivial norm class exactly when it belongs to the unramified norm subgroup. -/
theorem unramifiedNormClass_eq_one_iff_mem (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x : Kˣ) :
    unramifiedNormClass K n x = 1 ↔ x ∈ unramifiedNormSubgroup K n := by
  rw [unramifiedNormClass_eq_one_iff, mem_unramifiedNormSubgroup_iff]

/-- The unramified norm subgroup is the kernel of the multiplicative reduced valuation. -/
theorem unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHom (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) :
    MonoidHom.ker (valuationModDegreeMulHom K n) = unramifiedNormSubgroup K n := by
  ext x
  rw [MonoidHom.mem_ker, mem_unramifiedNormSubgroup_iff,
    valuationModDegreeMulHom_eq_one_iff_dvd]

/-- The valuation quotient model
`Kˣ / {x | n ∣ v(x)} ≃ Z/nZ`, in multiplicative notation. -/
noncomputable def unramifiedNormQuotientEquivZMod (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) :
    Kˣ ⧸ unramifiedNormSubgroup K n ≃* Multiplicative (ZMod n) :=
  (QuotientGroup.quotientMulEquivOfEq
    (unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHom K n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (valuationModDegreeMulHom K n)
      (valuationModDegreeMulHom_surjective K n))

/-- The quotient equivalence sends a unit class to its valuation modulo the degree. -/
@[simp]
theorem unramifiedNormQuotientEquivZMod_mk (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x : Kˣ) :
    unramifiedNormQuotientEquivZMod K n (QuotientGroup.mk x) =
      valuationModDegreeMulHom K n x := by
  simp only [unramifiedNormQuotientEquivZMod, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rw [QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply,
    QuotientGroup.kerLift_mk]

/-- For nonzero degree, the unramified norm quotient has cardinality equal to that degree. -/
theorem unramifiedNormQuotient_card_eq_degree (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) [NeZero n] :
    Nat.card (Kˣ ⧸ unramifiedNormSubgroup K n) = n := by
  calc
    Nat.card (Kˣ ⧸ unramifiedNormSubgroup K n) =
        Nat.card (Multiplicative (ZMod n)) :=
      Nat.card_congr (unramifiedNormQuotientEquivZMod K n).toEquiv
    _ = Nat.card (ZMod n) := Nat.card_congr Multiplicative.toAdd
    _ = n := Nat.card_zmod n


end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormTopology_FiniteNormArithmetic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.ideleClassCongr_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place arithmetic of idele norms

This file relates the finite components of the ordinary idele norm to local
orders and positive prime norms. It also proves the degree formula for the
finite positive norm under scalar extension.
-/

open scoped BigOperators NNReal NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

open AlgebraicNumberTheory.Valuations
open Function

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- A finite idele norm is its finitely supported product of local prime
norms raised to the corresponding local orders. -/
theorem finiteAbsoluteNorm_eq_finprod
    (a : FiniteIdeleGroup K) :
    FiniteIdeleGroup.absoluteNorm a =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        FiniteIdeleGroup.primeNorm v ^
          (FiniteIdeleGroup.localOrder v (a v)).toAdd := by
  classical
  let e := (FiniteIdeleGroup.valuationVector a).toAdd
  have heval (v : HeightOneSpectrum (𝓞 K)) :
      e v =
        (FiniteIdeleGroup.localOrder v (a v)).toAdd := by
    simpa only [e] using
      FiniteIdeleGroup.valuationVector_apply a v
  have hsupport :
      mulSupport
          (fun v : HeightOneSpectrum (𝓞 K) =>
            FiniteIdeleGroup.primeNorm v ^ e v) ⊆
        e.support := by
    intro v hv
    by_contra hmem
    have hev : e v = 0 :=
      Finsupp.notMem_support_iff.mp hmem
    exact hv (by simp [hev])
  rw [FiniteIdeleGroup.absoluteNorm_apply]
  change
    e.prod
        (fun v n => FiniteIdeleGroup.primeNorm v ^ n) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        FiniteIdeleGroup.primeNorm v ^
          (FiniteIdeleGroup.localOrder v (a v)).toAdd
  calc
    e.prod
          (fun v n => FiniteIdeleGroup.primeNorm v ^ n) =
        ∏ v ∈ e.support,
          FiniteIdeleGroup.primeNorm v ^ e v := rfl
    _ =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          FiniteIdeleGroup.primeNorm v ^ e v :=
      (finprod_eq_prod_of_mulSupport_subset _ hsupport).symm
    _ =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          FiniteIdeleGroup.primeNorm v ^
            (FiniteIdeleGroup.localOrder v (a v)).toAdd :=
      finprod_congr fun v => by rw [heval]

omit [FiniteDimensional K L] in
/-- The positive prime norm upstairs is the inertia-degree power of the
positive prime norm below. -/
theorem primeNorm_above
    (v₀ : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀}) :
    FiniteIdeleGroup.primeNorm W.1 =
      FiniteIdeleGroup.primeNorm v₀ ^
        W.1.asIdeal.inertiaDeg (𝓞 K) := by
  let : W.1.asIdeal.LiesOver v₀.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal W.2.symm
  apply Units.ext
  apply NNReal.eq
  change
    (Ideal.absNorm W.1.asIdeal : ℝ) =
      (Ideal.absNorm v₀.asIdeal : ℝ) ^
        W.1.asIdeal.inertiaDeg (𝓞 K)
  exact_mod_cast
    (Ideal.absNorm_pow_inertiaDeg
      v₀.asIdeal W.1.asIdeal).symm

end IdeleGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormTopology_ExtensionBehavior
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Scalar-extension behavior of idele norms

Scalar extension raises the finite, archimedean, and absolute idele norms to
the degree of the number-field extension. The rational relative-idele
base-change realization is included as the endpoint used by cyclotomic
reciprocity.
-/

open scoped BigOperators Classical NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- The fiber of restriction of infinite places is the set of places
lying over the chosen base place. -/
noncomputable def infinitePlaceFiberEquivPlacesOver
    (v₀ : InfinitePlace K) :
    {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v₀} ≃
      {W : InfinitePlace L // W ∈ v₀.placesOver L} where
  toFun W :=
    ⟨W.1, ⟨congrArg (fun v : InfinitePlace K => v.1) W.2⟩⟩
  invFun W :=
    ⟨W.1, by
      change W.1.comap (algebraMap K L) = v₀
      let : W.1.1.LiesOver v₀.1 := W.2
      exact InfinitePlace.LiesOver.comap_eq W.1 v₀⟩
  left_inv W := Subtype.ext rfl
  right_inv W := Subtype.ext rfl

omit [FiniteDimensional K L] in
/-- The inertia degrees in a restriction fiber sum to the global
extension degree. -/
theorem infinitePlaceFiber_inertiaDeg_sum
    (v₀ : InfinitePlace K) :
    ∑ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v₀},
      v₀.inertiaDeg W.1 =
        Module.finrank K L := by
  classical
  calc
    (∑ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v₀},
        v₀.inertiaDeg W.1) =
        ∑ W : {W : InfinitePlace L //
            W ∈ v₀.placesOver L},
          v₀.inertiaDeg W.1 :=
      Fintype.sum_equiv
        (infinitePlaceFiberEquivPlacesOver
          (K := K) (L := L) v₀)
        (fun W => v₀.inertiaDeg W.1)
        (fun W => v₀.inertiaDeg W.1)
        (fun _ => rfl)
    _ =
        ∑ W ∈ v₀.placesOver L,
          v₀.inertiaDeg W := by
      symm
      apply Finset.sum_subtype
      intro W
      simp
    _ = Module.finrank K L := by
      exact
        InfinitePlace.sum_inertiaDeg_eq_finrank
          K L v₀

omit [FiniteDimensional K L] in
/-- The total archimedean multiplicity in a restriction fiber is the
base multiplicity times the extension degree. -/
theorem infinitePlaceFiber_mult_sum
    (v₀ : InfinitePlace K) :
    ∑ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v₀},
      W.1.mult =
        v₀.mult * Module.finrank K L := by
  classical
  calc
    (∑ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v₀},
        W.1.mult) =
        ∑ W : {W : InfinitePlace L //
            _root_.infinitePlaceBelow (K := K) W = v₀},
          v₀.mult * v₀.inertiaDeg W.1 := by
      apply Finset.sum_congr rfl
      intro W _
      exact
        infinitePlace_mult_eq_base_mult_mul_inertiaDeg
          (K := K) (L := L) v₀ W.1
          ⟨congrArg (fun v : InfinitePlace K => v.1) W.2⟩
    _ =
        v₀.mult *
          ∑ W : {W : InfinitePlace L //
              _root_.infinitePlaceBelow (K := K) W = v₀},
            v₀.inertiaDeg W.1 := by
      rw [Finset.mul_sum]
    _ = v₀.mult * Module.finrank K L := by
      rw [infinitePlaceFiber_inertiaDeg_sum
        (K := K) (L := L) v₀]

/-- Scalar extension raises the archimedean idele norm to the degree of
the extension. -/
theorem archimedeanNorm_extension
    (a : IdeleGroup K) :
    InfiniteIdeleGroup.archimedeanNorm
        (extension K L a).1 =
      InfiniteIdeleGroup.archimedeanNorm a.1 ^
        Module.finrank K L := by
  classical
  have hlocal (W : InfinitePlace L) :
      nnnormUnitHom W.Completion
          (infiniteComponent W (extension K L a)) =
        nnnormUnitHom
          (_root_.infinitePlaceBelow (K := K) W).Completion
          (infiniteComponent
            (_root_.infinitePlaceBelow (K := K) W) a) := by
    let v₀ := _root_.infinitePlaceBelow (K := K) W
    let : W.1.LiesOver v₀.1 := ⟨rfl⟩
    rw [extension_infiniteComponent K L a W]
    exact
      nnnormUnitHom_infinitePlaceCompletionMap
        (K := K) (L := L) v₀ W
        (infiniteComponent v₀ a)
  rw [InfiniteIdeleGroup.archimedeanNorm_apply,
    InfiniteIdeleGroup.archimedeanNorm_apply]
  change
    (∏ W : InfinitePlace L,
        nnnormUnitHom W.Completion
          (infiniteComponent W (extension K L a)) ^ W.mult) =
      (∏ v₀ : InfinitePlace K,
          nnnormUnitHom v₀.Completion
            (infiniteComponent v₀ a) ^ v₀.mult) ^
        Module.finrank K L
  simp_rw [hlocal]
  calc
    (∏ W : InfinitePlace L,
        nnnormUnitHom
            (_root_.infinitePlaceBelow (K := K) W).Completion
            (infiniteComponent
              (_root_.infinitePlaceBelow (K := K) W) a) ^
          W.mult) =
        ∏ v₀ : InfinitePlace K,
          ∏ W : {W : InfinitePlace L //
              _root_.infinitePlaceBelow (K := K) W = v₀},
            nnnormUnitHom
                (_root_.infinitePlaceBelow
                  (K := K) W.1).Completion
                (infiniteComponent
                  (_root_.infinitePlaceBelow
                    (K := K) W.1) a) ^
              W.1.mult :=
      (Fintype.prod_fiberwise
        (_root_.infinitePlaceBelow (K := K))
        (fun W : InfinitePlace L =>
          nnnormUnitHom
              (_root_.infinitePlaceBelow (K := K) W).Completion
              (infiniteComponent
                (_root_.infinitePlaceBelow (K := K) W) a) ^
            W.mult)).symm
    _ =
        ∏ v₀ : InfinitePlace K,
          ∏ W : {W : InfinitePlace L //
              _root_.infinitePlaceBelow (K := K) W = v₀},
            nnnormUnitHom v₀.Completion
                (infiniteComponent v₀ a) ^
              W.1.mult := by
      apply Finset.prod_congr rfl
      intro v₀ _
      apply Finset.prod_congr rfl
      intro W _
      rw [W.2]
    _ =
        ∏ v₀ : InfinitePlace K,
          nnnormUnitHom v₀.Completion
              (infiniteComponent v₀ a) ^
            (∑ W : {W : InfinitePlace L //
                _root_.infinitePlaceBelow (K := K) W = v₀},
              W.1.mult) := by
      apply Finset.prod_congr rfl
      intro v₀ _
      exact
        Finset.prod_pow_eq_pow_sum
          Finset.univ
          (fun W : {W : InfinitePlace L //
              _root_.infinitePlaceBelow (K := K) W = v₀} =>
            W.1.mult)
          (nnnormUnitHom v₀.Completion
            (infiniteComponent v₀ a))
    _ =
        ∏ v₀ : InfinitePlace K,
          nnnormUnitHom v₀.Completion
              (infiniteComponent v₀ a) ^
            (v₀.mult * Module.finrank K L) := by
      apply Finset.prod_congr rfl
      intro v₀ _
      rw [infinitePlaceFiber_mult_sum
        (K := K) (L := L) v₀]
    _ =
        ∏ v₀ : InfinitePlace K,
          (nnnormUnitHom v₀.Completion
              (infiniteComponent v₀ a) ^ v₀.mult) ^
            Module.finrank K L := by
      apply Finset.prod_congr rfl
      intro v₀ _
      rw [pow_mul]
    _ =
        (∏ v₀ : InfinitePlace K,
          nnnormUnitHom v₀.Completion
            (infiniteComponent v₀ a) ^ v₀.mult) ^
          Module.finrank K L := by
      exact
        Finset.prod_pow
          Finset.univ
          (Module.finrank K L)
          (fun v₀ : InfinitePlace K =>
            nnnormUnitHom v₀.Completion
              (infiniteComponent v₀ a) ^ v₀.mult)

/-- If the finite part of a rational idele is trivial, then its scalar
extension has absolute norm equal to the extension degree power of the
original absolute norm. -/
theorem absoluteNorm_relativeIdeleBaseChange_inclusion_of_finite_eq_one
    (a : IdeleGroup ℚ)
    (ha : a.2 = 1) :
    absoluteNorm
        (_root_.relativeIdeleBaseChangeMulEquiv
          (K := ℚ) (L := L)
          (RelativeIdeleGroup.inclusion ℚ L a)) =
      absoluteNorm a ^ Module.finrank ℚ L := by
  change
    absoluteNorm (extension ℚ L a) =
      absoluteNorm a ^ Module.finrank ℚ L
  have hfinite : (extension ℚ L a).2 = 1 := by
    apply RestrictedProduct.ext
    intro W
    change finiteComponent W (extension ℚ L a) = 1
    rw [extension_finiteComponent]
    change
      Units.map
          (finitePlaceAdicCompletionMap ℚ L
            (_root_.finitePlaceBelow (K := ℚ) W)
            ⟨W, rfl⟩).toMonoidHom
          (a.2 (_root_.finitePlaceBelow (K := ℚ) W)) =
        1
    rw [ha]
    exact map_one _
  rw [absoluteNorm_apply, absoluteNorm_apply, hfinite, ha,
    map_one, one_mul,
    archimedeanNorm_extension (K := ℚ) (L := L)]
  simpa only [map_one, one_mul] using
    (inv_pow (InfiniteIdeleGroup.archimedeanNorm a.1)
      (Module.finrank ℚ L)).symm


end IdeleGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ClassFieldRealization
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Concrete realization of finite abelian subextensions

A finite abelian subextension in the abstract class-formation lattice is
represented by two nested closed subgroups of an ambient Galois group.  Its
upper relative fixed field is an actual finite extension of the lower fixed
field.  The quotient-to-Galois-group equivalence transports the commutativity
carried by the abstract package, so this actual extension is abelian Galois.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology
open scoped IsMulCommutative

universe u v w

variable
    {k Ω : Type}
    [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    {K : ClosedSubgroup (Gal(Ω / k))}

/-- The actual relative fixed field represented by a finite abelian
subextension is an abelian Galois extension of the actual base fixed field. -/
noncomputable instance
    finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois
    (L : FiniteAbelianSubextension K) :
    IsAbelianGalois
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω L.below) := by
  let F := abstractFixedField k Ω K
  let E := abstractRelativeFixedField k Ω L.below
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      k Ω K L.field L.below L.normal
  let e : L.extensionQuotient ≃* Gal(E / F) :=
    L.extensionQuotientMulEquiv.trans
      (abstractExtensionQuotientEquivGaloisGroup
        k Ω K L.field L.below L.normal)
  refine { is_comm.comm := fun σ τ ↦ ?_ }
  exact e.symm.injective (by
    simpa only [map_mul] using
      mul_comm (e.symm σ) (e.symm τ))

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_TowerRestriction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Restriction in a finite-place Artin tower

This module restricts finite-place extensions through an intermediate field and proves restriction naturality for the corresponding global Artin homomorphisms.
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

omit [NumberField K] [FiniteDimensional K L] in
/-- A compatible embedding of algebraic localizations carries
restriction of decomposition-group elements to restriction of the
corresponding local automorphisms. -/
theorem decompositionGroupEquivAlgebraicLocalizationAut_restrict_of_commutes
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (wE : AbsoluteValueExtension vK E)
    (wL : AbsoluteValueExtension vK L) :
    letI hEK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) wE.1
    letI : SMul K wE.1.Completion := hEK.toSMul
    letI : Algebra vK.Completion wE.1.Completion :=
      AbsoluteValue.completionAlgebra vK wE.1 wE.2
    letI hLK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) wL.1
    letI : SMul K wL.1.Completion := hLK.toSMul
    letI : Algebra vK.Completion wL.1.Completion :=
      AbsoluteValue.completionAlgebra vK wL.1 wL.2
    let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
    let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
    ∀ (localizationEmbedding : EL →ₐ[vK.Completion] LL),
      letI hELL : Algebra EL LL :=
        localizationEmbedding.toRingHom.toAlgebra
      letI : SMul EL LL := hELL.toSMul
      letI : IsScalarTower vK.Completion EL LL :=
        IsScalarTower.of_algebraMap_eq' (by
          apply RingHom.ext
          intro x
          exact (localizationEmbedding.commutes x).symm)
      letI : FiniteDimensional vK.Completion EL :=
        AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
          vK hvK wE
      letI : IsAbelianGalois vK.Completion EL :=
        LocalClassFieldTheory.localizedCompletion_isAbelianGalois
          vK hvK wE
      let eDE :
          absoluteValueDecompositionGroup K wE.1 ≃*
            (EL ≃ₐ[vK.Completion] EL) :=
        decompositionGroupEquivAlgebraicLocalizationAut
          vK hvK wE
      let eDL :
          absoluteValueDecompositionGroup K wL.1 ≃*
            (LL ≃ₐ[vK.Completion] LL) :=
        decompositionGroupEquivAlgebraicLocalizationAut
          vK hvK wL
      (∀ z : E,
        localizationEmbedding
            (AbsoluteValue.toAlgebraicLocalization
              vK wE.1 wE.2 z) =
          AbsoluteValue.toAlgebraicLocalization
            vK wL.1 wL.2 (algebraMap E L z)) →
        ∀ tauL : LL ≃ₐ[vK.Completion] LL,
          AlgEquiv.restrictNormalHom E
              ((eDL.symm tauL).1 : L ≃ₐ[K] L) =
            ((eDE.symm
              (AlgEquiv.restrictNormalHom EL tauL)).1 :
                E ≃ₐ[K] E) := by
  let hEK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wE.1
  let : SMul K wE.1.Completion := hEK.toSMul
  let : Algebra vK.Completion wE.1.Completion :=
    AbsoluteValue.completionAlgebra vK wE.1 wE.2
  let hLK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wL.1
  let : SMul K wL.1.Completion := hLK.toSMul
  let : Algebra vK.Completion wL.1.Completion :=
    AbsoluteValue.completionAlgebra vK wL.1 wL.2
  let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
  let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
  change
    ∀ localizationEmbedding : EL →ₐ[vK.Completion] LL, _
  intro localizationEmbedding
  let hELL : Algebra EL LL :=
    localizationEmbedding.toRingHom.toAlgebra
  let : SMul EL LL := hELL.toSMul
  let : IsScalarTower vK.Completion EL LL :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (localizationEmbedding.commutes x).symm)
  let : FiniteDimensional vK.Completion EL :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
      vK hvK wE
  let : IsAbelianGalois vK.Completion EL :=
    LocalClassFieldTheory.localizedCompletion_isAbelianGalois
      vK hvK wE
  let eDE :
      absoluteValueDecompositionGroup K wE.1 ≃*
        (EL ≃ₐ[vK.Completion] EL) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK wE
  let eDL :
      absoluteValueDecompositionGroup K wL.1 ≃*
        (LL ≃ₐ[vK.Completion] LL) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK wL
  change
    (∀ z : E,
      localizationEmbedding
          (AbsoluteValue.toAlgebraicLocalization
            vK wE.1 wE.2 z) =
        AbsoluteValue.toAlgebraicLocalization
          vK wL.1 wL.2 (algebraMap E L z)) →
      ∀ tauL : LL ≃ₐ[vK.Completion] LL, _
  intro hlocalization tauL
  let rhoL : absoluteValueDecompositionGroup K wL.1 :=
    eDL.symm tauL
  let tauE := AlgEquiv.restrictNormalHom EL tauL
  let rhoE : absoluteValueDecompositionGroup K wE.1 :=
    eDE.symm tauE
  change
    AlgEquiv.restrictNormalHom E
        (rhoL.1 : L ≃ₐ[K] L) =
      (rhoE.1 : E ≃ₐ[K] E)
  apply AlgEquiv.ext
  intro z
  apply (algebraMap E L).injective
  apply
    (AbsoluteValue.toAlgebraicLocalization
      vK wL.1 wL.2).injective
  let u : EL :=
    AbsoluteValue.toAlgebraicLocalization
      vK wE.1 wE.2 z
  have hcommutes :
      tauL (localizationEmbedding u) =
        localizationEmbedding
          ((AlgEquiv.restrictNormalHom EL tauL) u) := by
    change
      tauL (algebraMap EL LL u) =
        algebraMap EL LL
          ((AlgEquiv.restrictNormalHom EL tauL) u)
    exact
      (AlgEquiv.restrictNormal_commutes
        tauL EL u).symm
  calc
    AbsoluteValue.toAlgebraicLocalization vK wL.1 wL.2
        (algebraMap E L
          ((AlgEquiv.restrictNormalHom E
            (rhoL.1 : L ≃ₐ[K] L)) z)) =
      AbsoluteValue.toAlgebraicLocalization vK wL.1 wL.2
        ((rhoL.1 : L ≃ₐ[K] L)
          (algebraMap E L z)) := by
            exact congrArg
              (AbsoluteValue.toAlgebraicLocalization
                vK wL.1 wL.2)
              (AlgEquiv.restrictNormal_commutes
                (rhoL.1 : L ≃ₐ[K] L) E z)
    _ = eDL rhoL
        (AbsoluteValue.toAlgebraicLocalization
          vK wL.1 wL.2 (algebraMap E L z)) := by
            rw [localizationRamificationGroups_decompositionGroupEquiv_toLocalization]
    _ = tauL
        (AbsoluteValue.toAlgebraicLocalization
          vK wL.1 wL.2 (algebraMap E L z)) := by
            rw [eDL.apply_symm_apply]
    _ = tauL
        (localizationEmbedding
          (AbsoluteValue.toAlgebraicLocalization
            vK wE.1 wE.2 z)) := by
            rw [hlocalization]
    _ = localizationEmbedding
        ((AlgEquiv.restrictNormalHom EL tauL)
          (AbsoluteValue.toAlgebraicLocalization
            vK wE.1 wE.2 z)) := by
            exact hcommutes
    _ = localizationEmbedding
        (tauE
          (AbsoluteValue.toAlgebraicLocalization
            vK wE.1 wE.2 z)) := by
            rfl
    _ = localizationEmbedding
        (eDE rhoE
          (AbsoluteValue.toAlgebraicLocalization
            vK wE.1 wE.2 z)) := by
            rw [eDE.apply_symm_apply]
    _ = localizationEmbedding
        (AbsoluteValue.toAlgebraicLocalization vK wE.1 wE.2
          ((rhoE.1 : E ≃ₐ[K] E) z)) := by
            rw [localizationRamificationGroups_decompositionGroupEquiv_toLocalization]
    _ = AbsoluteValue.toAlgebraicLocalization vK wL.1 wL.2
        (algebraMap E L
          ((rhoE.1 : E ≃ₐ[K] E) z)) := by
            rw [hlocalization]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_NormQuotient
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_mk _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Ideles in the ordinary idele-class norm quotient

This file supplies the useful composite from ideles to the quotient
of `C_K` by the range of the ordinary norm `C_L → C_K`, used by the
global norm-residue-symbol constructions.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

local instance normQuotientIdeleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The composite from ideles to the canonical class norm quotient
`C_K / N_{L/K} C_L`. -/
def globalNormClassFromIdele :
    IdeleGroup K →*
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range :=
  (QuotientGroup.mk'
      (_root_.ideleClassNorm K L).range).comp
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K))

omit [FiniteDimensional K L] in
/-- The map from ideles to the class norm quotient factors through
`C_K`, so it kills every principal idele. -/
@[simp]
theorem globalNormClassFromIdele_principalIdele
    (x : Kˣ) :
    globalNormClassFromIdele K L
        (IdeleGroup.principalIdele K x) = 1 := by
  rw [globalNormClassFromIdele, MonoidHom.comp_apply]
  have hclass :
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (IdeleGroup.principalIdele K x) = 1 :=
    (QuotientGroup.eq_one_iff
      (IdeleGroup.principalIdele K x)).2 ⟨x, rfl⟩
  rw [hclass, map_one]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_OnePlaceNormKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
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

/-- The image of the global norm on relative ideles. -/
def ideleNormSubgroup :
    Subgroup (IdeleGroup K) :=
  (RelativeIdeleGroup.norm K L).range

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_isCyclotomic _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramified finite places of rational cyclotomic levels

This file connects the cyclotomic ramification-index formula over `ℤ`
to the finite-place completions used by the global Artin map.  A rational
prime outside the conductor is unramified at the actual chosen extension
of its normalized finite-place absolute value.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions
/-- The centre of the chosen finite-place extension in a rational
cyclotomic level is algebraically unramified away from the level. -/
theorem rationalCyclotomicLevel_isUnramifiedAt_chosenFinitePlaceCentre
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    Algebra.IsUnramifiedAt (𝓞 ℚ)
      (finitePlaceExtensionCentre
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel m)
        (RayClass.rationalPrime q)
        (chosenFinitePlaceExtension
          (L := KummerTheory.rationalCyclotomicLevel m)
          (RayClass.rationalPrime q))).asIdeal := by
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    RayClass.rationalPrime q
  let L :=
    KummerTheory.rationalCyclotomicLevel m
  let W :=
    finitePlaceExtensionCentre
      (K := ℚ) (L := L) v
      (chosenFinitePlaceExtension (L := L) v)
  change Algebra.IsUnramifiedAt (𝓞 ℚ) W.asIdeal
  let hWv : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver
      (K := ℚ) (L := L) v
      (chosenFinitePlaceExtension (L := L) v)
  let hvq :
      v.asIdeal.LiesOver (Ideal.span {(q.1 : ℤ)}) := by
    dsimp only [v]
    exact rationalPrime_liesOver_integerSpan q
  let hWq :
      W.asIdeal.LiesOver (Ideal.span {(q.1 : ℤ)}) :=
    Ideal.LiesOver.trans W.asIdeal v.asIdeal
      (Ideal.span {(q.1 : ℤ)})
  have hAbsolute :
      W.asIdeal.ramificationIdx ℤ = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd
      q.1 L W.asIdeal hq
  have hTower :
      W.asIdeal.ramificationIdx ℤ =
        v.asIdeal.ramificationIdx ℤ *
          W.asIdeal.ramificationIdx (𝓞 ℚ) :=
    Ideal.ramificationIdx_tower
      (R := ℤ) v.asIdeal W.asIdeal
  have hRelative :
      W.asIdeal.ramificationIdx (𝓞 ℚ) = 1 :=
    Nat.eq_one_of_mul_eq_one_left
      (hTower.symm.trans hAbsolute)
  exact Ideal.ramificationIdx_eq_one_iff.mp hRelative

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_MultiplicativeSeries
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.padicValuationSubringToCompletedUnramifiedWittRing_uniformizer _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The multiplicative Lubin--Tate series over `ℚ_p`

Mathlib's binomial series at the natural exponent `p` is

`(1 + X) ^ p`.

After subtracting `1`, this has zero constant coefficient, linear
coefficient `p`, and reduction `X ^ p`.  Thus it is the Lubin--Tate series
attached to the multiplicative formal group and the canonical prime
uniformizer of `ℚ_p`.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- The multiplicative Lubin--Tate series `(1 + X) ^ p - 1` over `ℚ_p`,
represented by mathlib's binomial series. -/
noncomputable def padicMultiplicativeLubinTateSeries
    (p : ℕ) [Fact p.Prime] :
    LubinTateSeries (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) where
  toPowerSeries :=
    PowerSeries.binomialSeries
        (padicLocalField p).valuationSubring (p : ℤ) -
      1
  constantCoeff_eq_zero := by
    simp
  coeff_one_eq_uniformizer := by
    have hcoeff : PowerSeries.coeff 1
        (PowerSeries.binomialSeries
            (padicLocalField p).valuationSubring (p : ℤ) - 1) =
        (p : (padicLocalField p).valuationSubring) := by
      simp only [PowerSeries.binomialSeries_nat, map_sub,
        PowerSeries.coeff_one]
      rw [PowerSeries.coeff_one_pow]
      simp
    exact hcoeff.trans (map_natCast (padicIntEquivValuationSubring p) p).symm
  map_residue_eq_frobenius := by
    let eO : ℤ_[p] ≃+*
        (padicDVRValuation p).valuationSubring :=
      padicIntEquivValuationSubring p
    let eRes :
        (padicLocalField p).residueField ≃+* ZMod p := by
      change
        IsLocalRing.ResidueField
            (padicDVRValuation p).valuationSubring ≃+*
          ZMod p
      exact
        (IsLocalRing.ResidueField.mapEquiv eO).symm.trans
          (padicIntResidueFieldEquivZMod p)
    let : CharP (padicLocalField p).residueField p :=
      charP_of_injective_ringHom
        (f := eRes.symm.toRingHom) eRes.symm.injective p
    let : CharP (PowerSeries (padicLocalField p).residueField) p :=
      CharP.of_ringHom_of_ne_zero
        PowerSeries.C p ((Fact.out : p.Prime).ne_zero)
    have hcard :
        Nat.card (padicLocalField p).residueField = p := by
      simpa [padicLocalField] using
        padicCompleteDVF_residueField_card p
    rw [hcard, PowerSeries.binomialSeries_nat (R := ℤ)]
    simp only [map_sub, map_pow, map_add, map_one, PowerSeries.map_X]
    rw [add_pow_char]
    simp

namespace LubinTateSeries

/-- The underlying series is literally mathlib's binomial series minus one. -/
@[simp]
theorem padicMultiplicativeLubinTateSeries_toPowerSeries
    (p : ℕ) [Fact p.Prime] :
    (padicMultiplicativeLubinTateSeries p).toPowerSeries =
      PowerSeries.binomialSeries
          (padicLocalField p).valuationSubring (p : ℤ) -
        1 :=
  rfl

end LubinTateSeries

/-- The prime occurring as the linear coefficient of the multiplicative
Lubin--Tate series is a uniformizer for the chosen valuation on `ℚ_p`. -/
theorem padicMultiplicativeLubinTateSeries_isUniformizer
    (p : ℕ) [Fact p.Prime] :
    (padicLocalField p).toCompleteDVF.valuation.IsUniformizer
      ((padicIntEquivValuationSubring p (p : ℤ_[p]) :
          (padicLocalField p).valuationSubring) : ℚ_[p]) := by
  change
    (padicDVRValuation p).IsUniformizer
      ((padicIntEquivValuationSubring p (p : ℤ_[p]) :
          (padicDVRValuation p).valuationSubring) : ℚ_[p])
  simpa using padicDVRValuation_isUniformizer_p p

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalPrincipalLocalUnit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.padicValuationSubringToCompletedUnramifiedWittRing_uniformizer _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The ramified local unit of a rational principal idele

For a nonzero rational number `x` and a rational prime `p`, removing the
`p`-power from `x` produces an actual `p`-adic unit.  This file identifies
that unit simultaneously in the height-one completion used by global
reciprocity, in the standard field `ℚ_[p]`, and in the valuation subring
used by the multiplicative Lubin--Tate construction.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open LocalFieldTheory.DiscreteValuationField.Examples.Qp

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_1
/-- The rational `p`-unit, expressed as a unit of the valuation subring of
the standard local field `ℚ_[p]`. -/
def rationalPrimeUnitValuationSubringUnit
    (x : ℚˣ) (p : Nat.Primes) :
    (padicLocalField p.1).valuationSubringˣ :=
  Units.map
      (padicIntEquivValuationSubring
        p.1).toMonoidHom
    (padicIntUnitOfRat p
      (rationalPrimeUnit x p : ℚ)
      (Units.ne_zero _)
      (padicValRat_rationalPrimeUnit x p))

/-- Forgetting the integrality proof from the standard valuation-subring
unit recovers the rational `p`-unit in `ℚ_[p]`. -/
@[simp]
theorem rationalPrimeUnitValuationSubringUnit_coe
    (x : ℚˣ) (p : Nat.Primes) :
    ((rationalPrimeUnitValuationSubringUnit x p :
        (padicLocalField p.1).valuationSubring) :
      ℚ_[p.1]) =
        ((rationalPrimeUnit x p : ℚ) : ℚ_[p.1]) := by
  change
    ((padicIntEquivValuationSubring p.1
        (padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (Units.ne_zero _)
          (padicValRat_rationalPrimeUnit x p)) :
        (padicLocalField p.1).valuationSubring) :
      ℚ_[p.1]) =
        ((rationalPrimeUnit x p : ℚ) : ℚ_[p.1])
  rw [
    padicIntEquivValuationSubring_coe,
    padicIntUnitOfRat_coe]

/-- The Lubin--Tate field-unit inclusion of the rational `p`-unit is the
ordinary embedding of that rational unit into `ℚ_[p]`. -/
theorem standardLubinTateUnitFactorFieldUnit_rationalPrimeUnit
    (x : ℚˣ) (p : Nat.Primes) :
    LubinTate.standardLubinTateUnitFactorFieldUnit
        (padicLocalField p.1)
        (rationalPrimeUnitValuationSubringUnit x p) =
      Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom
        (rationalPrimeUnit x p) := by
  apply Units.ext
  change
    ((rationalPrimeUnitValuationSubringUnit x p :
        (padicLocalField p.1).valuationSubring) :
      ℚ_[p.1]) =
        algebraMap ℚ ℚ_[p.1] (rationalPrimeUnit x p : ℚ)
  exact rationalPrimeUnitValuationSubringUnit_coe x p

/-- The standard multiplicative Lubin--Tate base uniformizer is exactly the
image of the positive rational prime generator in `ℚ_[p]ˣ`. -/
theorem standardLubinTateBaseUniformizerUnit_eq_rationalPrimeGenerator
    (p : Nat.Primes) :
    LubinTate.standardLubinTateBaseUniformizerUnit
        (LubinTate.padicMultiplicativeLubinTateSeries_isUniformizer
          p.1) =
      Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom
        (Units.mk0 (p.1 : ℚ) (by
          exact_mod_cast p.2.ne_zero)) := by
  apply Units.ext
  change
    ((padicIntEquivValuationSubring
        p.1 (p.1 : ℤ_[p.1]) :
      (padicLocalField p.1).valuationSubring) :
        ℚ_[p.1]) =
      algebraMap ℚ ℚ_[p.1] (p.1 : ℚ)
  rw [padicIntEquivValuationSubring_coe]
  simp

/-- Restoring the removed `p`-power recovers the original rational field
unit.  This is the multiplicative factorization used after completion. -/
theorem rationalPrimeUnit_mul_primeGenerator_zpow
    (x : ℚˣ) (p : Nat.Primes) :
    rationalPrimeUnit x p *
        (Units.mk0 (p.1 : ℚ) (by
          exact_mod_cast p.2.ne_zero)) ^
          padicValRat p.1 (x : ℚ) =
      x := by
  rw [rationalPrimeUnit]
  calc
    ((Units.mk0 (p.1 : ℚ) (by
          exact_mod_cast p.2.ne_zero)) ^
        (-padicValRat p.1 (x : ℚ)) * x) *
          (Units.mk0 (p.1 : ℚ) (by
            exact_mod_cast p.2.ne_zero)) ^
            padicValRat p.1 (x : ℚ) =
        x * ((Units.mk0 (p.1 : ℚ) (by
              exact_mod_cast p.2.ne_zero)) ^
            (-padicValRat p.1 (x : ℚ)) *
          (Units.mk0 (p.1 : ℚ) (by
              exact_mod_cast p.2.ne_zero)) ^
            padicValRat p.1 (x : ℚ)) := by
      ac_rfl
    _ = x := by
      rw [← zpow_add]
      simp

/-- In `ℚ_[p]ˣ`, a rational field unit is its actual integral
`rationalPrimeUnit` factor times the corresponding power of the standard
multiplicative Lubin--Tate uniformizer. -/
theorem rationalPadicFieldUnit_eq_unitFactor_mul_baseUniformizer_zpow
    (x : ℚˣ) (p : Nat.Primes) :
    Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom x =
      LubinTate.standardLubinTateUnitFactorFieldUnit
          (padicLocalField p.1)
          (rationalPrimeUnitValuationSubringUnit x p) *
        LubinTate.standardLubinTateBaseUniformizerUnit
            (LubinTate.padicMultiplicativeLubinTateSeries_isUniformizer
              p.1) ^
          padicValRat p.1 (x : ℚ) := by
  rw [
    standardLubinTateUnitFactorFieldUnit_rationalPrimeUnit,
    standardLubinTateBaseUniformizerUnit_eq_rationalPrimeGenerator,
    ← map_zpow,
    ← map_mul,
    rationalPrimeUnit_mul_primeGenerator_zpow]

/-- The exponent selected by the complete-DVF uniformizer decomposition of a
rational element is its ordinary `p`-adic valuation. -/
theorem rationalPadicFieldUnit_uniformizerValueExponent
    (x : ℚˣ) (p : Nat.Primes) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent
        (padicLocalField p.1).toCompleteDVF)
        (LubinTate.padicMultiplicativeLubinTateSeries_isUniformizer
          p.1)
        (Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom x) =
      padicValRat p.1 (x : ℚ) := by
  let F := padicLocalField p.1
  let hπ :=
    LubinTate.padicMultiplicativeLubinTateSeries_isUniformizer
      p.1
  let X : ℚ_[p.1]ˣ :=
    Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom x
  let u : F.valuationSubringˣ :=
    rationalPrimeUnitValuationSubringUnit x p
  let ϖ : ℚ_[p.1]ˣ :=
    LubinTate.standardLubinTateBaseUniformizerUnit hπ
  let V :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer
      F.toCompleteDVF) hπ
  have hfactor :
      X =
        LubinTate.standardLubinTateUnitFactorFieldUnit F u *
          ϖ ^ padicValRat p.1 (x : ℚ) := by
    simpa only [F, hπ, X, u, ϖ] using
      rationalPadicFieldUnit_eq_unitFactor_mul_baseUniformizer_zpow
        x p
  have huMem :
      LubinTate.standardLubinTateUnitFactorFieldUnit F u ∈
        F.valuation.valuationSubring.unitGroup := by
    simpa only [
      LubinTate.standardLubinTateUnitFactorFieldUnit] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits_mem_unitGroup
        F.toCompleteDVF u)
  have hzero :
      V.zeroSubgroup =
        F.valuation.valuationSubring.unitGroup := by
    simpa only [V] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup
        F.toCompleteDVF hπ)
  have huZero :
      V.val
          (LubinTate.standardLubinTateUnitFactorFieldUnit F u) =
        0 := by
    apply (V.mem_zeroSubgroup_iff _).1
    rw [hzero]
    exact huMem
  have hϖeq :
      ϖ =
        Units.mk0
          ((padicIntEquivValuationSubring
              p.1 (p.1 : ℤ_[p.1]) :
            (padicLocalField p.1).valuationSubring) :
            ℚ_[p.1])
          hπ.ne_zero := by
    apply Units.ext
    change
      (ϖ : ℚ_[p.1]) =
        ((padicIntEquivValuationSubring
            p.1 (p.1 : ℤ_[p.1]) :
          (padicLocalField p.1).valuationSubring) :
          ℚ_[p.1])
    simpa only [ϖ] using
      LubinTate.standardLubinTateBaseUniformizerUnit_coe hπ
  have hϖ : V.IsUniformizer ϖ := by
    rw [hϖeq]
    simpa only [V] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_isUniformizer
        F.toCompleteDVF hπ)
  change V.val X = padicValRat p.1 (x : ℚ)
  rw [
    hfactor,
    V.val_mul,
    V.val_uniformizer_zpow hϖ,
    huZero,
    zero_add]

/-- The actual unit part chosen by the standard multiplicative Lubin--Tate
uniformizer decomposition of a rational `p`-adic field unit is precisely
`rationalPrimeUnitValuationSubringUnit`. -/
theorem rationalPadicFieldUnit_uniformizerUnitPart
    (x : ℚˣ) (p : Nat.Primes) :
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitUniformizerUnitPart
        (padicLocalField p.1).toCompleteDVF
        (LubinTate.padicMultiplicativeLubinTateSeries_isUniformizer
          p.1)
        (Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom x) =
      rationalPrimeUnitValuationSubringUnit x p := by
  let F := padicLocalField p.1
  let hπ :=
    LubinTate.padicMultiplicativeLubinTateSeries_isUniformizer
      p.1
  let X : ℚ_[p.1]ˣ :=
    Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom x
  let u : F.valuationSubringˣ :=
    rationalPrimeUnitValuationSubringUnit x p
  let ϖ : ℚ_[p.1]ˣ :=
    LubinTate.standardLubinTateBaseUniformizerUnit hπ
  apply
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_injective
  refine
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart
      F.toCompleteDVF hπ X).trans ?_
  change
    X * ϖ ^
        (-((LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent
          F.toCompleteDVF) hπ X)) =
      LubinTate.standardLubinTateUnitFactorFieldUnit F u
  rw [
    show
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent
          F.toCompleteDVF) hπ X =
        padicValRat p.1 (x : ℚ) by
        simpa only [F, hπ, X] using
          rationalPadicFieldUnit_uniformizerValueExponent x p,
    show
      X =
        LubinTate.standardLubinTateUnitFactorFieldUnit F u *
          ϖ ^ padicValRat p.1 (x : ℚ) by
        simpa only [F, hπ, X, u, ϖ] using
          rationalPadicFieldUnit_eq_unitFactor_mul_baseUniformizer_zpow
            x p]
  rw [mul_assoc, ← zpow_add]
  simp

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormComparison
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norm quotients for unramified local extensions

For a finite unramified Galois extension, the field-norm subgroup is exactly
the subgroup of elements whose normalized valuation is divisible by the
extension degree. The inclusion is the normalized norm formula; the reverse
inclusion follows from finite local reciprocity because the norm quotient and
the valuation quotient have the same finite cardinality.
-/

noncomputable section


namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]
  [Module.Finite 𝒪[K] 𝒪[L]]
  [IsUnramifiedValuedExtension K L]

/-- Every field norm has normalized valuation divisible by the degree. -/
theorem localNormSubgroup_le_unramifiedNormSubgroup :
    localNormSubgroup K L ≤
      unramifiedNormSubgroup K (Module.finrank K L) := by
  intro x hx
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
  apply (mem_unramifiedNormSubgroup_iff K (Module.finrank K L) _).2
  rw [valuationMap_apply]
  change (Module.finrank K L : Int) ∣
    v K (Additive.ofMul
      (LocalFieldTheory.normUnits K L y))
  rw [v_normUnits_eq_residue_finrank_mul_of_isGalois K L,
    unramifiedValuation_residue_finrank_eq_finrank K L]
  exact dvd_mul_right _ _

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_CompletedIterates
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHom_apply_ofAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_mul_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeries_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_expSeries_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_one_ofWithZeroValuation _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.padicMultiplicativeLubinTateSeries_toPowerSeries _root_.LubinTate.padicValuationSubringToCompletedUnramifiedWittRing_uniformizer _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Valuations of standard Lubin--Tate iterates at a primitive point

At primitive level `n + 1`, the `i`-fold standard Lubin--Tate iterate has
normalized additive valuation `q ^ i` for `i ≤ n`.  The proof uses the
two-term formula

`f(y) = y ^ q + π y`.

The first summand has valuation `q ^ (i + 1)`.  The second has strictly
larger valuation because the image of the base uniformizer has valuation
equal to the totally ramified level degree `(q - 1) q ^ n`.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- Before the annihilating level, the evaluated iterates have exact
normalized additive valuations `1, q, ..., q ^ n`. -/
theorem standardLubinTatePrimitivePointIterateInteger_addVal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n i : ℕ) (hi : i ≤ n) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (standardLubinTatePrimitivePointIterateInteger hπ n i) =
      (Nat.card F.residueField ^ i : ℕ) := by
  induction i with
  | zero =>
      simpa using
        standardLubinTatePrimitivePointInteger_addVal hπ n
  | succ i ih =>
      let target := standardLubinTateLevelCompleteDVF hπ n
      let q := Nat.card F.residueField
      let d := (q - 1) * q ^ n
      let y := standardLubinTatePrimitivePointIterateInteger hπ n i
      have hi' : i ≤ n := Nat.le_trans (Nat.le_succ i) hi
      have hiy :
          IsDiscreteValuationRing.addVal target.valuationSubring y =
            (q ^ i : ℕ) := by
        exact ih hi'
      have hπval :
          IsDiscreteValuationRing.addVal target.valuationSubring
              (standardLubinTateLevelCoefficientHom hπ n π) =
            (d : ℕ) := by
        simpa [target, q, d, standardLubinTateLevelCoefficientHom] using
          standardLubinTateBaseUniformizerInteger_map_addVal hπ n
      have hpow :
          IsDiscreteValuationRing.addVal target.valuationSubring
              (y ^ q) =
            (q ^ (i + 1) : ℕ) := by
        rw [IsDiscreteValuationRing.addVal_pow, hiy]
        simp [nsmul_eq_mul, pow_succ, Nat.mul_comm]
      have hmul :
          IsDiscreteValuationRing.addVal target.valuationSubring
              (standardLubinTateLevelCoefficientHom hπ n π * y) =
            (d + q ^ i : ℕ) := by
        rw [IsDiscreteValuationRing.addVal_mul, hπval, hiy]
        rfl
      have hqone : 1 < q := by
        exact Finite.one_lt_card
      have hqpos : 0 < q := Nat.zero_lt_one.trans hqone
      have hpowle : q ^ (i + 1) ≤ q ^ n :=
        Nat.pow_le_pow_right hqpos hi
      have hqsub : 1 ≤ q - 1 := by
        omega
      have hdegreele : q ^ n ≤ d := by
        calc
          q ^ n = 1 * q ^ n := by simp
          _ ≤ (q - 1) * q ^ n :=
            Nat.mul_le_mul_right (q ^ n) hqsub
      have htailpos : 0 < q ^ i := Nat.pow_pos hqpos
      have hnatlt : q ^ (i + 1) < d + q ^ i :=
        hpowle.trans_lt
          (hdegreele.trans_lt (Nat.lt_add_of_pos_right htailpos))
      have henatlt :
          (q ^ (i + 1) : ℕ∞) < (d + q ^ i : ℕ) := by
        exact_mod_cast hnatlt
      have hdistinct :
          IsDiscreteValuationRing.addVal target.valuationSubring
                (y ^ q) ≠
            IsDiscreteValuationRing.addVal target.valuationSubring
              (standardLubinTateLevelCoefficientHom hπ n π * y) := by
        rw [hpow, hmul]
        exact ne_of_lt henatlt
      rw [standardLubinTatePrimitivePointIterateInteger_succ]
      rw [AddValuation.map_add_of_distinct_val
        (IsDiscreteValuationRing.addVal target.valuationSubring) hdistinct,
        hpow, hmul]
      rw [min_eq_left]
      exact henatlt.le

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_MultiplicativeIntertwiner
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.padicValuationSubringToCompletedUnramifiedWittRing_uniformizer _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Comparing the standard and multiplicative Lubin--Tate series over `ℚ_p`

The characteristic-independent same-uniformizer recursion supplies the
canonical series with linear coefficient `1` satisfying

`[(1 + X)^p - 1](H(X)) = H([pX + X^p](X))`.

Consequently, evaluation of `H` carries standard Lubin--Tate division points
to multiplicative division points.  This file constructs that series directly;
it does not identify the two actions from equality of their kernels.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

/-- The canonical linear-term-one intertwiner carrying standard Lubin--Tate
division points over `ℚ_p` to multiplicative division points. -/
noncomputable def padicStandardToMultiplicativeIntertwiner
    (p : ℕ) [Fact p.Prime] :
    PowerSeries (padicLocalField p).valuationSubring :=
  recursiveIntertwiner
    (padicMultiplicativeLubinTateSeries_isUniformizer p)
    (padicMultiplicativeLubinTateSeries p)
    (standardLubinTateSeries
      (padicMultiplicativeLubinTateSeries_isUniformizer p))
    (fun _ : Unit => 1)

/-- The standard-to-multiplicative intertwiner has linear coefficient `1`
and no constant term. -/
theorem padicStandardToMultiplicativeIntertwiner_hasLinearTerm
    (p : ℕ) [Fact p.Prime] :
    HasLinearTerm (padicStandardToMultiplicativeIntertwiner p)
      (fun _ : Unit =>
        (1 : (padicLocalField p).valuationSubring)) :=
  recursiveIntertwiner_hasLinearTerm
    (padicMultiplicativeLubinTateSeries_isUniformizer p)
    (padicMultiplicativeLubinTateSeries p)
    (standardLubinTateSeries
      (padicMultiplicativeLubinTateSeries_isUniformizer p))
    (fun _ : Unit => 1)

/-- The canonical series satisfies the literal same-uniformizer equation
from the multiplicative series to the standard series. -/
theorem padicStandardToMultiplicativeIntertwiner_intertwines
    (p : ℕ) [Fact p.Prime] :
    Intertwines
      (padicMultiplicativeLubinTateSeries p)
      (standardLubinTateSeries
        (padicMultiplicativeLubinTateSeries_isUniformizer p))
      (padicStandardToMultiplicativeIntertwiner p) :=
  recursiveIntertwiner_intertwines
    (padicMultiplicativeLubinTateSeries_isUniformizer p)
    (padicMultiplicativeLubinTateSeries p)
    (standardLubinTateSeries
      (padicMultiplicativeLubinTateSeries_isUniformizer p))
    (fun _ : Unit => 1)

/-- One-variable form of the intertwining equation:
the multiplicative series after `H` equals `H` after the standard series. -/
theorem padicStandardToMultiplicativeIntertwiner_functionalEquation
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.subst
        (padicStandardToMultiplicativeIntertwiner p)
        (padicMultiplicativeLubinTateSeries p).toPowerSeries =
      PowerSeries.subst
        (standardLubinTateSeries
          (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries
        (padicStandardToMultiplicativeIntertwiner p) := by
  have h :=
    padicStandardToMultiplicativeIntertwiner_intertwines p
  calc
    PowerSeries.subst
        (padicStandardToMultiplicativeIntertwiner p)
        (padicMultiplicativeLubinTateSeries p).toPowerSeries =
        MvPowerSeries.subst
          (fun i : Unit =>
            inVariable
              (standardLubinTateSeries
                (padicMultiplicativeLubinTateSeries_isUniformizer p)) i)
          (padicStandardToMultiplicativeIntertwiner p) :=
      h
    _ =
        PowerSeries.subst
          (standardLubinTateSeries
            (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries
          (padicStandardToMultiplicativeIntertwiner p) := by
      rw [PowerSeries.subst_def]
      congr 1
      funext i
      cases i
      exact
        PowerSeries.X_subst
          (standardLubinTateSeries
            (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries

/-- The intertwiner has zero constant coefficient, hence admits formal
substitution. -/
theorem padicStandardToMultiplicativeIntertwiner_hasSubst
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.HasSubst
      (padicStandardToMultiplicativeIntertwiner p) :=
  (padicStandardToMultiplicativeIntertwiner_hasLinearTerm p).hasSubst

/-- The coefficient of `X` in the canonical intertwiner is `1`. -/
@[simp]
theorem padicStandardToMultiplicativeIntertwiner_coeff_one
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.coeff 1
        (padicStandardToMultiplicativeIntertwiner p) =
      1 :=
  (padicStandardToMultiplicativeIntertwiner_hasLinearTerm p).coeff_single ()

/-- Conjugating a standard scalar endomorphism through the canonical
comparison gives the unique multiplicative-series endomorphism with the
same scalar linear coefficient. -/
theorem padicStandardToMultiplicativeIntertwiner_endomorphism
    (p : ℕ) [Fact p.Prime]
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (standardLubinTateEndomorphism
          (padicMultiplicativeLubinTateSeries_isUniformizer p) a)
        (padicStandardToMultiplicativeIntertwiner p) =
      PowerSeries.subst
        (padicStandardToMultiplicativeIntertwiner p)
        (recursiveIntertwiner
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          (padicMultiplicativeLubinTateSeries p)
          (padicMultiplicativeLubinTateSeries p)
          (fun _ : Unit => a)) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let E := padicMultiplicativeLubinTateSeries p
  let Ebar := standardLubinTateSeries hπ
  let H := padicStandardToMultiplicativeIntertwiner p
  let S := standardLubinTateEndomorphism hπ a
  let M :=
    recursiveIntertwiner hπ E E (fun _ : Unit => a)
  have hH :
      HasLinearTerm H
        (fun _ : Unit =>
          (1 : (padicLocalField p).valuationSubring)) :=
    padicStandardToMultiplicativeIntertwiner_hasLinearTerm p
  have hS :
      HasLinearTerm S (fun _ : Unit => a) :=
    standardLubinTateEndomorphism_hasLinearTerm hπ a
  have hM :
      HasLinearTerm M (fun _ : Unit => a) :=
    recursiveIntertwiner_hasLinearTerm hπ E E (fun _ : Unit => a)
  have hleftLinearRaw :=
    hH.subst
      (G := fun _ : Unit => S)
      (M := fun _ : Unit => fun _ : Unit => a)
      (fun _ => hS)
  have hleftLinear :
      HasLinearTerm (PowerSeries.subst S H)
        (fun _ : Unit => a) := by
    simpa [PowerSeries.subst_def] using hleftLinearRaw
  have hrightLinearRaw :=
    hM.subst
      (G := fun _ : Unit => H)
      (M := fun _ : Unit => fun _ : Unit =>
        (1 : (padicLocalField p).valuationSubring))
      (fun _ => hH)
  have hrightLinear :
      HasLinearTerm (PowerSeries.subst H M)
        (fun _ : Unit => a) := by
    simpa [PowerSeries.subst_def] using hrightLinearRaw
  have hHIntertwines :
      Intertwines E Ebar H :=
    padicStandardToMultiplicativeIntertwiner_intertwines p
  have hSIntertwines :
      Intertwines Ebar Ebar S :=
    standardLubinTateEndomorphism_intertwines hπ a
  have hMIntertwines :
      Intertwines E E M :=
    recursiveIntertwiner_intertwines hπ E E (fun _ : Unit => a)
  have hleftIntertwines :
      Intertwines E Ebar (PowerSeries.subst S H) :=
    hHIntertwines.powerSeries_subst hH.hasSubst
      hSIntertwines hS.hasSubst
  have hrightIntertwines :
      Intertwines E Ebar (PowerSeries.subst H M) :=
    hMIntertwines.powerSeries_subst hM.hasSubst
      hHIntertwines hH.hasSubst
  exact
    eq_of_hasLinearTerm_of_intertwines hπ E Ebar
      (fun _ : Unit => a)
      hleftLinear hleftIntertwines
      hrightLinear hrightIntertwines

/-- The canonical inverse-direction intertwiner carrying multiplicative
division points to standard Lubin--Tate division points. -/
noncomputable def padicMultiplicativeToStandardIntertwiner
    (p : ℕ) [Fact p.Prime] :
    PowerSeries (padicLocalField p).valuationSubring :=
  recursiveIntertwiner
    (padicMultiplicativeLubinTateSeries_isUniformizer p)
    (standardLubinTateSeries
      (padicMultiplicativeLubinTateSeries_isUniformizer p))
    (padicMultiplicativeLubinTateSeries p)
    (fun _ : Unit => 1)

/-- The multiplicative-to-standard intertwiner also has linear coefficient
`1` and no constant term. -/
theorem padicMultiplicativeToStandardIntertwiner_hasLinearTerm
    (p : ℕ) [Fact p.Prime] :
    HasLinearTerm (padicMultiplicativeToStandardIntertwiner p)
      (fun _ : Unit =>
        (1 : (padicLocalField p).valuationSubring)) :=
  recursiveIntertwiner_hasLinearTerm
    (padicMultiplicativeLubinTateSeries_isUniformizer p)
    (standardLubinTateSeries
      (padicMultiplicativeLubinTateSeries_isUniformizer p))
    (padicMultiplicativeLubinTateSeries p)
    (fun _ : Unit => 1)

/-- The inverse-direction canonical series satisfies its literal
same-uniformizer equation. -/
theorem padicMultiplicativeToStandardIntertwiner_intertwines
    (p : ℕ) [Fact p.Prime] :
    Intertwines
      (standardLubinTateSeries
        (padicMultiplicativeLubinTateSeries_isUniformizer p))
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeToStandardIntertwiner p) :=
  recursiveIntertwiner_intertwines
    (padicMultiplicativeLubinTateSeries_isUniformizer p)
    (standardLubinTateSeries
      (padicMultiplicativeLubinTateSeries_isUniformizer p))
    (padicMultiplicativeLubinTateSeries p)
    (fun _ : Unit => 1)

/-- The inverse-direction intertwiner admits formal substitution. -/
theorem padicMultiplicativeToStandardIntertwiner_hasSubst
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.HasSubst
      (padicMultiplicativeToStandardIntertwiner p) :=
  (padicMultiplicativeToStandardIntertwiner_hasLinearTerm p).hasSubst

/-- Composing the reverse comparison after the standard-to-multiplicative
series is the identity on the standard coordinate. -/
theorem padicMultiplicativeToStandardIntertwiner_subst_reverse
    (p : ℕ) [Fact p.Prime] :
    PowerSeries.subst
        (padicStandardToMultiplicativeIntertwiner p)
        (padicMultiplicativeToStandardIntertwiner p) =
      PowerSeries.X := by
  have hcomp :=
    (padicMultiplicativeToStandardIntertwiner_hasLinearTerm p).subst
      (G := fun _ : Unit =>
        padicStandardToMultiplicativeIntertwiner p)
      (M := fun _ : Unit => fun _ : Unit =>
        (1 : (padicLocalField p).valuationSubring))
      (fun _ =>
        padicStandardToMultiplicativeIntertwiner_hasLinearTerm p)
  have hcomp' :
      HasLinearTerm
        (PowerSeries.subst
          (padicStandardToMultiplicativeIntertwiner p)
          (padicMultiplicativeToStandardIntertwiner p))
        (fun _ : Unit =>
          (1 : (padicLocalField p).valuationSubring)) := by
    simpa [PowerSeries.subst_def] using hcomp
  have hIcomp :=
    (padicMultiplicativeToStandardIntertwiner_intertwines p).powerSeries_subst
      (padicMultiplicativeToStandardIntertwiner_hasSubst p)
      (padicStandardToMultiplicativeIntertwiner_intertwines p)
      (padicStandardToMultiplicativeIntertwiner_hasSubst p)
  have hX :
      HasLinearTerm
        (PowerSeries.X :
          PowerSeries (padicLocalField p).valuationSubring)
        (fun _ : Unit => 1) := by
    simpa [PowerSeries.X] using
      (hasLinearTerm_X
        (R := (padicLocalField p).valuationSubring) ())
  exact
    eq_of_hasLinearTerm_of_intertwines
      (padicMultiplicativeLubinTateSeries_isUniformizer p)
      (standardLubinTateSeries
        (padicMultiplicativeLubinTateSeries_isUniformizer p))
      (standardLubinTateSeries
        (padicMultiplicativeLubinTateSeries_isUniformizer p))
      (fun _ : Unit => 1)
      hcomp' hIcomp hX
      (intertwines_X
        (standardLubinTateSeries
          (padicMultiplicativeLubinTateSeries_isUniformizer p)) ())

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_MultiplicativeEvaluation_FiniteLevelEvaluation
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-level evaluation of the p-adic multiplicative comparison

This module evaluates the standard-to-multiplicative Lubin--Tate comparison
on topologically nilpotent integers in a standard finite level.  It proves
the functional equation, compatibility with scalar endomorphisms, the inverse
comparison identity, and injectivity of the evaluated comparison.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

variable {K : Type u} [Field K]

/-- The discrete coefficient uniformity used for finite-level analytic evaluation. -/
noncomputable local instance
    padicMultiplicativeLevelCoefficientUniformSpace
    (F : LocalField.{u, v} K) :
    UniformSpace F.valuationSubring :=
  ⊥

/-- The maximal-ideal adic structure on a standard finite Lubin--Tate level. -/
noncomputable local instance
    padicMultiplicativeLevelTargetWithIdeal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    WithIdeal
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring where
  i := (standardLubinTateLevelCompleteDVF hπ n).maximalIdeal

/-- Completeness of the standard finite-level valuation ring for its adic topology. -/
noncomputable local instance
    padicMultiplicativeLevelTargetCompleteSpace
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    CompleteSpace
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

/-- Separatedness of the standard finite-level valuation ring for its adic topology. -/
noncomputable local instance
    padicMultiplicativeLevelTargetT2Space
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    T2Space
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

section PadicLevelTopology

/-- The specialized level uses the same maximal-ideal adic topology as the generic evaluator. -/
noncomputable local instance
    padicMultiplicativeLevelTargetTopologicalSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    TopologicalSpace
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring :=
  @WithIdeal.instTopologicalSpace _ _
    (padicMultiplicativeLevelTargetWithIdeal
      (F := padicLocalField p)
      (π := show (padicLocalField p).valuationSubring from
        padicIntEquivValuationSubring p (p : ℤ_[p]))
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n)

/-- Evaluation of the standard-to-multiplicative comparison at the chosen
standard primitive point of level `n + 1`. -/
noncomputable def padicMultiplicativePrimitivePoint
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring :=
  standardLubinTatePrimitivePointEvaluation
    (padicMultiplicativeLubinTateSeries_isUniformizer p) n
    (padicStandardToMultiplicativeIntertwiner p)

/-- The evaluated multiplicative point is topologically nilpotent. -/
theorem padicMultiplicativePrimitivePoint_hasEval
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    PowerSeries.HasEval (padicMultiplicativePrimitivePoint p n) := by
  exact
    standardLubinTateLevelPowerSeriesEval_hasEval
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      (standardLubinTatePrimitivePointInteger
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n)
      (standardLubinTatePrimitivePointInteger_hasEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n)
      (padicStandardToMultiplicativeIntertwiner p)
      (padicStandardToMultiplicativeIntertwiner_hasSubst p)

/-- At every standard level, analytic evaluation of the multiplicative
Lubin--Tate series is the literal polynomial `(1 + x)^p - 1`. -/
theorem padicMultiplicativeLubinTateSeries_eval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
        (padicMultiplicativeLubinTateSeries p).toPowerSeries =
      (1 + x) ^ p - 1 := by
  rw [
    LubinTateSeries.padicMultiplicativeLubinTateSeries_toPowerSeries,
    PowerSeries.binomialSeries_nat (R := ℤ)]
  simp only [map_sub, map_pow, map_add, map_one]
  exact congrArg
    (fun z : (standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring =>
        (1 + z) ^ p - 1)
    (standardLubinTateLevelPowerSeriesEval_X
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx)

/-- Analytic evaluation preserves the standard-to-multiplicative
intertwining equation at every topologically nilpotent level integer. -/
theorem padicStandardToMultiplicativeIntertwiner_eval_functionalEquation
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p))
        (standardLubinTateLevelPowerSeriesEval_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p)
          (padicStandardToMultiplicativeIntertwiner_hasSubst p))
        (padicMultiplicativeLubinTateSeries p).toPowerSeries =
      standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (standardLubinTateSeries
            (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries)
        (standardLubinTateLevelPowerSeriesEval_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (standardLubinTateSeries
            (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries
          (PowerSeries.HasSubst.of_constantCoeff_zero
            (LubinTateSeries.constantCoeff_eq_zero
              (standardLubinTateSeries
                (padicMultiplicativeLubinTateSeries_isUniformizer p)))))
        (padicStandardToMultiplicativeIntertwiner p) := by
  let hπ :=
    padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let E := padicMultiplicativeLubinTateSeries p
  let Ebar := standardLubinTateSeries hπ
  let hH : PowerSeries.HasSubst H :=
    padicStandardToMultiplicativeIntertwiner_hasSubst p
  let hEbar : PowerSeries.HasSubst Ebar.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero
      Ebar.constantCoeff_eq_zero
  let hHEval :
      PowerSeries.HasEval
        (standardLubinTateLevelPowerSeriesEval hπ n x hx H) :=
    standardLubinTateLevelPowerSeriesEval_hasEval
      hπ n x hx H hH
  let hEbarEval :
      PowerSeries.HasEval
        (standardLubinTateLevelPowerSeriesEval
          hπ n x hx Ebar.toPowerSeries) :=
    standardLubinTateLevelPowerSeriesEval_hasEval
      hπ n x hx Ebar.toPowerSeries hEbar
  calc
    standardLubinTateLevelPowerSeriesEval hπ n
        (standardLubinTateLevelPowerSeriesEval hπ n x hx H)
        hHEval E.toPowerSeries =
        standardLubinTateLevelPowerSeriesEval hπ n x hx
          (PowerSeries.subst H E.toPowerSeries) :=
      (standardLubinTateLevelPowerSeriesEval_subst
        hπ n x hx H E.toPowerSeries hH hHEval).symm
    _ =
        standardLubinTateLevelPowerSeriesEval hπ n x hx
          (PowerSeries.subst Ebar.toPowerSeries H) := by
      rw [padicStandardToMultiplicativeIntertwiner_functionalEquation]
    _ =
        standardLubinTateLevelPowerSeriesEval hπ n
          (standardLubinTateLevelPowerSeriesEval
            hπ n x hx Ebar.toPowerSeries)
          hEbarEval H :=
      standardLubinTateLevelPowerSeriesEval_subst
        hπ n x hx Ebar.toPowerSeries H hEbar hEbarEval

/-- Finite-level evaluation of the comparison carries the standard scalar
action with coefficient `a` to the unique multiplicative-series scalar
action with the same coefficient. -/
theorem padicStandardToMultiplicativeIntertwiner_eval_endomorphism
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a : (padicLocalField p).valuationSubring) :
    standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateEndomorphismEvalAt
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx a)
        (standardLubinTateEndomorphismEvalAt_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx a)
        (padicStandardToMultiplicativeIntertwiner p) =
      standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p))
        (standardLubinTateLevelPowerSeriesEval_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p)
          (padicStandardToMultiplicativeIntertwiner_hasSubst p))
        (recursiveIntertwiner
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          (padicMultiplicativeLubinTateSeries p)
          (padicMultiplicativeLubinTateSeries p)
          (fun _ : Unit => a)) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let S := standardLubinTateEndomorphism hπ a
  let M :=
    recursiveIntertwiner hπ
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit => a)
  let xS := standardLubinTateEndomorphismEvalAt hπ n x hx a
  let xH := standardLubinTateLevelPowerSeriesEval hπ n x hx H
  let hSSubst : PowerSeries.HasSubst S :=
    (standardLubinTateEndomorphism_hasLinearTerm hπ a).hasSubst
  let hHSubst : PowerSeries.HasSubst H :=
    padicStandardToMultiplicativeIntertwiner_hasSubst p
  let hxS : PowerSeries.HasEval xS :=
    standardLubinTateEndomorphismEvalAt_hasEval hπ n x hx a
  let hxH : PowerSeries.HasEval xH :=
    standardLubinTateLevelPowerSeriesEval_hasEval
      hπ n x hx H hHSubst
  calc
    standardLubinTateLevelPowerSeriesEval hπ n xS hxS H =
        standardLubinTateLevelPowerSeriesEval hπ n x hx
          (PowerSeries.subst S H) :=
      (standardLubinTateLevelPowerSeriesEval_subst
        hπ n x hx S H hSSubst hxS).symm
    _ =
        standardLubinTateLevelPowerSeriesEval hπ n x hx
          (PowerSeries.subst H M) := by
      rw [padicStandardToMultiplicativeIntertwiner_endomorphism]
    _ =
        standardLubinTateLevelPowerSeriesEval hπ n xH hxH M :=
      standardLubinTateLevelPowerSeriesEval_subst
        hπ n x hx H M hHSubst hxH

/-- Evaluating the reverse comparison after the forward comparison recovers
every topologically nilpotent standard-level point. -/
theorem padicMultiplicativeToStandardIntertwiner_eval_comp
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p))
        (standardLubinTateLevelPowerSeriesEval_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p)
          (padicStandardToMultiplicativeIntertwiner_hasSubst p))
        (padicMultiplicativeToStandardIntertwiner p) =
      x := by
  let hπ :=
    padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let G := padicMultiplicativeToStandardIntertwiner p
  let hH : PowerSeries.HasSubst H :=
    padicStandardToMultiplicativeIntertwiner_hasSubst p
  let hHEval :
      PowerSeries.HasEval
        (standardLubinTateLevelPowerSeriesEval hπ n x hx H) :=
    standardLubinTateLevelPowerSeriesEval_hasEval
      hπ n x hx H hH
  calc
    standardLubinTateLevelPowerSeriesEval hπ n
        (standardLubinTateLevelPowerSeriesEval hπ n x hx H)
        hHEval G =
        standardLubinTateLevelPowerSeriesEval hπ n x hx
          (PowerSeries.subst H G) :=
      (standardLubinTateLevelPowerSeriesEval_subst
        hπ n x hx H G hH hHEval).symm
    _ =
        standardLubinTateLevelPowerSeriesEval hπ n x hx
          PowerSeries.X := by
      rw [padicMultiplicativeToStandardIntertwiner_subst_reverse]
    _ = x :=
      standardLubinTateLevelPowerSeriesEval_X
        hπ n x hx

/-- The forward comparison evaluates to zero at the zero point. -/
theorem padicStandardToMultiplicativeIntertwiner_eval_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        0 PowerSeries.HasEval.zero
        (padicStandardToMultiplicativeIntertwiner p) =
      0 := by
  obtain ⟨B, hB⟩ :
      (PowerSeries.X :
          PowerSeries (padicLocalField p).valuationSubring) ∣
        padicStandardToMultiplicativeIntertwiner p := by
    rw [PowerSeries.X_dvd_iff]
    exact
      (padicStandardToMultiplicativeIntertwiner_hasLinearTerm p
        ).constantCoeff_eq_zero
  rw [hB, map_mul]
  exact
    (congrArg
      (fun z : (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring =>
          z * standardLubinTateLevelPowerSeriesEval
            (padicMultiplicativeLubinTateSeries_isUniformizer p) n
            0 PowerSeries.HasEval.zero B)
      (standardLubinTateLevelPowerSeriesEval_X
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        0 PowerSeries.HasEval.zero)).trans (zero_mul _)

/-- Evaluation of the forward comparison is injective on topologically
nilpotent points of every standard level. -/
theorem padicStandardToMultiplicativeIntertwiner_eval_injective
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    {x y :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy :
      standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p) =
        standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n y hy
          (padicStandardToMultiplicativeIntertwiner p)) :
    x = y := by
  let hπ :=
    padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let G := padicMultiplicativeToStandardIntertwiner p
  let hxH :=
    standardLubinTateLevelPowerSeriesEval_hasEval
      hπ n x hx H
        (padicStandardToMultiplicativeIntertwiner_hasSubst p)
  let hyH :=
    standardLubinTateLevelPowerSeriesEval_hasEval
      hπ n y hy H
        (padicStandardToMultiplicativeIntertwiner_hasSubst p)
  let evalReverse :
      {z :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
        PowerSeries.HasEval z} →
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
    fun z =>
      standardLubinTateLevelPowerSeriesEval hπ n z.1 z.2 G
  let forwardX :=
    standardLubinTateLevelPowerSeriesEval hπ n x hx H
  let forwardY :=
    standardLubinTateLevelPowerSeriesEval hπ n y hy H
  let packedX :
      {z :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
        PowerSeries.HasEval z} :=
    ⟨forwardX, hxH⟩
  let packedY :
      {z :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
        PowerSeries.HasEval z} :=
    ⟨forwardY, hyH⟩
  have hpacked : packedX = packedY := by
    apply Subtype.ext
    exact hxy
  have hxback : evalReverse packedX = x :=
    padicMultiplicativeToStandardIntertwiner_eval_comp p n x hx
  have hyback : evalReverse packedY = y :=
    padicMultiplicativeToStandardIntertwiner_eval_comp p n y hy
  exact hxback.symm.trans ((congrArg evalReverse hpacked).trans hyback)

end PadicLevelTopology

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_MultiplicativeEvaluation_FiniteLevelPrimitiveRoot
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.padicValuationSubringToCompletedUnramifiedWittRing_uniformizer _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Primitive roots from finite p-adic Lubin--Tate levels

The evaluated multiplicative point yields an actual primitive
`p ^ (n + 1)`-st root of unity.  This module proves its exact order and
identifies the genuine finite-level Galois action with the cyclotomic power
action.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

variable {K : Type u} [Field K]

attribute [local instance]
  padicMultiplicativeLevelCoefficientUniformSpace
  padicMultiplicativeLevelTargetWithIdeal
  padicMultiplicativeLevelTargetTopologicalSpace
  padicMultiplicativeLevelTargetCompleteSpace
  padicMultiplicativeLevelTargetT2Space

theorem padicMultiplicativeScalarEndomorphism_nat
    (p : ℕ) [Fact p.Prime] (m : ℕ) :
    recursiveIntertwiner
        (padicMultiplicativeLubinTateSeries_isUniformizer p)
        (padicMultiplicativeLubinTateSeries p)
        (padicMultiplicativeLubinTateSeries p)
        (fun _ : Unit =>
          (m : (padicLocalField p).valuationSubring)) =
      (1 + PowerSeries.X) ^ m - 1 := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let A :
      PowerSeries (padicLocalField p).valuationSubring :=
    (1 + PowerSeries.X) ^ m - 1
  let Eps :
      PowerSeries (padicLocalField p).valuationSubring :=
    (padicMultiplicativeLubinTateSeries p).toPowerSeries
  have hEps :
      Eps =
        PowerSeries.binomialSeries
            (padicLocalField p).valuationSubring (p : ℤ) -
          1 :=
    rfl
  have hAconstant : PowerSeries.constantCoeff A = 0 := by
    simp [A]
  have hAcoeffOne :
      PowerSeries.coeff 1 A =
        (m : (padicLocalField p).valuationSubring) := by
    dsimp only [A]
    simp only [map_sub, PowerSeries.coeff_one]
    rw [PowerSeries.coeff_one_pow]
    simp
  have hAlinear :
      HasLinearTerm A
        (fun _ : Unit =>
          (m : (padicLocalField p).valuationSubring)) := by
    rw [HasLinearTerm]
    apply MvPowerSeries.nat_le_order
    intro d hd
    have hdNat : d.degree < 2 := by
      exact_mod_cast hd
    have hdegree : d.degree = d () := by
      simp [Finsupp.degree_eq_sum]
    have hd' : d () < 2 := by omega
    by_cases hd0 : d () = 0
    · have hdeq : d = 0 := by
        apply Finsupp.ext
        intro i
        cases i
        simp [hd0]
      subst d
      change
        PowerSeries.constantCoeff A -
            MvPowerSeries.constantCoeff
              (linearForm
                (fun _ : Unit =>
                  (m : (padicLocalField p).valuationSubring))) =
          0
      rw [hAconstant, constantCoeff_linearForm, sub_self]
    · have hd1 : d () = 1 := by omega
      have hdeq : d = Finsupp.single () 1 := by
        apply Finsupp.ext
        intro i
        cases i
        simp [hd1]
      subst d
      have hlinearForm :
          linearForm
              (fun _ : Unit =>
                (m : (padicLocalField p).valuationSubring)) =
            MvPowerSeries.C
                (m : (padicLocalField p).valuationSubring) *
              MvPowerSeries.X () := by
        simp [linearForm]
      change
        PowerSeries.coeff 1 A -
            MvPowerSeries.coeff (Finsupp.single () 1)
              (linearForm
                (fun _ : Unit =>
                  (m : (padicLocalField p).valuationSubring))) =
          0
      classical
      rw [hAcoeffOne, hlinearForm, MvPowerSeries.coeff_C_mul,
        MvPowerSeries.coeff_index_single_self_X, mul_one, sub_self]
  have hAsubst : PowerSeries.HasSubst A :=
    hAlinear.hasSubst
  have hEsubst :
      PowerSeries.HasSubst Eps := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero
    exact (padicMultiplicativeLubinTateSeries p).constantCoeff_eq_zero
  have hAsubstOne :
      PowerSeries.subst A
          (1 : PowerSeries (padicLocalField p).valuationSubring) =
        1 := by
    change
      PowerSeries.subst A
          (PowerSeries.C
            (1 : (padicLocalField p).valuationSubring)) =
        1
    rw [PowerSeries.subst_C]
    rfl
  have hEsubstOne :
      PowerSeries.subst Eps
          (1 : PowerSeries (padicLocalField p).valuationSubring) =
        1 := by
    change
      PowerSeries.subst Eps
          (PowerSeries.C
            (1 : (padicLocalField p).valuationSubring)) =
        1
    rw [PowerSeries.subst_C]
    rfl
  have hAone :
      1 + A = (1 + PowerSeries.X) ^ m := by
    dsimp only [A]
    ring
  have hEone :
      1 + Eps =
        (1 + PowerSeries.X) ^ p := by
    rw [hEps, PowerSeries.binomialSeries_nat (R := ℤ)]
    ring
  have hcommutes :
      PowerSeries.subst A Eps =
        PowerSeries.subst Eps A := by
    calc
      PowerSeries.subst A Eps =
          (1 + A) ^ p - 1 := by
        rw [hEps, PowerSeries.binomialSeries_nat (R := ℤ),
          PowerSeries.subst_sub hAsubst,
          PowerSeries.subst_pow hAsubst,
          PowerSeries.subst_add hAsubst,
          PowerSeries.subst_X hAsubst, hAsubstOne]
      _ = ((1 + PowerSeries.X) ^ m) ^ p - 1 := by
        rw [hAone]
      _ = (1 + PowerSeries.X) ^ (m * p) - 1 := by
        rw [← pow_mul]
      _ = (1 + PowerSeries.X) ^ (p * m) - 1 := by
        rw [mul_comm m p]
      _ = ((1 + PowerSeries.X) ^ p) ^ m - 1 := by
        rw [pow_mul]
      _ =
          (1 + Eps) ^ m - 1 := by
        rw [hEone]
      _ =
          PowerSeries.subst Eps
            ((1 +
              (PowerSeries.X :
                PowerSeries (padicLocalField p).valuationSubring)) ^ m -
              1) := by
        symm
        rw [PowerSeries.subst_sub hEsubst,
          PowerSeries.subst_pow hEsubst,
          PowerSeries.subst_add hEsubst,
          PowerSeries.subst_X hEsubst, hEsubstOne]
      _ =
          PowerSeries.subst Eps A :=
        rfl
  have hAintertwines :
      Intertwines
        (padicMultiplicativeLubinTateSeries p)
        (padicMultiplicativeLubinTateSeries p) A := by
    change
      PowerSeries.subst A Eps =
        MvPowerSeries.subst
          (fun i : Unit =>
            inVariable (padicMultiplicativeLubinTateSeries p) i) A
    calc
      PowerSeries.subst A Eps =
          PowerSeries.subst Eps A :=
        hcommutes
      _ =
          MvPowerSeries.subst
            (fun i : Unit =>
              inVariable (padicMultiplicativeLubinTateSeries p) i) A := by
        symm
        rw [PowerSeries.subst_def]
        congr 1
        funext i
        cases i
        change
          PowerSeries.subst PowerSeries.X Eps = Eps
        exact PowerSeries.X_subst Eps
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit =>
        (m : (padicLocalField p).valuationSubring))
      (recursiveIntertwiner_hasLinearTerm hπ
        (padicMultiplicativeLubinTateSeries p)
        (padicMultiplicativeLubinTateSeries p)
        (fun _ : Unit =>
          (m : (padicLocalField p).valuationSubring)))
      (recursiveIntertwiner_intertwines hπ
        (padicMultiplicativeLubinTateSeries p)
        (padicMultiplicativeLubinTateSeries p)
        (fun _ : Unit =>
          (m : (padicLocalField p).valuationSubring)))
      hAlinear hAintertwines

theorem
    padicValuationSubring_sub_toZModPow_val_mem_maximalIdeal_pow
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : (padicLocalField p).valuationSubring) :
    let z :=
      (padicIntEquivValuationSubring p).symm
        a
    let m := (PadicInt.toZModPow (p := p) (n + 1) z).val
    a - (m : (padicLocalField p).valuationSubring) ∈
      (padicLocalField p).toCompleteDVF.maximalIdeal ^ (n + 1) := by
  change (padicDVRValuation p).valuationSubring at a
  let e := padicIntEquivValuationSubring p
  let z : ℤ_[p] :=
    e.symm a
  let m := (PadicInt.toZModPow (p := p) (n + 1) z).val
  have hz :
      z - (m : ℤ_[p]) ∈
        Ideal.span ({(p : ℤ_[p]) ^ (n + 1)} : Set ℤ_[p]) := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    rw [map_sub, map_natCast]
    dsimp only [m]
    rw [ZMod.natCast_zmod_val, sub_self]
  have hzmax :
      z - (m : ℤ_[p]) ∈
        IsLocalRing.maximalIdeal ℤ_[p] ^ (n + 1) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
    exact hz
  have hmapped :
      e (z - (m : ℤ_[p])) ∈
        IsLocalRing.maximalIdeal
            (padicDVRValuation p).valuationSubring ^ (n + 1) :=
    (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
      e (n + 1) (z - (m : ℤ_[p]))).2 hzmax
  change
    a - (m : (padicDVRValuation p).valuationSubring) ∈
      IsLocalRing.maximalIdeal
          (padicDVRValuation p).valuationSubring ^ (n + 1)
  simpa only [map_sub, map_natCast, e, z, m,
    RingEquiv.apply_symm_apply] using hmapped

theorem
    padicStandardPrimitivePointIntegerAction_eq_toZModPow_val
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let m :=
      (PadicInt.toZModPow (p := p) (n + 1)
        ((padicIntEquivValuationSubring p).symm
          (u : (padicLocalField p).valuationSubring))).val
    standardLubinTatePrimitivePointIntegerAction
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n u =
      standardLubinTateEndomorphismValue
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (m : (padicLocalField p).valuationSubring) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let m :=
    (PadicInt.toZModPow (p := p) (n + 1)
      ((padicIntEquivValuationSubring p).symm
        (u : (padicLocalField p).valuationSubring))).val
  let d : (padicLocalField p).valuationSubring :=
    (u : (padicLocalField p).valuationSubring) - m
  have hd :
      d ∈ (padicLocalField p).toCompleteDVF.maximalIdeal ^ (n + 1) := by
    simpa only [d, m] using
      padicValuationSubring_sub_toZModPow_val_mem_maximalIdeal_pow p n
        (u : (padicLocalField p).valuationSubring)
  have hdzero :
      standardLubinTateEndomorphismValue hπ n d = 0 :=
    (standardLubinTateEndomorphismValue_eq_zero_iff_mem_maximalIdeal_pow
      hπ n d).2 hd
  change
    standardLubinTateEndomorphismValue hπ n
        (u : (padicLocalField p).valuationSubring) =
      standardLubinTateEndomorphismValue hπ n
        (m : (padicLocalField p).valuationSubring)
  calc
    standardLubinTateEndomorphismValue hπ n
        (u : (padicLocalField p).valuationSubring) =
        standardLubinTateEndomorphismValue hπ n
          ((m : (padicLocalField p).valuationSubring) + d) := by
      congr 1
      dsimp only [d]
      ring
    _ =
        standardLubinTateFormalAdd hπ n
          (standardLubinTateEndomorphismValue hπ n
            (m : (padicLocalField p).valuationSubring))
          (standardLubinTateEndomorphismValue hπ n d) :=
      standardLubinTateEndomorphismValue_add hπ n m d
    _ =
        standardLubinTateFormalAdd hπ n
          (standardLubinTateEndomorphismValue hπ n
            (m : (padicLocalField p).valuationSubring))
          (standardLubinTateEndomorphismValue hπ n 0) := by
      exact congrArg
        (standardLubinTateFormalAdd hπ n
          (standardLubinTateEndomorphismValue hπ n
            (m : (padicLocalField p).valuationSubring)))
        (hdzero.trans (standardLubinTateEndomorphismValue_zero hπ n).symm)
    _ =
        standardLubinTateEndomorphismValue hπ n
          ((m : (padicLocalField p).valuationSubring) + 0) :=
      (standardLubinTateEndomorphismValue_add hπ n m 0).symm
    _ =
        standardLubinTateEndomorphismValue hπ n
          (m : (padicLocalField p).valuationSubring) := by
      rw [add_zero]

theorem padicStandardLubinTateSeries_eval_iterate
    (p : ℕ) [Fact p.Prime] (n i : ℕ) :
    standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTatePrimitivePointIterateInteger
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n i)
        (standardLubinTatePrimitivePointIterateInteger_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n i)
        (standardLubinTateSeries
          (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries =
      standardLubinTatePrimitivePointIterateInteger
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n (i + 1) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let x := standardLubinTatePrimitivePointIterateInteger hπ n i
  have hpoly :
      Polynomial.eval₂ (standardLubinTateLevelCoefficientHom hπ n) x
          (standardLubinTatePolynomial (padicLocalField p) π) =
        x ^ Nat.card (padicLocalField p).residueField +
          standardLubinTateLevelCoefficientHom hπ n π * x := by
    simp only [standardLubinTatePolynomial, Polynomial.eval₂_add,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul,
      Polynomial.eval₂_C]
  rw [← standardLubinTatePolynomial_toPowerSeries_eq_series hπ]
  exact (standardLubinTateLevelPowerSeriesEval_coe hπ n x
    (standardLubinTatePrimitivePointIterateInteger_hasEval hπ n i)
    (standardLubinTatePolynomial (padicLocalField p) π)).trans
      (hpoly.trans (standardLubinTatePrimitivePointIterateInteger_succ hπ n i).symm)

theorem
    padicStandardLubinTatePrimitivePointIterateInteger_ne_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    standardLubinTatePrimitivePointIterateInteger
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n n ≠
      0 := by
  intro hzero
  have hval :=
    standardLubinTatePrimitivePointIterateInteger_addVal
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n n le_rfl
  rw [hzero, IsDiscreteValuationRing.addVal_zero] at hval
  exact ENat.top_ne_natCast _ hval

theorem padicMultiplicativePrimitivePoint_pow_primePower
    (p : ℕ) [Fact p.Prime] (n i : ℕ) :
    (1 + padicMultiplicativePrimitivePoint p n) ^ (p ^ i) =
      1 +
        standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTatePrimitivePointIterateInteger
            (padicMultiplicativeLubinTateSeries_isUniformizer p) n i)
          (standardLubinTatePrimitivePointIterateInteger_hasEval
            (padicMultiplicativeLubinTateSeries_isUniformizer p) n i)
          (padicStandardToMultiplicativeIntertwiner p) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let points :
      ℕ →
        {z :
            (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
          PowerSeries.HasEval z} :=
    fun j =>
      ⟨standardLubinTatePrimitivePointIterateInteger hπ n j,
        standardLubinTatePrimitivePointIterateInteger_hasEval hπ n j⟩
  let evalH :
      {z :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
        PowerSeries.HasEval z} →
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
    fun z =>
      standardLubinTateLevelPowerSeriesEval hπ n z.1 z.2 H
  change
    (1 + padicMultiplicativePrimitivePoint p n) ^ (p ^ i) =
      1 + evalH (points i)
  induction i with
  | zero =>
      have hpacked : points 0 =
          ⟨standardLubinTatePrimitivePointInteger hπ n,
            standardLubinTatePrimitivePointInteger_hasEval hπ n⟩ :=
        Subtype.ext (standardLubinTatePrimitivePointIterateInteger_zero hπ n)
      have heval : evalH (points 0) =
          evalH ⟨standardLubinTatePrimitivePointInteger hπ n,
            standardLubinTatePrimitivePointInteger_hasEval hπ n⟩ :=
        congrArg evalH hpacked
      have hbase :
          evalH ⟨standardLubinTatePrimitivePointInteger hπ n,
            standardLubinTatePrimitivePointInteger_hasEval hπ n⟩ =
            padicMultiplicativePrimitivePoint p n := by
        simp only [evalH, H, padicMultiplicativePrimitivePoint,
          standardLubinTatePrimitivePointEvaluation]
      simpa only [pow_zero, pow_one] using
        congrArg (fun z : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring =>
          1 + z) (heval.trans hbase).symm
  | succ i ih =>
      let Ebar := (standardLubinTateSeries hπ).toPowerSeries
      let mappedPoint :
          {z :
              (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
            PowerSeries.HasEval z} :=
        ⟨standardLubinTateLevelPowerSeriesEval hπ n
            (points i).1 (points i).2 Ebar,
          standardLubinTateLevelPowerSeriesEval_hasEval hπ n
            (points i).1 (points i).2 Ebar
            (PowerSeries.HasSubst.of_constantCoeff_zero
              (LubinTateSeries.constantCoeff_eq_zero
                (standardLubinTateSeries hπ)))⟩
      have hfunctional :=
        padicStandardToMultiplicativeIntertwiner_eval_functionalEquation
          p n (points i).1 (points i).2
      rw [padicMultiplicativeLubinTateSeries_eval] at hfunctional
      change
        (1 + evalH (points i)) ^ p - 1 =
          evalH mappedPoint at hfunctional
      have hiterate : mappedPoint.1 = (points (i + 1)).1 :=
        padicStandardLubinTateSeries_eval_iterate p n i
      have hpacked : mappedPoint = points (i + 1) :=
        Subtype.ext hiterate
      have hfunctionalClean :
          (1 + evalH (points i)) ^ p - 1 =
            evalH (points (i + 1)) :=
        hfunctional.trans (congrArg evalH hpacked)
      have hstep :
          (1 + evalH (points i)) ^ p =
            1 + evalH (points (i + 1)) := by
        calc
          _ = evalH (points (i + 1)) + 1 :=
            sub_eq_iff_eq_add.mp hfunctionalClean
          _ = _ := add_comm _ _
      calc
        (1 + padicMultiplicativePrimitivePoint p n) ^ (p ^ (i + 1)) =
            ((1 + padicMultiplicativePrimitivePoint p n) ^ (p ^ i)) ^ p := by
              rw [pow_succ, pow_mul]
        _ = (1 + evalH (points i)) ^ p := by rw [ih]
        _ = 1 + evalH (points (i + 1)) := hstep

/-- The root of unity obtained from the standard primitive Lubin--Tate
point through the multiplicative comparison.  Level `n` corresponds to
exact order `p ^ (n + 1)`. -/
noncomputable def padicMultiplicativePrimitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n :=
  1 + (padicMultiplicativePrimitivePoint p n :
    standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n)

/-- The finite Lubin--Tate unit action becomes the usual power action on
the actual primitive `p ^ (n + 1)`-st root.  The exponent is the canonical
mathlib reduction of the corresponding `p`-adic integer modulo
`p ^ (n + 1)`. This is the finite-level cyclotomic action formula. -/
theorem padicMultiplicativePrimitiveRoot_unitAction
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    1 +
        (standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTatePrimitivePointIntegerAction
            (padicMultiplicativeLubinTateSeries_isUniformizer p) n u)
          (standardLubinTatePrimitivePointIntegerAction_hasEval
            (padicMultiplicativeLubinTateSeries_isUniformizer p) n u)
          (padicStandardToMultiplicativeIntertwiner p) :
          standardLubinTateLevelField
            (padicMultiplicativeLubinTateSeries_isUniformizer p) n) =
      padicMultiplicativePrimitiveRoot p n ^
        (PadicInt.toZModPow (p := p) (n + 1)
          ((padicIntEquivValuationSubring p).symm
            (u : (padicLocalField p).valuationSubring))).val := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let m :=
    (PadicInt.toZModPow (p := p) (n + 1)
      ((padicIntEquivValuationSubring p).symm
        (u : (padicLocalField p).valuationSubring))).val
  let lambda :=
    standardLubinTatePrimitivePointInteger hπ n
  let hlambda :=
    standardLubinTatePrimitivePointInteger_hasEval hπ n
  let lambdaU :=
    standardLubinTatePrimitivePointIntegerAction hπ n u
  let hlambdaU :=
    standardLubinTatePrimitivePointIntegerAction_hasEval hπ n u
  let zetaMinusOne := padicMultiplicativePrimitivePoint p n
  let hzetaMinusOne :=
    padicMultiplicativePrimitivePoint_hasEval p n
  have hlambdaUeq :
      lambdaU =
        standardLubinTateEndomorphismValue hπ n
          (m : (padicLocalField p).valuationSubring) := by
    simpa only [lambdaU, hπ, m] using
      padicStandardPrimitivePointIntegerAction_eq_toZModPow_val p n u
  have hscalar :
      standardLubinTateLevelPowerSeriesEval hπ n
          (standardLubinTateEndomorphismValue hπ n
            (m : (padicLocalField p).valuationSubring))
          (standardLubinTateEndomorphismValue_hasEval hπ n
            (m : (padicLocalField p).valuationSubring))
          H =
        standardLubinTateLevelPowerSeriesEval hπ n
          zetaMinusOne hzetaMinusOne
          (recursiveIntertwiner hπ
            (padicMultiplicativeLubinTateSeries p)
            (padicMultiplicativeLubinTateSeries p)
            (fun _ : Unit =>
              (m : (padicLocalField p).valuationSubring))) := by
    simpa [standardLubinTateEndomorphismValue,
      padicMultiplicativePrimitivePoint,
      standardLubinTatePrimitivePointEvaluation,
      hπ, H, lambda, hlambda, zetaMinusOne, hzetaMinusOne] using
      padicStandardToMultiplicativeIntertwiner_eval_endomorphism
        p n lambda hlambda
        (m : (padicLocalField p).valuationSubring)
  have heval :
      standardLubinTateLevelPowerSeriesEval hπ n
          lambdaU hlambdaU H =
        (1 + zetaMinusOne) ^ m - 1 := by
    have eval_eq_of_point_eq
        {x y :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring}
        (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
        (hxy : x = y) :
        standardLubinTateLevelPowerSeriesEval hπ n x hx H =
          standardLubinTateLevelPowerSeriesEval hπ n y hy H := by
      subst y
      rfl
    calc
      standardLubinTateLevelPowerSeriesEval hπ n
          lambdaU hlambdaU H =
          standardLubinTateLevelPowerSeriesEval hπ n
            (standardLubinTateEndomorphismValue hπ n
              (m : (padicLocalField p).valuationSubring))
            (standardLubinTateEndomorphismValue_hasEval hπ n
              (m : (padicLocalField p).valuationSubring))
            H := by
        exact eval_eq_of_point_eq hlambdaU _ hlambdaUeq
      _ =
          standardLubinTateLevelPowerSeriesEval hπ n
            zetaMinusOne hzetaMinusOne
            (recursiveIntertwiner hπ
              (padicMultiplicativeLubinTateSeries p)
              (padicMultiplicativeLubinTateSeries p)
              (fun _ : Unit =>
                (m : (padicLocalField p).valuationSubring))) :=
        hscalar
      _ =
          standardLubinTateLevelPowerSeriesEval hπ n
            zetaMinusOne hzetaMinusOne
            ((1 + PowerSeries.X) ^ m - 1) := by
        rw [padicMultiplicativeScalarEndomorphism_nat]
      _ = (1 + zetaMinusOne) ^ m - 1 := by
        simp only [map_sub, map_pow, map_add, map_one]
        exact congrArg
          (fun z : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring =>
            (1 + z) ^ m - 1)
          (standardLubinTateLevelPowerSeriesEval_X
            hπ n zetaMinusOne hzetaMinusOne)
  have hrootInteger :
      1 +
          standardLubinTateLevelPowerSeriesEval hπ n
            lambdaU hlambdaU H =
        (1 + zetaMinusOne) ^ m := by
    rw [heval]
    ring
  have hrootField :=
    congrArg
      (fun x :
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring =>
          (x : standardLubinTateLevelField hπ n))
      hrootInteger
  simpa [padicMultiplicativePrimitiveRoot, hπ, H, m,
    lambdaU, hlambdaU, zetaMinusOne] using hrootField

theorem padicMultiplicativeLevelAlgEquiv_mem_valuationSubring_iff
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (σ : Gal((standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n) / ℚ_[p]))
    (x : standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :
    x ∈ (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuation.valuationSubring ↔
      σ x ∈ (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuation.valuationSubring := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let target := standardLubinTateLevelCompleteDVF hπ n
  let L := standardLubinTateLevelField hπ n
  let : Algebra (padicLocalField p).valuationSubring target.valuationSubring :=
    (standardLubinTateLevelCoefficientHom hπ n).toAlgebra
  let : WithIdeal target.valuationSubring :=
    padicMultiplicativeLevelTargetWithIdeal
      (F := padicLocalField p)
      (π := show (padicLocalField p).valuationSubring from
        padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  let : IsScalarTower
      (padicLocalField p).valuationSubring target.valuationSubring L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsIntegralClosure
      target.valuationSubring
      (padicLocalField p).valuationSubring L :=
    standardLubinTateLevelCompleteDVF_isIntegralClosure hπ n
  have hforward
      (τ : Gal(L / ℚ_[p])) {y : L}
      (hy : y ∈ target.valuation.valuationSubring) :
      τ y ∈ target.valuation.valuationSubring := by
    have hyIntegral :
        IsIntegral (padicLocalField p).valuationSubring y :=
      (IsIntegralClosure.isIntegral_iff
        (A := target.valuationSubring)
        (R := (padicLocalField p).valuationSubring)
        (B := L)).2
          ⟨⟨y, hy⟩, rfl⟩
    have hτIntegral :
        IsIntegral (padicLocalField p).valuationSubring (τ y) :=
      IsIntegral.map τ.toAlgHom hyIntegral
    rcases
        (IsIntegralClosure.isIntegral_iff
          (A := target.valuationSubring)
          (R := (padicLocalField p).valuationSubring)
          (B := L)).1 hτIntegral
      with ⟨z, hz⟩
    exact hz ▸ z.property
  constructor
  · exact hforward σ
  · intro hσx
    have hback := hforward σ.symm hσx
    simpa using hback

noncomputable def
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (σ : Gal((standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n) / ℚ_[p])) :
    (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring ≃+*
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring :=
  higherPrincipalUnitGroup.valuationSubringRingEquivOfPreserves
    (standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n)
    σ.toRingEquiv
    (padicMultiplicativeLevelAlgEquiv_mem_valuationSubring_iff p n σ)

@[simp]
theorem
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (σ : Gal((standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n) / ℚ_[p]))
    (x : (standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring) :
    ((padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n σ x :
        (standardLubinTateLevelCompleteDVF
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring) :
      standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) =
      σ (x : standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :=
  rfl

theorem
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv_continuous
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (σ : Gal((standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n) / ℚ_[p])) :
    Continuous (padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n σ) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let target := standardLubinTateLevelCompleteDVF hπ n
  let : WithIdeal target.valuationSubring :=
    padicMultiplicativeLevelTargetWithIdeal
      (F := padicLocalField p)
      (π := show (padicLocalField p).valuationSubring from
        padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  let r := padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n σ
  apply continuous_of_continuousAt_zero r
  rw [ContinuousAt, map_zero]
  have hadic : IsAdic target.maximalIdeal := rfl
  apply (hadic.hasBasis_nhds_zero.tendsto_right_iff).2
  intro m _
  apply (hadic.hasBasis_nhds_zero.mem_iff).2
  refine ⟨m, trivial, ?_⟩
  intro x hx
  exact
    (higherPrincipalUnitGroup.valuationSubringRingEquivOfPreserves_mem_maximalIdeal_pow_iff
      target σ.toRingEquiv
      (padicMultiplicativeLevelAlgEquiv_mem_valuationSubring_iff p n σ)
      m x).2 hx

theorem
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv_comp_coefficientHom
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (σ : Gal((standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n) / ℚ_[p])) :
    (padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n σ :
        (standardLubinTateLevelCompleteDVF
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring →+*
        (standardLubinTateLevelCompleteDVF
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring).comp
      (standardLubinTateLevelCoefficientHom
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) =
      standardLubinTateLevelCoefficientHom
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n := by
  ext a : 1
  apply Subtype.ext
  simp only [RingHom.comp_apply]
  exact σ.commutes (a : ℚ_[p])

theorem
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv_primitivePointEvaluation
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n
        ((standardLubinTateUnitParameterEquivGal
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u))⁻¹)
        (padicMultiplicativePrimitivePoint p n) =
      standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTatePrimitivePointIntegerAction
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n u⁻¹)
        (standardLubinTatePrimitivePointIntegerAction_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n u⁻¹)
        (padicStandardToMultiplicativeIntertwiner p) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let target := standardLubinTateLevelCompleteDVF hπ n
  let L := standardLubinTateLevelField hπ n
  let σ : Gal(L / ℚ_[p]) :=
    (standardLubinTateUnitParameterEquivGal
      (padicLocalField p) hπ n
      (standardLubinTateUnitParameterClass
        (padicLocalField p) n u))⁻¹
  let r := padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n σ
  let H := padicStandardToMultiplicativeIntertwiner p
  let lambda := standardLubinTatePrimitivePointInteger hπ n
  let lambdaInv := standardLubinTatePrimitivePointIntegerAction hπ n u⁻¹
  let hlambdaInv :=
    standardLubinTatePrimitivePointIntegerAction_hasEval hπ n u⁻¹
  let zetaMinusOne := padicMultiplicativePrimitivePoint p n
  let : WithIdeal target.valuationSubring :=
    padicMultiplicativeLevelTargetWithIdeal
      (F := padicLocalField p)
      (π := show (padicLocalField p).valuationSubring from
        padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  letI : UniformSpace target.valuationSubring :=
    WithIdeal.instUniformSpace target.valuationSubring
  have hrLambda : r lambda = lambdaInv := by
    apply Subtype.ext
    rw [padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply]
    change
      σ (standardLubinTateLevelGenerator hπ n) =
        standardLubinTatePrimitiveLevelAction hπ n u⁻¹
    simpa only [σ, standardLubinTateLevelGenerator] using
      standardLubinTateUnitParameterEquivGal_inv_class_apply_gen
        (padicLocalField p) hπ n u
  have hcoeffContinuous :
      @Continuous
        (padicLocalField p).valuationSubring
        target.valuationSubring
        (padicMultiplicativeLevelCoefficientUniformSpace
          (padicLocalField p)).toTopologicalSpace
        (inferInstance : UniformSpace target.valuationSubring).toTopologicalSpace
        (standardLubinTateLevelCoefficientHom hπ n) := by
    change @Continuous
      (padicLocalField p).valuationSubring target.valuationSubring ⊥ _ _
    exact
      @continuous_of_discreteTopology
        (padicLocalField p).valuationSubring
        ⊥
        (discreteTopology_bot (padicLocalField p).valuationSubring)
        target.valuationSubring
        _
        (standardLubinTateLevelCoefficientHom hπ n)
  let : T2Space target.valuationSubring :=
    padicMultiplicativeLevelTargetT2Space
      (F := padicLocalField p)
      (π := show (padicLocalField p).valuationSubring from
        padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  let : CompleteSpace target.valuationSubring :=
    padicMultiplicativeLevelTargetCompleteSpace
      (F := padicLocalField p)
      (π := show (padicLocalField p).valuationSubring from
        padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  have hcomp :=
    PowerSeries.comp_eval₂
      (R := (padicLocalField p).valuationSubring)
      (S := target.valuationSubring)
      (φ := standardLubinTateLevelCoefficientHom hπ n)
      (a := lambda)
      hcoeffContinuous
      (standardLubinTatePrimitivePointInteger_hasEval hπ n)
      (ε := (r : target.valuationSubring →+* target.valuationSubring))
      (padicMultiplicativeLevelAutomorphismIntegerRingEquiv_continuous p n σ)
  have happ := congrArg (fun f => f H) hcomp
  rw [padicMultiplicativeLevelAutomorphismIntegerRingEquiv_comp_coefficientHom
    p n σ] at happ
  have hrLambdaRing :
      (r : target.valuationSubring →+* target.valuationSubring) lambda =
        lambdaInv :=
    hrLambda
  rw [hrLambdaRing] at happ
  change
    r zetaMinusOne =
      standardLubinTateLevelPowerSeriesEval hπ n lambdaInv hlambdaInv H
  simpa [zetaMinusOne, padicMultiplicativePrimitivePoint,
    standardLubinTatePrimitivePointEvaluation,
    standardLubinTateLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom, Function.comp_apply,
    target, lambda, H] using happ

/-- For the finite Galois element supplied by the Lubin--Tate unit
parameter, the inverse automorphism acts on the actual primitive
`p ^ (n + 1)`-st root by the inverse unit exponent modulo `p ^ (n + 1)`.
This is the explicit cyclotomic norm-residue formula. -/
theorem padicMultiplicativePrimitiveRoot_galoisAction
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    (standardLubinTateUnitParameterEquivGal
        (padicLocalField p)
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u))⁻¹
        (padicMultiplicativePrimitiveRoot p n) =
      padicMultiplicativePrimitiveRoot p n ^
        (PadicInt.toZModPow (p := p) (n + 1)
          ((padicIntEquivValuationSubring p).symm
            ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
              (padicLocalField p).valuationSubring))).val := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let target := standardLubinTateLevelCompleteDVF hπ n
  let L := standardLubinTateLevelField hπ n
  let σ : Gal(L / ℚ_[p]) :=
    (standardLubinTateUnitParameterEquivGal
      (padicLocalField p) hπ n
      (standardLubinTateUnitParameterClass
        (padicLocalField p) n u))⁻¹
  let r := padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n σ
  let H := padicStandardToMultiplicativeIntertwiner p
  let lambdaInv :=
    standardLubinTatePrimitivePointIntegerAction hπ n u⁻¹
  let hlambdaInv :=
    standardLubinTatePrimitivePointIntegerAction_hasEval hπ n u⁻¹
  let zetaMinusOne := padicMultiplicativePrimitivePoint p n
  have hσOneAdd (x : L) : σ (1 + x) = 1 + σ x := by
    calc
      σ (1 + x) = σ 1 + σ x := σ.map_add 1 x
      _ = 1 + σ x := congrArg (fun y : L => y + σ x) σ.map_one
  have hrApply (x : target.valuationSubring) :
      ((r x : target.valuationSubring) : L) =
        σ (x : L) :=
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply p n σ x
  have hrEval :
      r zetaMinusOne =
        standardLubinTateLevelPowerSeriesEval hπ n
          lambdaInv hlambdaInv H := by
    exact
      padicMultiplicativeLevelAutomorphismIntegerRingEquiv_primitivePointEvaluation
        p n u
  change
    σ (padicMultiplicativePrimitiveRoot p n) =
      padicMultiplicativePrimitiveRoot p n ^
        (PadicInt.toZModPow (p := p) (n + 1)
          ((padicIntEquivValuationSubring p).symm
            ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
              (padicLocalField p).valuationSubring))).val
  calc
    σ (padicMultiplicativePrimitiveRoot p n) =
        σ (1 + (zetaMinusOne : L)) := by
      rfl
    _ = 1 + σ (zetaMinusOne : L) :=
      hσOneAdd (zetaMinusOne : L)
    _ = 1 + (r zetaMinusOne : L) := by
      rw [hrApply]
    _ =
        1 +
          (standardLubinTateLevelPowerSeriesEval hπ n
            lambdaInv hlambdaInv H : L) := by
      rw [hrEval]
    _ =
        padicMultiplicativePrimitiveRoot p n ^
          (PadicInt.toZModPow (p := p) (n + 1)
            ((padicIntEquivValuationSubring p).symm
              ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
                (padicLocalField p).valuationSubring))).val := by
      simpa only [hπ, H, lambdaInv, hlambdaInv] using
        padicMultiplicativePrimitiveRoot_unitAction p n u⁻¹

/-- The finite Lubin--Tate parameter automorphism itself acts on the
genuine primitive `p ^ (n + 1)`-st root by the direct unit exponent.

This is the direct-orientation companion to
`padicMultiplicativePrimitiveRoot_galoisAction`: applying that theorem
to the inverse unit cancels both inversions. -/
theorem padicMultiplicativePrimitiveRoot_unitParameterGaloisAction
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    standardLubinTateUnitParameterEquivGal
        (padicLocalField p)
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u)
        (padicMultiplicativePrimitiveRoot p n) =
      padicMultiplicativePrimitiveRoot p n ^
        (PadicInt.toZModPow (p := p) (n + 1)
          ((padicIntEquivValuationSubring p).symm
            ((u : (padicLocalField p).valuationSubringˣ) :
              (padicLocalField p).valuationSubring))).val := by
  simpa only [map_inv, inv_inv] using
    padicMultiplicativePrimitiveRoot_galoisAction p n u⁻¹

/-- The multiplicative comparison identifies the standard level-`n`
Lubin--Tate generator with a primitive `p ^ (n + 1)`-st root of unity. -/
theorem padicMultiplicativePrimitiveRoot_isPrimitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsPrimitiveRoot (padicMultiplicativePrimitiveRoot p n) (p ^ (n + 1)) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let iteratePoint :=
    standardLubinTatePrimitivePointIterateInteger hπ n
  have hfinalInteger :
      (1 + padicMultiplicativePrimitivePoint p n) ^ (p ^ (n + 1)) = 1 := by
    have hpow :=
      padicMultiplicativePrimitivePoint_pow_primePower p n (n + 1)
    have hevalZero :
        standardLubinTateLevelPowerSeriesEval hπ n
            (iteratePoint (n + 1))
            (standardLubinTatePrimitivePointIterateInteger_hasEval
              hπ n (n + 1)) H =
          0 := by
      have hpoint :
          iteratePoint (n + 1) = 0 := by
        simpa only [iteratePoint,
          standardLubinTatePrimitivePointIterateInteger,
          standardLubinTateLevelCoefficientHom] using
          standardLubinTatePrimitivePointInteger_iterate_succ_eq_zero hπ n
      let evalForward :
          {z :
              (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
            PowerSeries.HasEval z} →
            (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
        fun z =>
          standardLubinTateLevelPowerSeriesEval hπ n z.1 z.2 H
      have hpacked :
          (⟨iteratePoint (n + 1),
              standardLubinTatePrimitivePointIterateInteger_hasEval
                hπ n (n + 1)⟩ :
              {z :
                  (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
                PowerSeries.HasEval z}) =
            ⟨0, PowerSeries.HasEval.zero⟩ :=
        Subtype.ext hpoint
      exact
        (congrArg evalForward hpacked).trans
          (padicStandardToMultiplicativeIntertwiner_eval_zero p n)
    calc
      _ = 1 +
          standardLubinTateLevelPowerSeriesEval hπ n
            (iteratePoint (n + 1))
            (standardLubinTatePrimitivePointIterateInteger_hasEval
              hπ n (n + 1)) H := hpow
      _ = 1 := by rw [hevalZero, add_zero]
  have hfinal :
      padicMultiplicativePrimitiveRoot p n ^ (p ^ (n + 1)) = 1 := by
    simpa [padicMultiplicativePrimitiveRoot] using
      congrArg
        (fun z :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring =>
            (z : standardLubinTateLevelField hπ n))
        hfinalInteger
  have hprevious :
      ¬padicMultiplicativePrimitiveRoot p n ^ (p ^ n) = 1 := by
    intro hpower
    have hpowerInteger :
        (1 + padicMultiplicativePrimitivePoint p n) ^ (p ^ n) = 1 := by
      apply Subtype.ext
      simpa [padicMultiplicativePrimitiveRoot] using hpower
    have hiterateEvaluation :
        standardLubinTateLevelPowerSeriesEval hπ n (iteratePoint n)
            (standardLubinTatePrimitivePointIterateInteger_hasEval hπ n n) H =
          0 := by
      have hpow :=
        padicMultiplicativePrimitivePoint_pow_primePower p n n
      rw [hpowerInteger] at hpow
      have hsub := congrArg
        (fun z :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring =>
            z - 1)
        hpow
      simpa using hsub.symm
    have hiterateZero : iteratePoint n = 0 := by
      apply padicStandardToMultiplicativeIntertwiner_eval_injective
        p n
        (standardLubinTatePrimitivePointIterateInteger_hasEval hπ n n)
        PowerSeries.HasEval.zero
      simpa [H, padicStandardToMultiplicativeIntertwiner_eval_zero] using
        hiterateEvaluation
    exact
      padicStandardLubinTatePrimitivePointIterateInteger_ne_zero p n
        hiterateZero
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_eq_prime_pow hprevious hfinal

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionRatAlgebra
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
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_rb40e56_1
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsNonarchimedeanLocalField
/-- The completion-to-`ℚ_q` equivalence respects the rational embedding. -/
theorem rationalFinitePlaceCompletionRingEquivPadic_algebraMap
    (q : Nat.Primes) (a : ℚ) :
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion a) =
      algebraMap ℚ ℚ_[q.1] a := by
  exact
    (rationalFinitePlaceCompletionRingEquivPadic q).toRingHom.map_rat_algebraMap a

/-- The completion field equivalence and its restriction to valuation
rings commute with the natural inclusions into the fields. -/
theorem rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe
    (q : Nat.Primes)
    (a :
      𝒪[(HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion]) :
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion a) =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q a) := by
  exact
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap
      (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q) a)

/-- The rational prime, pulled back from `ℤ_q` to the valuation ring of
the absolute-value completion at `q`. -/
noncomputable def rationalPrimeFinitePlaceInteger
    (q : Nat.Primes) :
    𝒪[(HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion] :=
  (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).symm
    (q.1 : ℤ_[q.1])

/-- The pulled-back rational prime is irreducible in the completion
valuation ring. -/
theorem rationalPrimeFinitePlaceInteger_irreducible
    (q : Nat.Primes) :
    Irreducible (rationalPrimeFinitePlaceInteger q) := by
  exact
    (MulEquiv.irreducible_iff
      (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
        q).symm.toMulEquiv).2
      ((PadicInt.prime_p :
        Prime (q.1 : ℤ_[q.1])).irreducible)

/-- Coercing the pulled-back prime to the completion field gives the
ordinary image of the rational number `q`. -/
theorem rationalPrimeFinitePlaceInteger_coe
    (q : Nat.Primes) :
    ((rationalPrimeFinitePlaceInteger q :
      𝒪[(HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion]) :
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion) =
      algebraMap ℚ
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (q.1 : ℚ) := by
  apply
    (rationalFinitePlaceCompletionRingEquivPadic q).injective
  change
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeFinitePlaceInteger q)) =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (q.1 : ℚ))
  calc
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeFinitePlaceInteger q)) =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
          (rationalPrimeFinitePlaceInteger q)) :=
        rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe
          q (rationalPrimeFinitePlaceInteger q)
    _ = (q.1 : ℚ_[q.1]) := by
      rw [rationalPrimeFinitePlaceInteger,
        (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
          q).apply_symm_apply,
        PadicInt.algebraMap_apply,
        PadicInt.coe_natCast]
    _ =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (q.1 : ℚ)) := by
      rw [
        rationalFinitePlaceCompletionRingEquivPadic_algebraMap]
      norm_num

/-- The rational prime as a field unit of its absolute-value completion. -/
noncomputable def rationalPrimeFinitePlaceFieldUnit
    (q : Nat.Primes) :
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completionˣ :=
  Units.mk0
    (rationalPrimeFinitePlaceInteger q :
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion)
    (by
      intro hzero
      exact
        (rationalPrimeFinitePlaceInteger_irreducible q).ne_zero
          (Subtype.ext hzero))

/-- In the inverse-standard local reciprocity normalization, the rational
prime itself has normalized additive value `-1`. -/
theorem rationalPrimeFinitePlaceFieldUnit_valuationMap
    (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          (rationalPrimeFinitePlaceFieldUnit q)) =
      -1 := by
  simpa [IsNonarchimedeanLocalField.valuationMap_apply] using
    (LocalFieldTheory.v_integerRingIrreducibleFieldUnit
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion
      (rationalPrimeFinitePlaceInteger q)
      (rationalPrimeFinitePlaceInteger_irreducible q)
      (rationalPrimeFinitePlaceFieldUnit q) rfl)

/-- The rational `q`-unit part of `x`, pulled back from `ℤ_qˣ` to the
valuation ring of the absolute-value completion. -/
noncomputable def rationalPrimeUnitFinitePlaceIntegerUnit
    (x : ℚˣ) (q : Nat.Primes) :
    𝒪[(HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion]ˣ :=
  Units.map
      (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
        q).symm.toMonoidHom
    (padicIntUnitOfRat q
      (rationalPrimeUnit x q : ℚ)
      (rationalPrimeUnit x q).ne_zero
      (padicValRat_rationalPrimeUnit x q))

/-- Forgetting the integrality proof from the pulled-back `q`-unit gives
the ordinary image of the rational `q`-unit in the completion field. -/
theorem rationalPrimeUnitFinitePlaceIntegerUnit_coe
    (x : ℚˣ) (q : Nat.Primes) :
    (((rationalPrimeUnitFinitePlaceIntegerUnit x q :
        𝒪[(HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion]ˣ) :
        𝒪[(HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion]) :
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion) =
      algebraMap ℚ
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (rationalPrimeUnit x q : ℚ) := by
  apply
    (rationalFinitePlaceCompletionRingEquivPadic q).injective
  change
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
            𝒪[(HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion])) =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeUnit x q : ℚ))
  calc
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion])) =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
            𝒪[(HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion])) :=
        rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe q
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
            𝒪[(HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion])
    _ =
      ((padicIntUnitOfRat q
        (rationalPrimeUnit x q : ℚ)
        (rationalPrimeUnit x q).ne_zero
        (padicValRat_rationalPrimeUnit x q) :
          ℤ_[q.1]) : ℚ_[q.1]) := by
      rw [rationalPrimeUnitFinitePlaceIntegerUnit]
      simp [PadicInt.algebraMap_apply]
    _ = ((rationalPrimeUnit x q : ℚ) : ℚ_[q.1]) := by
      rw [padicIntUnitOfRat_coe]
    _ =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeUnit x q : ℚ)) := by
      rw [
        rationalFinitePlaceCompletionRingEquivPadic_algebraMap]
      simp

/-- The completion field unit underlying the pulled-back rational `q`-unit
has normalized additive value zero. -/
theorem rationalPrimeUnitFinitePlaceField_valuationMap
    (x : ℚˣ) (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          (IsNonarchimedeanLocalField.integerUnitsToFieldUnits
            (HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion
            (rationalPrimeUnitFinitePlaceIntegerUnit x q))) =
      0 := by
  rw [IsNonarchimedeanLocalField.valuationMap_apply]
  exact
    IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion
      (rationalPrimeUnitFinitePlaceIntegerUnit x q)

/-- Reattaching the removed `q`-power to the rational `q`-unit recovers
the original rational field unit. -/
theorem rationalPrimeGeneratorUnit_zpow_mul_rationalPrimeUnit
    (x : ℚˣ) (q : Nat.Primes) :
    rationalPrimeGeneratorUnit q ^
          padicValRat q.1 (x : ℚ) *
        rationalPrimeUnit x q =
      x := by
  rw [rationalPrimeGeneratorUnit, rationalPrimeUnit,
    ← mul_assoc, ← zpow_add]
  simp

end Reciprocity
end GlobalClassFieldTheory
end
end


