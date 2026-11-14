-- Prove2me | Definitions.Def_OAIQ244Duke076
-- name    : OAIQ244Duke076
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T23:07:12.942297+00:00
-- url     : https://prove2.me/theorems/e2fd7d44-457d-4c37-a0b2-139653579833
-- title:
--   Definitions bundle OAIQ244Duke076 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 5 definitions and 32 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedEquivCompletion`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIntegerAlgebra`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValued`, `LocalClassFieldTheory.extensionQuotientEquivOfEq`, `LocalClassFieldTheory.fixedFieldFiniteNormQuotientEquivNormQuotient`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_OnePlaceNormKernel`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalAwayProduct`, `LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityPrimeNorm`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_BaseComparison_FixedFieldNormQuotient`, `LocalClassFieldTheory_Finite_LocalReciprocity_Main`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormalization`, `LocalField_DiscreteValuationField_PadicValuationComparison`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke069`, `OAIQ244Duke070`, `OAIQ244Duke071` and `OAIQ244Duke072` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke082` and `OAIQ244Duke114`.
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
import Definitions.Def_OAIQ244Duke069
import Definitions.Def_OAIQ244Duke070
import Definitions.Def_OAIQ244Duke071
import Definitions.Def_OAIQ244Duke072

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_Main
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open LocalFieldTheory

/-!
# Finite local reciprocity: the local reciprocity law

The residue Frobenius datum, the normalized henselian valuation, and the
class-field axiom constructed over the fixed separable closure are inserted
into the abstract reciprocity theorem.  The resulting isomorphism is independent of the
embedding used to realize the finite Galois extension in that closure.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L]

/-- The local norm-residue symbol of the finite local reciprocity construction is surjective. -/
theorem localArtinMonoidHom_surjective :
    Function.Surjective (localArtinMonoidHom K L) :=
  (abelianizationEquivNormQuotient K L).symm.surjective.comp
    (QuotientGroup.mk'_surjective (localNormSubgroup K L))

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_OnePlaceNormKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
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

omit [NumberField L] in
/-- The finite-place tensor form with the actual chosen completion
norm group. -/
theorem finitePlaceIdele_mem_ideleNormSubgroup_iff_chosenLocalNorm
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    finitePlaceIdele v x ∈
        ideleNormSubgroup (K := K) (L := L) ↔
      x ∈ chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  rw [finitePlaceIdele_mem_ideleNormSubgroup_iff
    (K := K) (L := L)]
  exact SetLike.ext_iff.mp
    (finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup
      (K := K) (L := L) v) x

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityPrimeNorm
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Concrete prime-norm evaluation

The abstract prime-norm formula is transported through an explicit
separable-closure realization. The resulting concrete norm-residue symbol
sends the transported base-field norm to the represented Galois automorphism.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable (i : L →ₐ[K] SeparableClosure K)

local notation "Eᵢ" => finiteGaloisAbstractExtensionOfEmbedding K L i

/-- The concrete local norm-residue symbol evaluated on the norm of a prime
element in the fixed field of a positive Frobenius lift.

The hypothesis on `x` identifies its image in the base fixed coefficient
group with the abstract relative norm, so the statement is independent of a
particular presentation of that norm. The right side is the abelianization
class of the actual `K`-automorphism of `L` represented by `q`. -/
theorem concreteNormResidueSymbolOfEmbedding_apply_primeNorm
    (D : DegreeData (intrinsicAbsoluteGalois K)) (v : ValuationData D (intrinsicAbsoluteUnits K))
    (hcf : SatisfiesClassFieldAxiom (intrinsicAbsoluteUnits K))
    (q : (Eᵢ).extensionQuotient)
    (sigma : D.FrobeniusElements
      ((intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField D) (Eᵢ).field (Eᵢ).below)
    (hsigma : D.frobeniusRestriction
      ((intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField D) (Eᵢ).field (Eᵢ).below sigma = q)
    (pi : ambientFixedAddSubgroup (intrinsicAbsoluteUnits K)
      (D.frobeniusFixedField ((intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField D)
        (Eᵢ).field (Eᵢ).below sigma))
    (hpi :
      letI : Finite ((intrinsicFiniteAbstractBase K).field.toSubgroup ⧸
          extensionSubgroup (intrinsicFiniteAbstractBase K).field (Eᵢ).field (Eᵢ).below) := by
        change Finite ((intrinsicAbstractBase K).toSubgroup ⧸
          extensionSubgroup (intrinsicAbstractBase K) (Eᵢ).field (Eᵢ).below)
        exact (Eᵢ).finite
      let KR := (intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField D
      let S := D.frobeniusFixedField KR (Eᵢ).field (Eᵢ).below sigma
      letI : Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
          extensionSubgroup (baseField (intrinsicAbsoluteGalois K)) S (le_baseField S)) :=
        D.frobeniusFixedField_absoluteFinite
          (intrinsicFiniteAbstractBase K) (Eᵢ).field (Eᵢ).below sigma
      let Sigma : FiniteAbstractField (intrinsicAbsoluteGalois K) := ⟨S, inferInstance⟩
      v.IsPrimeElement Sigma pi)
    (x : Kˣ)
    (hx :
      let KR := (intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField D
      let S := D.frobeniusFixedField KR (Eᵢ).field (Eᵢ).below sigma
      let hSB := D.frobeniusFixedField_le KR (Eᵢ).field (Eᵢ).below sigma
      letI : Finite ((intrinsicAbstractBase K).toSubgroup ⧸
          extensionSubgroup (intrinsicAbstractBase K) S hSB) :=
        D.frobeniusFixedField_finite
          KR (Eᵢ).field (Eᵢ).below sigma
      baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul x) =
        relativeNorm
          (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K) S hSB pi) :
    concreteNormResidueSymbolOfEmbedding K L i D v hcf x =
      Abelianization.of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q) := by
  dsimp only at hx
  let BK := intrinsicFiniteAbstractBase K
  let hEfinite : Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) (Eᵢ).field (Eᵢ).below) :=
    (Eᵢ).finite
  let hBKEfinite : Finite (BK.field.toSubgroup ⧸
      extensionSubgroup BK.field (Eᵢ).field (Eᵢ).below) := by
    change Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) (Eᵢ).field (Eᵢ).below)
    exact hEfinite
  let KR := BK.toFiniteResidueAbstractField D
  let S := D.frobeniusFixedField KR (Eᵢ).field (Eᵢ).below sigma
  let hSB := D.frobeniusFixedField_le
    KR (Eᵢ).field (Eᵢ).below sigma
  let hSBfinite : Finite ((intrinsicAbstractBase K).toSubgroup ⧸
      extensionSubgroup (intrinsicAbstractBase K) S hSB) :=
    D.frobeniusFixedField_finite
      KR (Eᵢ).field (Eᵢ).below sigma
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  let a := relativeNorm (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K) S hSB pi
  have hbase : e (Additive.ofMul x) = a := by
    simpa only [BK, KR, S, hSB, e, a] using hx
  have hprimeNorm :
      D.finiteReciprocityHom (intrinsicAbsoluteUnits K) v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
          BK (Eᵢ).field (Eᵢ).below (Additive.ofMul q) =
        finiteNormClass (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K) (Eᵢ).field (Eᵢ).below a := by
    simpa only [BK, KR, S, hSB, a] using
      D.finiteReciprocityHom_apply_eq_primeNormClass
        (intrinsicAbsoluteUnits K) v (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
        BK (Eᵢ).field (Eᵢ).below
        (Additive.ofMul q) sigma hsigma pi hpi
  have hreciprocity :
      D.abstractReciprocityEquiv (intrinsicAbsoluteUnits K) v hcf BK Eᵢ
          (Additive.ofMul (Abelianization.of q)) =
        finiteNormClass (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K) (Eᵢ).field (Eᵢ).below a := by
    rw [D.abstractReciprocityEquiv_apply_of (intrinsicAbsoluteUnits K) v hcf BK Eᵢ q]
    exact hprimeNorm
  have hnormTransport :
      finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L i
          (finiteNormClass (intrinsicAbsoluteUnits K) (intrinsicAbstractBase K) (Eᵢ).field (Eᵢ).below a) =
        Additive.ofMul (normClass K L x) := by
    rw [← hbase]
    convert
      finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit
        K L i x using 1 <;>
      rfl
  have hsource :
      MulEquiv.toAdditive
          ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
            K L i).abelianizationCongr.symm)
          (Additive.ofMul (Abelianization.of
            (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q))) =
        Additive.ofMul (Abelianization.of q) := by
    change
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K L i).abelianizationCongr.symm
          (Abelianization.of
            (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q)) =
        Abelianization.of q
    rw [← abelianizationCongr_of
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i) q]
    exact
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        K L i).abelianizationCongr.symm_apply_apply _
  have hforward :
      concreteReciprocityAddEquivOfEmbedding K L i D v hcf
          (Additive.ofMul (Abelianization.of
            (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q))) =
        Additive.ofMul (normClass K L x) := by
    change
      finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L i
          (D.abstractReciprocityEquiv (intrinsicAbsoluteUnits K) v hcf BK Eᵢ
            (MulEquiv.toAdditive
              ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
                K L i).abelianizationCongr.symm)
              (Additive.ofMul (Abelianization.of
                (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
                  K L i q))))) =
        Additive.ofMul (normClass K L x)
    rw [hsource, hreciprocity, hnormTransport]
  change
    (concreteReciprocityEquivOfEmbedding K L i D v hcf).symm
        (normClass K L x) =
      Abelianization.of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q)
  apply (concreteReciprocityEquivOfEmbedding K L i D v hcf).injective
  rw [(concreteReciprocityEquivOfEmbedding K L i D v hcf).apply_symm_apply]
  exact (congrArg Additive.toMul hforward).symm

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Abstract and concrete unramified Frobenius

This module compares the residue-degree construction on a fixed separable
closure with the ordinary unramified valuation extension and its arithmetic
Frobenius.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open RamificationTheory.HilbertRamification.ValuationSubring


section BaseFrobeniusLift

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem abstractBaseFrobeniusLift_normalizedDegree :
    (localResidueDatum K).normalizedDegree
        (finiteResidueAbstractBase K)
        (abstractBaseFrobeniusLift K) =
      Multiplicative.ofAdd (1 : ZHat) :=
  Classical.choose_spec
    ((localResidueDatum K).normalizedDegree_surjective
      (finiteResidueAbstractBase K)
      (Multiplicative.ofAdd (1 : ZHat)))

theorem abstractBaseFrobeniusLift_degree :
    localResidueDegree K (abstractBaseFrobeniusLift K).1 =
      Multiplicative.ofAdd (1 : ZHat) := by
  apply Multiplicative.ext
  have h :=
    (localResidueDatum K).residueDegree_nsmul_normalizedDegree
      (finiteResidueAbstractBase K)
      (abstractBaseFrobeniusLift K)
  rw [finiteResidueAbstractBase_residueDegree_eq_one K, one_nsmul,
    abstractBaseFrobeniusLift_normalizedDegree K] at h
  exact h.symm

end BaseFrobeniusLift

section

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]

variable
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]

variable (i : L →ₐ[K] SeparableClosure K)

omit [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] in
/-- The concrete residue action is the restriction of the selected absolute
residue action along the chosen finite Galois embedding. -/
theorem finiteGaloisResidueEmbeddingOfEmbedding_equivariant
    (τ : (abstractBase_p1 K).toSubgroup) (x : 𝓀[L]) :
    finiteGaloisResidueEmbeddingOfEmbedding K L i
        (galoisGroupResidueAlgEquivOfIsIntegralClosure K L
          (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
            (QuotientGroup.mk τ)) x) =
      localSeparableResidueAlgAction K τ.1
        (finiteGaloisResidueEmbeddingOfEmbedding K L i x) := by
  let A := localSeparableValuationSubring K
  let σ : Gal(L / K) :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
      (QuotientGroup.mk τ)
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  let jO : 𝒪[L] → A := fun y =>
    ⟨i (y : L), by
      have hy : (y : L) ∈ A.comap i.toRingHom := by
        rw [localSeparableValuationSubring_comap_embedding K L i]
        exact y.property
      exact hy⟩
  let σa : 𝒪[L] :=
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ a
  let aA : A := jO a
  let σaA : A := jO σa
  let τD : decompositionGroup K A :=
    toDecompositionGroupOfEqTop K A
      (localSeparableDecompositionGroup_eq_top K) τ.1
  have hσaA : σaA = τD • aA := by
    apply Subtype.ext
    exact finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
      K L i τ (a : L)
  calc
    finiteGaloisResidueEmbeddingOfEmbedding K L i
        (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ
          (IsLocalRing.residue 𝒪[L] a)) =
      finiteGaloisResidueEmbeddingOfEmbedding K L i
        (IsLocalRing.residue 𝒪[L] σa) := by
          congr 1
    _ = IsLocalRing.residue A σaA := by
      simpa only [jO, σaA] using
        finiteGaloisResidueEmbeddingOfEmbedding_residue K L i σa
    _ = IsLocalRing.residue A (τD • aA) := by rw [hσaA]
    _ = localSeparableResidueAlgAction K τ.1
        (IsLocalRing.residue A aA) := by
      change IsLocalRing.residue A (τD • aA) =
        residueAlgActionOfEqTop K A
          (localSeparableDecompositionGroup_eq_top K) τ.1
            (IsLocalRing.residue A aA)
      exact (decompositionGroupResidueAction_residue
        (K := K) A τD aA).symm
    _ = localSeparableResidueAlgAction K τ.1
        (finiteGaloisResidueEmbeddingOfEmbedding K L i
          (IsLocalRing.residue 𝒪[L] a)) := by
      rw [finiteGaloisResidueEmbeddingOfEmbedding_residue]

/-! ## Comparison of unramifiedness -/

/-- An actually unramified finite Galois extension gives an unramified
extension for the abstract local residue datum. -/
theorem finiteGaloisAbstractExtensionOfEmbedding_isUnramified :
    (finiteGaloisAbstractExtensionOfEmbedding K L i).IsUnramified
      (localResidueDatum K) := by
  apply ((finiteGaloisAbstractExtensionOfEmbedding K L i).isUnramified_iff_inertia_le
    (localResidueDatum K)).2
  intro g hg
  let A := localSeparableValuationSubring K
  let k := decompositionResidueField K A
  let Omega := selectedResidueField A
  let τ : (abstractBase_p1 K).toSubgroup := ⟨g, hg.1⟩
  let q : Gal(L / K) :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
      (QuotientGroup.mk τ)
  have hdegree : localResidueDegree K g = 1 := hg.2
  have hdegree' :
      residueAbsoluteDegreeIn k Omega
        (localSeparableResidueAlgAction K g) = 1 := hdegree
  have hlocal :
      localSeparableResidueAlgAction K g = 1 := by
    calc
      localSeparableResidueAlgAction K g =
          residueAbsoluteFrobenius k Omega
            (residueAbsoluteDegreeIn k Omega
              (localSeparableResidueAlgAction K g)) :=
        ((residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply
          (localSeparableResidueAlgAction K g)).symm
      _ = residueAbsoluteFrobenius k Omega 1 := by rw [hdegree']
      _ = 1 := map_one _
  have hresidue :
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L q = 1 := by
    apply AlgEquiv.ext
    intro x
    apply (finiteGaloisResidueEmbeddingOfEmbedding K L i).injective
    rw [finiteGaloisResidueEmbeddingOfEmbedding_equivariant K L i τ x]
    change localSeparableResidueAlgAction K g
        (finiteGaloisResidueEmbeddingOfEmbedding K L i x) =
      finiteGaloisResidueEmbeddingOfEmbedding K L i x
    rw [hlocal]
    rfl
  have hq : q = 1 := by
    apply
      galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
        K L
    rw [map_one]
    exact hresidue
  change g ∈
    (finiteGaloisFieldRangeOfEmbedding K L i).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro z hz
  rcases hz with ⟨x, rfl⟩
  have hrestrict :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
      K L i τ x
  change i (q x) = g (i x) at hrestrict
  rw [hq] at hrestrict
  exact hrestrict.symm

/-! ## Frobenius normalization -/

section AbstractUnramifiedFrobenius

attribute [local instance] finiteGaloisResidueBaseExtension_normal

/-- Under the field-facing quotient equivalence, the abstract degree-one
unramified Frobenius is the actual arithmetic Frobenius of the unramified
valuation extension. -/
theorem finiteGaloisAbstractUnramifiedFrobenius_eq_arithmeticFrobenius :
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
        ((localResidueDatum K).unramifiedFrobenius
          (finiteResidueAbstractBase K)
          (finiteGaloisAbstractExtensionOfEmbedding K L i).field
          (finiteGaloisAbstractExtensionOfEmbedding K L i).below) =
      arithmeticFrobeniusOfUnramifiedValuation K L := by
  let phi := abstractBaseFrobeniusLift K
  let q : Gal(L / K) :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
      (QuotientGroup.mk phi)
  have hselected :
      localSeparableResidueAlgAction K phi.1 =
        FiniteField.frobeniusAlgEquivOfAlgebraic
          (decompositionResidueField K
            (localSeparableValuationSubring K))
          (selectedResidueField
            (localSeparableValuationSubring K)) :=
    localSeparableResidueAlgAction_eq_frobenius_of_degree_one K phi.1
      (abstractBaseFrobeniusLift_degree K)
  have hcard :
      Nat.card
          (decompositionResidueField K
            (localSeparableValuationSubring K)) =
        Nat.card 𝓀[K] :=
    (Nat.card_congr
      (localBaseResidueEquivDecompositionResidue K).toEquiv).symm
  have hresidue :
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L q =
        galoisGroupResidueAlgEquivOfIsIntegralClosure K L
          (arithmeticFrobeniusOfUnramifiedValuation K L) := by
    apply AlgEquiv.ext
    intro x
    apply (finiteGaloisResidueEmbeddingOfEmbedding K L i).injective
    rw [finiteGaloisResidueEmbeddingOfEmbedding_equivariant K L i phi x,
      hselected]
    simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    rw [galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply,
      map_pow, ← Nat.card_eq_fintype_card, hcard]
  have hq : q = arithmeticFrobeniusOfUnramifiedValuation K L := by
    apply
      galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
        K L
    exact hresidue
  change q = arithmeticFrobeniusOfUnramifiedValuation K L
  exact hq

end AbstractUnramifiedFrobenius

end

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_BaseComparison_FixedFieldNormQuotient
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeEquiv_unramifiedFrobenius _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_frobenius _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedExtensionRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.DegreeData.maximalUnramifiedRestriction_frobenius _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteAbelianSubextension.normSubgroupMap_val _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.mem_normFilterBasis_iff _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.normQuotientMapOfRingEquiv_normClass _root_.LocalClassFieldTheory.normQuotientToUnramifiedNormQuotient_mk _root_.LocalClassFieldTheory.normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure_mk _root_.LocalClassFieldTheory.unramifiedLocalArtinMap_apply _root_.LocalClassFieldTheory.unramifiedLocalReciprocityIsoToGaloisGroup_inverseIntegerRingUniformizerFieldUnit _root_.LocalClassFieldTheory.unramifiedLocalReciprocityIso_inverseIntegerRingUniformizerFieldUnit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Fixed-field norm quotients

This module compares cohomological finite norm quotients with ordinary field-norm quotients and records their compatibility with fixed-field norm-residue symbols.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- The fixed-field units equivalence sends the cohomological finite norm
subgroup to the additive form of the ordinary field-norm subgroup. -/
theorem map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroup
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsSepClosed Ω]
    (K L : ClosedSubgroup Gal(Ω / k))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField Gal(Ω / k)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω / k)) K
          (le_baseField K))] :
    (finiteNormSubgroup (galoisAmbientUnitsRep k Ω) K L hLK).map
        (abstractFixedFieldUnitsEquivGaloisFixed
          k Ω K).symm.toAddMonoidHom =
      additiveNormSubgroup
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) := by
  let F : IntermediateField k Ω :=
    abstractFixedField k Ω K
  let E : IntermediateField F Ω :=
    abstractRelativeFixedField k Ω hLK
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  let e := abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨b, rfl⟩
    let u : Eˣ := Additive.toMul
      ((abstractRelativeFixedFieldUnitsEquivGaloisFixed
        k Ω K L hLK).symm b)
    have hb :
        abstractRelativeFixedFieldUnitsEquivGaloisFixed
            k Ω K L hLK (Additive.ofMul u) = b := by
      change
        abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK
            ((abstractRelativeFixedFieldUnitsEquivGaloisFixed
              k Ω K L hLK).symm b) = b
      exact
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK).apply_symm_apply b
    rw [← hb,
      relativeNorm_abstractFixedFieldUnit_eq_normUnits
        k Ω K L hLK]
    change e.symm
        (e (Additive.ofMul (normUnits F E u))) ∈ additiveNormSubgroup F E
    rw [e.symm_apply_apply]
    exact ⟨u, rfl⟩
  · intro hy
    change Additive.toMul y ∈ localNormSubgroup F E at hy
    rcases hy with ⟨u, hu⟩
    refine
      ⟨e (Additive.ofMul (normUnits F E u)), ?_, ?_⟩
    · refine
        ⟨abstractRelativeFixedFieldUnitsEquivGaloisFixed
            k Ω K L hLK (Additive.ofMul u), ?_⟩
      exact
        relativeNorm_abstractFixedFieldUnit_eq_normUnits
          k Ω K L hLK u
    · change e.symm
        (e (Additive.ofMul (normUnits F E u))) = y
      rw [e.symm_apply_apply]
      exact congrArg Additive.ofMul hu

/-- The cohomological finite norm quotient for a pair of closed subgroups is
additively equivalent to the ordinary norm quotient of their fixed fields. -/
noncomputable def fixedFieldFiniteNormQuotientEquivNormQuotient
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsSepClosed Ω]
    (K L : ClosedSubgroup Gal(Ω / k))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField Gal(Ω / k)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω / k)) K
          (le_baseField K))] :
    FiniteNormQuotient (galoisAmbientUnitsRep k Ω) K L hLK ≃+
      Additive
        (NormQuotient
          (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK)) := by
  let F : IntermediateField k Ω :=
    abstractFixedField k Ω K
  let E : IntermediateField F Ω :=
    abstractRelativeFixedField k Ω hLK
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  let S := finiteNormSubgroup (galoisAmbientUnitsRep k Ω) K L hLK
  let normAdd : Additive Fˣ →+ Additive (NormQuotient F E) :=
    MonoidHom.toAdditive (normClass F E)
  let T := normAdd.ker
  let e := abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  have hmap : S.map e.symm.toAddMonoidHom = T := by
    simpa [S, T, normAdd, e] using
      (map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroup
        k Ω K L hLK).trans
        (additiveNormSubgroup_eq_ker_quotient_map F E)
  have hforward : S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro x hx
    change e.symm x ∈ T
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hinverse : T ≤ AddSubgroup.comap e.toAddMonoidHom S := by
    intro y hy
    change e y ∈ S
    have hy' : y ∈ S.map e.symm.toAddMonoidHom := by
      rw [hmap]
      exact hy
    rcases hy' with ⟨x, hx, hxy⟩
    have heq : e y = x := by
      apply e.symm.injective
      simpa using hxy.symm
    rw [heq]
    exact hx
  let f :
      (ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) K ⧸ S) →+
        (Additive Fˣ ⧸ T) :=
    QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
  let g :
      (Additive Fˣ ⧸ T) →+
        (ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) K ⧸ S) :=
    QuotientAddGroup.map T S e.toAddMonoidHom hinverse
  let modelEquiv :
      (ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) K ⧸ S) ≃+
        (Additive Fˣ ⧸ T) :=
    { toFun := f
      invFun := g
      left_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change ↑(e (e.symm x)) =
          (↑x : ambientFixedAddSubgroup
            (galoisAmbientUnitsRep k Ω) K ⧸ S)
        rw [e.apply_symm_apply]
      right_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change ↑(e.symm (e x)) = (↑x : Additive Fˣ ⧸ T)
        rw [e.symm_apply_apply]
      map_add' := f.map_add }
  let quotientEquiv :
      (Additive Fˣ ⧸ T) ≃+ Additive (NormQuotient F E) :=
    QuotientAddGroup.quotientKerEquivOfSurjective normAdd
      (QuotientGroup.mk'_surjective
        (localNormSubgroup
          (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK)))
  exact
    (finiteNormQuotientConcreteEquiv
      (galoisAmbientUnitsRep k Ω) K L hLK).trans
      (modelEquiv.trans quotientEquiv)

/-- The fixed-field norm-quotient equivalence sends a cohomological finite norm
class to the ordinary norm class of the corresponding fixed-field unit. -/
theorem fixedFieldFiniteNormQuotientEquivNormQuotient_finiteNormClass
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsSepClosed Ω]
    (K L : ClosedSubgroup Gal(Ω / k))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField Gal(Ω / k)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω / k)) K
          (le_baseField K))]
    (a : ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) K) :
    fixedFieldFiniteNormQuotientEquivNormQuotient
        k Ω K L hLK
        (finiteNormClass (galoisAmbientUnitsRep k Ω) K L hLK a) =
      MonoidHom.toAdditive
        (normClass
          (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK))
        ((abstractFixedFieldUnitsEquivGaloisFixed k Ω K).symm a) := by
  let F : IntermediateField k Ω :=
    abstractFixedField k Ω K
  let E : IntermediateField F Ω :=
    abstractRelativeFixedField k Ω hLK
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  let S := finiteNormSubgroup (galoisAmbientUnitsRep k Ω) K L hLK
  let normAdd : Additive Fˣ →+ Additive (NormQuotient F E) :=
    MonoidHom.toAdditive (normClass F E)
  let T := normAdd.ker
  let e := abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  have hmap : S.map e.symm.toAddMonoidHom = T := by
    simpa [S, T, normAdd, e] using
      (map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroup
        k Ω K L hLK).trans
        (additiveNormSubgroup_eq_ker_quotient_map F E)
  have hforward : S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro x hx
    change e.symm x ∈ T
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  simp only [fixedFieldFiniteNormQuotientEquivNormQuotient,
    finiteNormQuotientConcreteEquiv_finiteNormClass,
    AddEquiv.trans_apply,
    QuotientAddGroup.quotientKerEquivOfSurjective,
    QuotientAddGroup.quotientKerEquivOfRightInverse]
  change QuotientAddGroup.kerLift normAdd
      (QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
        (QuotientAddGroup.mk' S a)) =
    normAdd (e.symm a)
  rw [QuotientAddGroup.map_mk', QuotientAddGroup.kerLift_mk]
  rfl

/-- The abstract fixed-field norm-residue symbol of the relative norm of a
prime element is the prescribed Frobenius quotient class. -/
theorem abstractFixedFieldNormResidueSymbol_apply_primeNorm
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsSepClosed Ω]
    (D : DegreeData Gal(Ω / k))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k Ω))
    (K L : ClosedSubgroup Gal(Ω / k))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField Gal(Ω / k)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω / k)) K
          (le_baseField K))]
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (σ : D.FrobeniusElements
      ((⟨K, hKabsolute⟩ : FiniteAbstractField
        Gal(Ω / k)).toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      ((⟨K, hKabsolute⟩ : FiniteAbstractField
        Gal(Ω / k)).toFiniteResidueAbstractField D) L hLK σ = q)
    (π : ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω)
      (D.frobeniusFixedField
        ((⟨K, hKabsolute⟩ : FiniteAbstractField
          Gal(Ω / k)).toFiniteResidueAbstractField D)
        L hLK σ))
    (hπ :
      let KF : FiniteAbstractField Gal(Ω / k) :=
        ⟨K, hKabsolute⟩
      let KR := KF.toFiniteResidueAbstractField D
      let S := D.frobeniusFixedField KR L hLK σ
      let hSK := D.frobeniusFixedField_le KR L hLK σ
      letI : Finite
          (K.toSubgroup ⧸ extensionSubgroup K S hSK) :=
        D.frobeniusFixedField_finite KR L hLK σ
      let Sigma : FiniteAbstractField Gal(Ω / k) :=
        ⟨S, D.frobeniusFixedField_absoluteFinite KF L hLK σ⟩
      v.IsPrimeElement Sigma π) :
    let KF : FiniteAbstractField Gal(Ω / k) :=
      ⟨K, hKabsolute⟩
    let KR := KF.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.toSubgroup ⧸ extensionSubgroup K S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    let x : (abstractFixedField k Ω K)ˣ :=
      Additive.toMul
        ((abstractFixedFieldUnitsEquivGaloisFixed k Ω K).symm
          (relativeNorm (galoisAmbientUnitsRep k Ω)
            K S hSK π))
    abstractFixedFieldNormResidueSymbol
        k Ω D v hcf K L hLK (Additive.ofMul x) =
      Additive.ofMul
        ((abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal).abelianizationCongr
          (Abelianization.of q)) := by
  dsimp only
  let KF : FiniteAbstractField Gal(Ω / k) :=
    ⟨K, hKabsolute⟩
  let E : FiniteGaloisSubextension KF.field :=
    ⟨L, hLK, hnormal, hfinite⟩
  let KR := KF.toFiniteResidueAbstractField D
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK := D.frobeniusFixedField_le KR L hLK σ
  let hSfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let qGal :=
    abstractExtensionQuotientEquivGaloisGroup
      k Ω K L hLK hnormal
  let b :=
    abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  let a :=
    relativeNorm (galoisAmbientUnitsRep k Ω) K S hSK π
  let x : (abstractFixedField k Ω K)ˣ :=
    Additive.toMul (b.symm a)
  have hbase : b (Additive.ofMul x) = a := by
    change b (b.symm a) = a
    exact b.apply_symm_apply a
  have hprime :
      D.finiteReciprocityHom
          (galoisAmbientUnitsRep k Ω) v
          (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
          KF L hLK (Additive.ofMul q) =
        finiteNormClass (galoisAmbientUnitsRep k Ω)
          K L hLK a := by
    simpa only [KF, KR, S, hSK, a] using
      D.finiteReciprocityHom_apply_eq_primeNormClass
        (galoisAmbientUnitsRep k Ω) v
        (v.classFieldAxiom_implies_unramifiedUnitCohomology hcf)
        KF L hLK (Additive.ofMul q) σ hσ π hπ
  change
    (MulEquiv.toAdditive qGal.abelianizationCongr)
        (D.normResidueSymbol
          (galoisAmbientUnitsRep k Ω) v hcf KF E
          (finiteNormClass (galoisAmbientUnitsRep k Ω)
            K L hLK (b (Additive.ofMul x)))) =
      Additive.ofMul
        (qGal.abelianizationCongr (Abelianization.of q))
  rw [hbase, ← hprime]
  exact congrArg
    (fun z : Additive (Abelianization E.extensionQuotient) =>
      MulEquiv.toAdditive qGal.abelianizationCongr z)
    (D.normResidueSymbol_finiteReciprocityHom
      (galoisAmbientUnitsRep k Ω) v hcf KF E
      (show E.extensionQuotient from q))

/-- The abstract fixed-field norm-residue symbol depends only on the norm
class of the input unit. -/
theorem abstractFixedFieldNormResidueSymbol_eq_of_normClass_eq
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsSepClosed Ω]
    (D : DegreeData Gal(Ω / k))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k Ω))
    (K L : ClosedSubgroup Gal(Ω / k))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField Gal(Ω / k)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω / k)) K
          (le_baseField K))]
    (x y : (abstractFixedField k Ω K)ˣ)
    (hxy :
      normClass (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK) x =
        normClass (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK) y) :
    abstractFixedFieldNormResidueSymbol
        k Ω D v hcf K L hLK (Additive.ofMul x) =
      abstractFixedFieldNormResidueSymbol
        k Ω D v hcf K L hLK (Additive.ofMul y) := by
  let F := abstractFixedField k Ω K
  let E := abstractRelativeFixedField k Ω hLK
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  let b :=
    abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  have hfiniteClass :
      finiteNormClass (galoisAmbientUnitsRep k Ω)
          K L hLK (b (Additive.ofMul x)) =
        finiteNormClass (galoisAmbientUnitsRep k Ω)
          K L hLK (b (Additive.ofMul y)) := by
    apply
      (fixedFieldFiniteNormQuotientEquivNormQuotient
        k Ω K L hLK).injective
    rw [
      fixedFieldFiniteNormQuotientEquivNormQuotient_finiteNormClass,
      fixedFieldFiniteNormQuotientEquivNormQuotient_finiteNormClass]
    simpa [b, F, E] using congrArg Additive.ofMul hxy
  change
    (MulEquiv.toAdditive
      (abstractExtensionQuotientEquivGaloisGroup
        k Ω K L hLK hnormal).abelianizationCongr)
        (D.normResidueSymbol
          (galoisAmbientUnitsRep k Ω) v hcf
          (⟨K, hKabsolute⟩ : FiniteAbstractField
            Gal(Ω / k))
          (⟨L, hLK, hnormal, hfinite⟩ :
            FiniteGaloisSubextension K)
          (finiteNormClass (galoisAmbientUnitsRep k Ω)
            K L hLK (b (Additive.ofMul x)))) =
      (MulEquiv.toAdditive
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal).abelianizationCongr)
        (D.normResidueSymbol
          (galoisAmbientUnitsRep k Ω) v hcf
          (⟨K, hKabsolute⟩ : FiniteAbstractField
            Gal(Ω / k))
          (⟨L, hLK, hnormal, hfinite⟩ :
            FiniteGaloisSubextension K)
          (finiteNormClass (galoisAmbientUnitsRep k Ω)
            K L hLK (b (Additive.ofMul y))))
  rw [hfiniteClass]

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormalization
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Canonical unramified normalization

The canonical local norm-residue symbol is identified with the field-facing
unramified Artin map. An element of normalized valuation one maps to arithmetic
Frobenius, both algebraically and in the topological abelianization.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped IsMulCommutative ValuativeRel
open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

def extensionQuotientEquivOfEq
    {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {K L K' L' : ClosedSubgroup Γ}
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK : K = K') (hL : L = L') :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃
      (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K') := by
  subst K'
  subst L'
  have hp : hLK = hL'K' := Subsingleton.elim _ _
  subst hL'K'
  exact Equiv.refl _

section BasePrime

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem localHenselianValuation_valuationAt_baseUnit
    (x : Kˣ) :
    (((localHenselianValuation K).valuationAt (intrinsicFiniteAbstractBase K)
      (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
        (Additive.ofMul x)) :
        (localHenselianValuation K).valueGroup) : ZHat) =
      Int.castRingHom ZHat
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul x)) := by
  let : Finite ((baseField (G_p3 K)).toSubgroup ⧸
      extensionSubgroup (baseField (G_p3 K)) (B_p2 K) (le_baseField (B_p2 K))) :=
    (intrinsicFiniteAbstractBase K).finite
  have h :=
    (localHenselianValuation K).residueDegree_nsmul_dividedAt
      (intrinsicFiniteAbstractBase K)
      (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
        (Additive.ofMul x))
  rw [intrinsicFiniteAbstractBase_residueDegree_eq_one K, one_nsmul] at h
  rw [(localHenselianValuation K).valuationAt_coe, h]
  change localBaseValuation K
      (normToBase (A_p2 K) (B_p2 K)
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul x))) =
    Int.castRingHom ZHat
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
        (Additive.ofMul x))
  let a : ambientFixedAddSubgroup (A_p2 K) (baseField (G_p3 K)) :=
    baseFieldUnitsEquiv K (Additive.ofMul x)
  have ha :
      baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul x) =
        fixedFieldInclusion (A_p2 K) (baseField (G_p3 K)) (B_p2 K)
          (le_baseField (B_p2 K)) a := by
    apply Subtype.ext
    rfl
  rw [ha]
  let E : DegreeData.FiniteAbstractExtension (G_p3 K) := {
    field := B_p2 K
    base := baseField (G_p3 K)
    below := le_baseField (B_p2 K)
    finiteQuotient := inferInstance }
  change localBaseValuation K
      (relativeNorm (A_p2 K) (baseField (G_p3 K)) (B_p2 K)
        (le_baseField (B_p2 K))
        (fixedFieldInclusion (A_p2 K) (baseField (G_p3 K)) (B_p2 K)
          (le_baseField (B_p2 K)) a)) = _
  rw [relativeNorm_fixedFieldInclusion (A_p2 K) E]
  have hdegree :
      (E.degree : ℕ) = 1 := by
    rw [← E.relIndex_eq_degree]
    change (B_p2 K).toSubgroup.relIndex (baseField (G_p3 K)).toSubgroup = 1
    rw [show B_p2 K = baseField (G_p3 K) from
      closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K)]
    exact Subgroup.relIndex_self (H := (baseField (G_p3 K)).toSubgroup)
  rw [hdegree, one_nsmul]
  exact localBaseValuation_baseFieldUnitsEquiv K (Additive.ofMul x)

end BasePrime

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicValuationComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.LubinTate.standardLubinTateUnitParameter_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsNonarchimedeanLocalField _root_.chosenFinitePlaceBaseValuativeRel _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Comparison of the chosen and canonical valuations on the p-adic field

The concrete local-field package on `ℚ_[p]` uses the DVR valuation obtained
from `ℤ_[p]`, whereas mathlib's nonarchimedean-local-field API uses
`ValuativeRel.valuation ℚ_[p]`.  This file proves that these are equivalent
valuations and makes the comparison usable when transporting valuation
extensions.
-/

noncomputable section

open scoped ValuativeRel

namespace LocalFieldTheory
namespace DiscreteValuationField
namespace Examples
namespace Qp

universe u v

/-- Any valuation extension of the canonical complete-DVF valuation on
`ℚ_[p]` is also an extension of the valuation selected by
`padicLocalField p`. -/
theorem padicLocalFieldValuation_hasExtension_of_localCompleteDVF
    (p : ℕ) [Fact p.Prime]
    {E : Type u} [Field E] [Algebra ℚ_[p] E]
    {Gamma : Type v} [LinearOrderedCommGroupWithZero Gamma]
    (wE : _root_.Valuation E Gamma)
    [(LocalFieldTheory.localCompleteDVF ℚ_[p]).valuation.HasExtension wE] :
    (padicLocalField p).toCompleteDVF.valuation.HasExtension wE :=
  ValuationTheory.DiscreteValuationField.ValuedExtension.hasExtension_of_isEquiv_base
    (padicLocalField_valuation_isEquiv_localCompleteDVF p)

end Qp
end Examples
end DiscreteValuationField
end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.instContinuousSMulPadicLocalAlgebra _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instLocallyCompactSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass
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
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_r50d02d_1
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
noncomputable local instance
    rationalCyclotomicArtinLocalizedGlobalAlgebra_r50d02d_1
    (m : ℕ+) (q : Nat.Primes) :
    Algebra ℚ (rationalCyclotomicArtinLocalizedField m q) :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
noncomputable local instance
    rationalCyclotomicArtinLocalizedScalarTower_r50d02d_1
    (m : ℕ+) (q : Nat.Primes) :
    IsScalarTower ℚ
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) := by
  constructor
  intro r x y
  simp only [Algebra.smul_def, map_mul, eq_ratCast,
    map_ratCast, mul_assoc]
  try (first | exact (Rat.smul_def r _).symm | (rw [Algebra.smul_def, eq_ratCast]) | simp [Algebra.smul_def])
noncomputable local instance
    rationalCyclotomicArtinLocalizedFiniteDimensional
    (m : ℕ+) (q : Nat.Primes) :
    FiniteDimensional
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  finitePlaceLocalArtinFiniteDimensional
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsAbelianGalois
    (m : ℕ+) (q : Nat.Primes) :
    IsAbelianGalois
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  finitePlaceLocalArtinIsAbelianGalois
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)
    (inferInstance :
      FiniteDimensional ℚ (rationalCyclotomicArtinLevel m))

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsSeparable
    (m : ℕ+) (q : Nat.Primes) :
    Algebra.IsSeparable
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  (rationalCyclotomicArtinLocalizedIsAbelianGalois m q).toIsGalois.to_isSeparable

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsCyclotomic
    (m : ℕ+) (q : Nat.Primes) :
    IsCyclotomicExtension {(m : ℕ)}
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  rationalCyclotomicLevel_localizedCompletion_isCyclotomicExtension
    m (rationalCyclotomicArtinPlace q)

noncomputable local instance
    rationalCyclotomicArtinExtensionFiniteDimensional
    (m : ℕ+) (q : Nat.Primes) :
    FiniteDimensional
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  completionModuleFinite
    (rationalCyclotomicArtinBaseAbv q)
    (RayClass.adicAbv_isNontrivial
      (rationalCyclotomicArtinPlace q))
    (rationalCyclotomicArtinExtension m q)

noncomputable local instance
    rationalCyclotomicArtinExtensionContinuousSMul
    (m : ℕ+) (q : Nat.Primes) :
    ContinuousSMul
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  continuousSMul_of_algebraMap _ _
    (AbsoluteValue.completionMap_isometry
      (rationalCyclotomicArtinBaseAbv q)
      (rationalCyclotomicArtinExtension m q).1
      (rationalCyclotomicArtinExtension m q).2).continuous

noncomputable local instance
    rationalCyclotomicArtinExtensionLocallyCompact
    (m : ℕ+) (q : Nat.Primes) :
    LocallyCompactSpace
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  LocallyCompactSpace.of_finiteDimensional_of_complete
    (rationalCyclotomicArtinBaseAbv q).Completion
    (rationalCyclotomicArtinExtension m q).1.Completion

noncomputable def
    rationalCyclotomicArtinLocalizedEquivCompletion
    (m : ℕ+) (q : Nat.Primes) :
    rationalCyclotomicArtinLocalizedField m q ≃ᵢ
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  { toEquiv :=
      (localizedCompletionEquivCompletion
        (rationalCyclotomicArtinBaseAbv q)
        (RayClass.adicAbv_isNontrivial
          (rationalCyclotomicArtinPlace q))
        (rationalCyclotomicArtinExtension m q)).toEquiv
    isometry_toFun :=
      Isometry.of_dist_eq fun _ _ => rfl }

noncomputable local instance
    rationalCyclotomicArtinLocalizedLocallyCompact
    (m : ℕ+) (q : Nat.Primes) :
    LocallyCompactSpace
      (rationalCyclotomicArtinLocalizedField m q) :=
  ((rationalCyclotomicArtinLocalizedEquivCompletion m q).toHomeomorph.locallyCompactSpace_iff).2
    inferInstance

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsUltrametricDist_r50d02d_1
    (m : ℕ+) (q : Nat.Primes) :
    IsUltrametricDist
      (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionIsUltrametricDist
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))
noncomputable local instance rationalCyclotomicArtinLocalizedValued
    (m : ℕ+) (q : Nat.Primes) :
    Valued (rationalCyclotomicArtinLocalizedField m q) ℝ≥0 :=
  localizedCompletionFinitePlaceValued
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))

attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuativeRel
noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationCompatible
    (m : ℕ+) (q : Nat.Primes) :
    (Valued.v : Valuation
      (rationalCyclotomicArtinLocalizedField m q) ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _

noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationHasExtension
    (m : ℕ+) (q : Nat.Primes) :
    Valuation.HasExtension
      (ValuativeRel.valuation
        (rationalCyclotomicArtinBaseAbv q).Completion)
      (ValuativeRel.valuation
        (rationalCyclotomicArtinLocalizedField m q)) :=
  localizedCompletionValuationHasExtension
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))

noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationIsNontrivial
    (m : ℕ+) (q : Nat.Primes) :
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q)).IsNontrivial :=
  Valuation.IsNontrivial.of_hasExtension
    (ValuativeRel.valuation
      (rationalCyclotomicArtinBaseAbv q).Completion)
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q))

noncomputable local instance
    rationalCyclotomicArtinLocalizedValuativeRelIsNontrivial
    (m : ℕ+) (q : Nat.Primes) :
    ValuativeRel.IsNontrivial
      (rationalCyclotomicArtinLocalizedField m q) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q))).2 inferInstance

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsValuativeTopology
    (m : ℕ+) (q : Nat.Primes) :
    IsValuativeTopology
      (rationalCyclotomicArtinLocalizedField m q) :=
  isValuativeTopology_of_valued_ofValuation
    (rationalCyclotomicArtinLocalizedField m q) ℝ≥0

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField
    (m : ℕ+) (q : Nat.Primes) :
    IsNonarchimedeanLocalField
      (rationalCyclotomicArtinLocalizedField m q) :=
  { toIsValuativeTopology := inferInstance
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := inferInstance }

noncomputable local instance
    rationalCyclotomicArtinLocalizedIntegerAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      (rationalCyclotomicArtinLocalizedField m q) :=
  Algebra.ofSubsemiring
    𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsIntegralClosure
    (m : ℕ+) (q : Nat.Primes) :
    IsIntegralClosure
      𝒪[rationalCyclotomicArtinLocalizedField m q]
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionIsIntegralClosureWithExtension
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (RayClass.adicAbv_isNontrivial
      (rationalCyclotomicArtinPlace q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))

noncomputable local instance
    rationalCyclotomicArtinLocalizedIntegerModuleFinite
    (m : ℕ+) (q : Nat.Primes) :
    Module.Finite
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      𝒪[rationalCyclotomicArtinLocalizedField m q] :=
  integerRing_moduleFinite_of_isIntegralClosure
    (rationalCyclotomicArtinBaseAbv q).Completion
    (rationalCyclotomicArtinLocalizedField m q)

section RationalCyclotomicPrincipalPrime

/-! ## Ramified prime-power transport

This section reuses the canonical finite-place Artin tower above.  In
particular, it introduces no parallel completion/localization instance tower. -/

/-! ## The ramified principal finite-place factor -/

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_2
attribute [local instance] GlobalClassFieldTheory.Reciprocity.instNeZeroNatVal_solutions
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsUltrametricDist
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionSMul
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinCompletionAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionRatAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelIsAbelianGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseLocallyCompactSpace
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValued
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRel
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationCompatible
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRelIsNontrivial
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_r50d02d_2
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsNonarchimedeanLocalField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionAlgebra
noncomputable local instance
    rationalCyclotomicArtinLocalizedGlobalAlgebra_r50d02d_2
    (m : ℕ+) (q : Nat.Primes) :
    Algebra ℚ (rationalCyclotomicArtinLocalizedField m q) :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
noncomputable local instance
    rationalCyclotomicArtinLocalizedScalarTower_r50d02d_2
    (m : ℕ+) (q : Nat.Primes) :
    IsScalarTower ℚ
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) := by
  constructor
  intro r x y
  simp only [Algebra.smul_def, map_mul, eq_ratCast,
    map_ratCast, mul_assoc]
  try (first | exact (Rat.smul_def r _).symm | (rw [Algebra.smul_def, eq_ratCast]) | simp [Algebra.smul_def])
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsUltrametricDist_r50d02d_2
    (m : ℕ+) (q : Nat.Primes) :
    IsUltrametricDist
      (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionIsUltrametricDist
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuativeRel
noncomputable local instance
    rationalCyclotomicPrincipalPrimeLevelIsCyclotomicExtension_r50d02d_1
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
noncomputable local instance
    rationalCyclotomicArtinLocalizedPadicScalarTower_r50d02d_1
    (m : ℕ+) (p : Nat.Primes) :
    IsScalarTower ℚ ℚ_[p.1]
      (rationalCyclotomicArtinLocalizedField m p) := by
  constructor
  intro r x y
  simp only [Algebra.smul_def, map_mul, eq_ratCast,
    map_ratCast, mul_assoc]
  try (first | exact (Rat.smul_def r _).symm | (rw [Algebra.smul_def, eq_ratCast]) | simp [Algebra.smul_def])
theorem finitePlaceLocalToGlobalMonoidHom_apply_pow_of_localized_action
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (sigma :
      let vK := HeightOneSpectrum.adicAbv K v
      let E := LocalizedCompletion vK w
      letI : Algebra vK.Completion E :=
        finitePlaceLocalArtinLocalizedAlgebra v w
      Gal(E / vK.Completion))
    (z : L)
    (zLocal :
      let vK := HeightOneSpectrum.adicAbv K v
      LocalizedCompletion vK w)
    (e : ℕ)
    (hLocalization :
      let vK := HeightOneSpectrum.adicAbv K v
      let E := LocalizedCompletion vK w
      letI : Algebra vK.Completion E :=
        finitePlaceLocalArtinLocalizedAlgebra v w
      let eLoc : L →+* E :=
        AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
      eLoc z = zLocal)
    (hlocal : sigma zLocal = zLocal ^ e) :
    finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w sigma z = z ^ e := by
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial v
  let E := LocalizedCompletion vK w
  let : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let eD : absoluteValueDecompositionGroup K w.1 ≃* Gal(E / vK.Completion) :=
    decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
  let eLoc : L →+* E :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let delta : absoluteValueDecompositionGroup K w.1 := eD.symm sigma
  have hDecomposition : eD delta = sigma := eD.apply_symm_apply sigma
  apply eLoc.injective
  calc
    eLoc (finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w sigma z) =
        eD delta (eLoc z) :=
      (localizationRamificationGroups_decompositionGroupEquiv_toLocalization
        vK hvK w delta z).symm
    _ = sigma (eLoc z) :=
      congrArg (fun tau : Gal(E / vK.Completion) => tau (eLoc z))
        hDecomposition
    _ = sigma zLocal :=
      congrArg (fun y : E => sigma y) hLocalization
    _ = zLocal ^ e := hlocal
    _ = (eLoc z) ^ e :=
      congrArg (fun y : E => y ^ e) hLocalization.symm
    _ = eLoc (z ^ e) := (map_pow eLoc z e).symm

end RationalCyclotomicPrincipalPrime

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalAwayProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField
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
local instance instNeZeroNatVal_solutions_1_r50d02d_1 (m : ℕ+) : NeZero (m : ℕ) :=
  ⟨m.ne_zero⟩
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalPrimePowerNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalPrimePowerFiniteDimensional
local instance rationalCyclotomicPrincipalPrimePowerIsGalois
    (p : Nat.Primes) (k : ℕ) :
    IsGalois ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_isGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

end Reciprocity
end GlobalClassFieldTheory
end
end


