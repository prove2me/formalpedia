-- Prove2me | Definitions.Def_OAIQ244Duke078
-- name    : OAIQ244Duke078
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T23:07:49.475196+00:00
-- url     : https://prove2.me/theorems/7baadbe9-c688-4133-875b-0e8b0d4f6bd8
-- title:
--   Definitions bundle OAIQ244Duke078 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 5 definitions and 10 theorems. The definitions and types are `GlobalClassFieldTheory.GlobalClassFields.sUnitKummerNormSupport`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalToGlobalMonoidHom`, `GlobalClassFieldTheory.Reciprocity.rationalIdeleClassEquivBaseFixed`, `GlobalClassFieldTheory.Reciprocity.rationalIdeleClassEquivFixed`, `GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassToFixed`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_GlobalClassFields_SUnitKummerNormCore`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitAbstractFixedField`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFixedPointDescent`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFixedPointDescentCore`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFixedPoints`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`.
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
import Definitions.Def_OAIQ244Duke069
import Definitions.Def_OAIQ244Duke070
import Definitions.Def_OAIQ244Duke071
import Definitions.Def_OAIQ244Duke072

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SUnitKummerNormCore
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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

/-- The chosen finite support used for the full `S`-unit Kummer
construction: it contains the prescribed seed, a support large enough to
represent every idele class, and the finite support of the exponent. -/
noncomputable def sUnitKummerNormSupport
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  let hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let nUnit : Kˣ := Units.mk0 ((n : ℕ) : K) hnK
  (S ∪ IdeleGroup.sufficientlyLargeFiniteSet (K := K)) ∪
    chosenUnitFiniteSupport (K := K) nUnit

/-- The prescribed seed is contained in the chosen Kummer norm
support. -/
theorem subset_sUnitKummerNormSupport
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    S ⊆ sUnitKummerNormSupport (K := K) n S := by
  intro v hv
  exact Finset.mem_union_left _
    (Finset.mem_union_left _ hv)

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFixedPointDescentCore
private local instance q359TowerIdeleIsMulCommutative0.{w} (A B C : Type w) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Descent of fixed rational idele classes

An element of the rational idele-class direct limit which is fixed over a
finite intermediate field is represented at a finite Galois level.  Its
actual tower base change is Galois-fixed, hence descends to an idele class
of the intermediate field.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- If a finite-level representative of the rational idele-class direct
limit is fixed by the absolute Galois subgroup over `K`, then its actual
tower base change from `ℚ` to `K` is fixed by `Gal(U/K)`. -/
theorem rationalTowerRelativeIdeleClass_fixed_of_directLimit_fixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    [IsScalarTower ℚ K U]
    [FiniteDimensional K U]
    [IsGalois K U]
    (h_algebraMap : ∀ x : K,
      ((algebraMap K U x : U) : SeparableClosure ℚ) =
        (x : SeparableClosure ℚ))
    (d : RelativeIdeleGroup.ClassGroup ℚ U)
    (z : rationalIdeleClassDirectLimit)
    (hzU :
      z = (⟦⟨U, d⟩⟧ : rationalIdeleClassDirectLimit))
    (hz_fixed :
      ∀ σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ,
        σ ∈ K.fixingSubgroup → σ • z = z) :
    towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
          ((TowerRelativeIdeleGroup.classGroupEquiv
            ℚ K U).symm d) ∈
      RelativeIdeleGroup.galoisFixedClassSubgroup K U := by
  intro η
  let τ : U ≃ₐ[ℚ] U :=
    η.restrictScalars ℚ
  obtain ⟨σ, hσU⟩ :=
    (AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := U) (E := SeparableClosure ℚ)) τ
  have hσK : σ ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    let yK : K := ⟨y, hy⟩
    let yU : U := algebraMap K U yK
    have hη : η yU = yU := by
      exact η.commutes yK
    have hres :=
      DFunLike.congr_fun hσU yU
    calc
      σ y =
          σ ((yU : U) : SeparableClosure ℚ) := by
        rw [h_algebraMap yK]
      _ =
          (((AlgEquiv.restrictNormalHom U σ) yU : U) :
            SeparableClosure ℚ) :=
        (AlgEquiv.restrictNormal_commutes σ U yU).symm
      _ = ((τ yU : U) : SeparableClosure ℚ) :=
        congrArg Subtype.val hres
      _ = ((η yU : U) : SeparableClosure ℚ) := rfl
      _ = ((yU : U) : SeparableClosure ℚ) :=
        congrArg Subtype.val hη
      _ = y :=
        h_algebraMap yK
  have hzσ := hz_fixed σ hσK
  rw [hzU, DirectLimit.smul_def] at hzσ
  have hdQ :
      (AlgEquiv.restrictNormalHom U σ) • d = d :=
    (rationalRelativeIdeleClassToDirectLimit_injective U) hzσ
  have hdτ : τ • d = d := by
    rw [← hσU]
    exact hdQ
  calc
    η •
        towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
          ((TowerRelativeIdeleGroup.classGroupEquiv
            ℚ K U).symm d) =
        towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
          ((TowerRelativeIdeleGroup.classGroupEquiv
            ℚ K U).symm
            ((η.restrictScalars ℚ) • d)) :=
      (towerRelativeIdeleClassBaseChangeMulEquiv_smul
        ℚ K U η d).symm
    _ =
        towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
          ((TowerRelativeIdeleGroup.classGroupEquiv
            ℚ K U).symm d) :=
      congrArg
        (fun a =>
          towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
            ((TowerRelativeIdeleGroup.classGroupEquiv
              ℚ K U).symm a))
        hdτ


end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFixedPointDescent
private local instance q359TowerIdeleIsMulCommutative1.{w} (A B C : Type w) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-level and direct-limit fixed-point descent endpoints

This endpoint leaf turns the reusable fixed-point comparisons into actual
descent witnesses first at one finite Galois level and then in the rational
idèle-class direct limit.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity
/-- The tower base-change equivalence carries extension of a rational
relative idele class along `K ↪ U` to relative class inclusion of the
corresponding idele class of `K`. This is the actual commuting square used
for descent. -/
theorem rationalRelativeIdeleClass_descent_square
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    [IsScalarTower ℚ K U]
    [FiniteDimensional K U]
    [IsGalois K U]
    (hKU :
      K ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)))
    (h_algebraMap : ∀ x : K,
      ((algebraMap K U x : U) : SeparableClosure ℚ) =
        (x : SeparableClosure ℚ))
    (q : IdeleClassGroup K) :
    rationalRelativeIdeleClassTowerBaseChangeEquiv K U
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
          (IntermediateField.inclusion hKU)
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm q)) =
      RelativeIdeleGroup.classInclusion K U q := by
  have hAlgebra :=
    rationalIntermediateField_algebra_eq_inclusion
      K U hKU h_algebraMap
  cases hAlgebra
  let : Algebra K U :=
    (IntermediateField.inclusion hKU).toRingHom.toAlgebra
  let : IsScalarTower ℚ K U :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional K U :=
    FiniteDimensional.right ℚ K U
  let : IsGalois K U :=
    IsGalois.tower_top_of_isGalois ℚ K U
  calc
    rationalRelativeIdeleClassTowerBaseChangeEquiv K U
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
            (IntermediateField.inclusion hKU)
            ((_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K)).symm q)) =
        RelativeIdeleGroup.classInclusion K U
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)
            ((_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K)).symm q)) := by
      change
        towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
            ((TowerRelativeIdeleGroup.classGroupEquiv ℚ K U).symm
              (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
                (IntermediateField.inclusion hKU)
                ((_root_.relativeIdeleClassBaseChangeMulEquiv
                  (K := ℚ) (L := K)).symm q))) =
          RelativeIdeleGroup.classInclusion K U
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K)
              ((_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := K)).symm q))
      exact
        rationalRelativeIdeleClassEmbedding_towerBaseChange
          hKU
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm q)
    _ = RelativeIdeleGroup.classInclusion K U q := by
      exact
        congrArg (RelativeIdeleGroup.classInclusion K U)
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).apply_symm_apply q)

/-- A rational relative idele class at a finite Galois level whose actual
tower base change is fixed over `K` descends to an actual idele class of
`K`.  The conclusion is the commuting square with relative scalar
extension, not merely an abstract preimage. -/
theorem rationalRelativeIdeleClass_exists_descent_of_tower_fixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (U : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    [Algebra K U]
    [IsScalarTower ℚ K U]
    [FiniteDimensional K U]
    [IsGalois K U]
    (hKU :
      K ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)))
    (h_algebraMap : ∀ x : K,
      ((algebraMap K U x : U) : SeparableClosure ℚ) =
        (x : SeparableClosure ℚ))
    (d : RelativeIdeleGroup.ClassGroup ℚ U)
    (hd_fixed :
      towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
            ((TowerRelativeIdeleGroup.classGroupEquiv
              ℚ K U).symm d) ∈
        RelativeIdeleGroup.galoisFixedClassSubgroup K U) :
    ∃ q : IdeleClassGroup K,
      RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
          (IntermediateField.inclusion hKU)
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm q) =
        d := by
  let e :
      RelativeIdeleGroup.ClassGroup ℚ U ≃*
        RelativeIdeleGroup.ClassGroup K U :=
    rationalRelativeIdeleClassTowerBaseChangeEquiv K U
  let dK : RelativeIdeleGroup.ClassGroup K U :=
    towerRelativeIdeleClassBaseChangeMulEquiv ℚ K U
      ((TowerRelativeIdeleGroup.classGroupEquiv ℚ K U).symm d)
  have hdK_fixed :
      dK ∈
        RelativeIdeleGroup.galoisFixedClassSubgroup K U := by
    exact hd_fixed
  let dFixed :
      RelativeIdeleGroup.galoisFixedClassSubgroup K U :=
    ⟨dK, hdK_fixed⟩
  let q : IdeleClassGroup K :=
    (rationalIntermediateIdeleClassEquivGaloisFixed K U).symm dFixed
  have hqU :
      RelativeIdeleGroup.classInclusion K U q = dK := by
    calc
      RelativeIdeleGroup.classInclusion K U q =
          ((rationalIntermediateIdeleClassEquivGaloisFixed K U q :
              RelativeIdeleGroup.galoisFixedClassSubgroup K U) :
            RelativeIdeleGroup.ClassGroup K U) :=
        (rationalIntermediateIdeleClassEquivGaloisFixed_coe
          K U q).symm
      _ = dK := by
        exact congrArg Subtype.val
          ((rationalIntermediateIdeleClassEquivGaloisFixed
            K U).apply_symm_apply dFixed)
  refine ⟨q, e.injective ?_⟩
  calc
    e
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
          (IntermediateField.inclusion hKU)
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm q)) =
        RelativeIdeleGroup.classInclusion K U q :=
      rationalRelativeIdeleClass_descent_square
        K U hKU h_algebraMap q
    _ = dK := hqU
    _ = e d := rfl

/-- Every rational direct-limit idele class fixed by the absolute Galois
subgroup over a finite intermediate field comes from an actual idele
class of that field.  The proof chooses an actual finite-Galois
representative and descends it through the tower comparison. -/
theorem rationalDirectLimit_fixed_exists_ideleClass
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (z : rationalIdeleClassDirectLimit)
    (hz_fixed :
      ∀ σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ,
        σ ∈ K.fixingSubgroup → σ • z = z) :
    ∃ q : IdeleClassGroup K,
      rationalIntermediateIdeleClassToDirectLimit K q = z := by
  obtain ⟨E, c, hzc⟩ :=
    DirectLimit.exists_eq_mk
      (fun _ _ h => rationalRelativeIdeleClassTransition h) z
  let U :
      FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) :=
    E ⊔ rationalNormalClosure K
  let hEU : E ≤ U :=
    le_sup_left
  let hNU : rationalNormalClosure K ≤ U :=
    le_sup_right
  let hKU :
      K ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)) :=
    (IntermediateField.le_normalClosure K).trans hNU
  let d : RelativeIdeleGroup.ClassGroup ℚ U :=
    RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
      (IntermediateField.inclusion hEU) c
  have hzU :
      z = (⟦⟨U, d⟩⟧ : rationalIdeleClassDirectLimit) := by
    exact hzc.trans
      (rationalIdeleClassDirectLimit_mk_apply c hEU).symm
  let : Algebra K U :=
    (IntermediateField.inclusion hKU).toRingHom.toAlgebra
  let : IsScalarTower ℚ K U :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional K U :=
    FiniteDimensional.right ℚ K U
  let : IsGalois K U :=
    IsGalois.tower_top_of_isGalois ℚ K U
  have h_algebraMap (x : K) :
      ((algebraMap K U x : U) : SeparableClosure ℚ) =
        (x : SeparableClosure ℚ) :=
    rfl
  have hd_fixed :=
    rationalTowerRelativeIdeleClass_fixed_of_directLimit_fixed
      K U h_algebraMap d z hzU hz_fixed
  obtain ⟨q, hq⟩ :=
    rationalRelativeIdeleClass_exists_descent_of_tower_fixed
      K U hKU h_algebraMap d hd_fixed
  refine ⟨q, ?_⟩
  calc
    rationalIntermediateIdeleClassToDirectLimit K q =
        (⟦⟨U,
          RelativeIdeleGroup.classEmbedding (K := ℚ)
            (L := rationalNormalClosure K) (M := U)
            (IntermediateField.inclusion hNU)
            (rationalIntermediateIdeleClassToNormalClosure K q)⟩⟧ :
          rationalIdeleClassDirectLimit) :=
      (rationalIdeleClassDirectLimit_mk_apply
        (rationalIntermediateIdeleClassToNormalClosure K q)
        hNU).symm
    _ =
        (⟦⟨U,
          RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
            (IntermediateField.inclusion hKU)
            ((_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K)).symm q)⟩⟧ :
          rationalIdeleClassDirectLimit) := by
      apply congrArg
        (fun a : RelativeIdeleGroup.ClassGroup ℚ U =>
          (⟦⟨U, a⟩⟧ : rationalIdeleClassDirectLimit))
      change
        RelativeIdeleGroup.classEmbedding (K := ℚ)
            (L := rationalNormalClosure K) (M := U)
            (IntermediateField.inclusion hNU)
            (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K)
              (M := rationalNormalClosure K)
              (IntermediateField.inclusion
                (IntermediateField.le_normalClosure K))
              ((_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := K)).symm q)) =
          RelativeIdeleGroup.classEmbedding (K := ℚ) (L := K) (M := U)
            (IntermediateField.inclusion
              ((IntermediateField.le_normalClosure K).trans hNU))
            ((_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K)).symm q)
      exact
        rationalRelativeIdeleClassEmbedding_comp
          (IntermediateField.le_normalClosure K) hNU
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm q)
    _ = ⟦⟨U, d⟩⟧ := by rw [hq]
    _ = z := hzU.symm

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFixedPoints
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Fixed points of the rational idele-class direct limit

The actual idele class group of a finite rational intermediate field is
identified with the corresponding fixed subgroup of the direct limit.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- Additive idele classes map into the fixed subgroup of the rational
idele-class representation. -/
theorem rationalIntermediateIdeleClassToDirectLimit_mem_fixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : Additive (IdeleClassGroup K)) :
    MonoidHom.toAdditive
        (rationalIntermediateIdeleClassToDirectLimit K) c ∈
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K) := by
  change
    (show rationalIdeleClassRepresentation from
      MonoidHom.toAdditive
        (rationalIntermediateIdeleClassToDirectLimit K) c) ∈
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
  rw [KummerTheory.mem_ambientFixedAddSubgroup_iff]
  intro σ
  change
    Additive.ofMul
        (σ.1 •
          rationalIntermediateIdeleClassToDirectLimit K
            (Additive.toMul c)) =
      Additive.ofMul
        (rationalIntermediateIdeleClassToDirectLimit K
          (Additive.toMul c))
  exact congrArg Additive.ofMul
    (rationalIntermediateIdeleClassToDirectLimit_fixed
      K (Additive.toMul c) σ.1 σ.2)

/-- The canonical additive homomorphism from the idele class group of a
finite rational intermediate field to the corresponding fixed subgroup. -/
noncomputable def rationalIntermediateIdeleClassToFixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    Additive (IdeleClassGroup K) →+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K) :=
  (MonoidHom.toAdditive
      (rationalIntermediateIdeleClassToDirectLimit K)).codRestrict
    (KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation
      (RamificationTheory.closedFixingSubgroup
        ℚ (SeparableClosure ℚ) K))
    (rationalIntermediateIdeleClassToDirectLimit_mem_fixed K)

/-- The canonical map from a finite rational idele class group to the
corresponding fixed subgroup is injective. -/
theorem rationalIntermediateIdeleClassToFixed_injective
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    Function.Injective
      (rationalIntermediateIdeleClassToFixed K) := by
  intro a b hab
  have hlim :
      rationalIntermediateIdeleClassToDirectLimit K
          (Additive.toMul a) =
        rationalIntermediateIdeleClassToDirectLimit K
          (Additive.toMul b) := by
    exact congrArg
      (fun z :
          KummerTheory.ambientFixedAddSubgroup
            rationalIdeleClassRepresentation
            (RamificationTheory.closedFixingSubgroup
              ℚ (SeparableClosure ℚ) K) =>
        Additive.toMul
          (z.1 : (rationalIdeleClassRepresentation).V))
      hab
  have hnormal :
      rationalIntermediateIdeleClassToNormalClosure K
          (Additive.toMul a) =
        rationalIntermediateIdeleClassToNormalClosure K
          (Additive.toMul b) :=
    (rationalRelativeIdeleClassToDirectLimit_injective
      (rationalNormalClosure K)) hlim
  have hrelative :
      (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K)).symm (Additive.toMul a) =
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K)).symm (Additive.toMul b) :=
    (rationalRelativeIdeleClassEmbedding_injective
      (IntermediateField.le_normalClosure K)) hnormal
  apply Additive.toMul.injective
  exact
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := K)).symm.injective hrelative

/-- The canonical map from a finite rational idele class group to the
corresponding fixed subgroup is surjective. -/
theorem rationalIntermediateIdeleClassToFixed_surjective
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    Function.Surjective
      (rationalIntermediateIdeleClassToFixed K) := by
  intro x
  let z : rationalIdeleClassDirectLimit :=
    Additive.toMul
      (x.1 : (rationalIdeleClassRepresentation).V)
  have hz_fixed
      (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (hσ : σ ∈ K.fixingSubgroup) :
      σ • z = z := by
    have hfixed := x.2 ⟨σ, hσ⟩
    change Additive.ofMul (σ • z) = Additive.ofMul z at hfixed
    exact Additive.ofMul.injective hfixed
  obtain ⟨q, hqz⟩ :=
    rationalDirectLimit_fixed_exists_ideleClass
      K z hz_fixed
  refine ⟨Additive.ofMul q, ?_⟩
  apply Subtype.ext
  change
    (show rationalIdeleClassRepresentation from
      Additive.ofMul
        (rationalIntermediateIdeleClassToDirectLimit K q)) =
      x.1
  rw [hqz]
  exact
    ofMul_toMul
      (x.1 : Additive rationalIdeleClassDirectLimit)

/-- The subgroup of the absolute idele-class direct limit fixed by the
absolute Galois group over a finite rational intermediate field is
exactly that field's actual idele class group. -/
noncomputable def rationalIdeleClassEquivFixed
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    Additive (IdeleClassGroup K) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K) :=
  AddEquiv.ofBijective
    (rationalIntermediateIdeleClassToFixed K)
    ⟨rationalIntermediateIdeleClassToFixed_injective K,
      rationalIntermediateIdeleClassToFixed_surjective K⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitAbstractFixedField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

/-- The ordinary rational idele class group is the fixed part at the
distinguished base subgroup.  This is `rationalIdeleClassEquivFixed` at
the bottom intermediate field, transported along mathlib's canonical
`ℚ ≃ₐ[ℚ] ⊥` equivalence and the identity
`Gal(ℚ̄/⊥) = baseField`. -/
noncomputable def rationalIdeleClassEquivBaseFixed :
    Additive (IdeleClassGroup ℚ) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) := by
  let B := (⊥ :
    IntermediateField ℚ (SeparableClosure ℚ))
  letI : FiniteDimensional ℚ B :=
    (IntermediateField.botEquiv
      ℚ (SeparableClosure ℚ)).symm.toLinearEquiv.finiteDimensional
  letI : NumberField B :=
    NumberField.of_module_finite ℚ B
  let e : ℚ ≃ₐ[ℚ] B :=
    (IntermediateField.botEquiv
      ℚ (SeparableClosure ℚ)).symm
  let hB :
      RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) B =
        baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    LocalClassFieldTheory.closedFixingSubgroup_bot_eq_baseField
      ℚ (SeparableClosure ℚ)
  exact
    (MulEquiv.toAdditive
      (ideleClassCongr e)).trans
        ((rationalIdeleClassEquivFixed B).trans
          (AddEquiv.addSubgroupCongr
            (congrArg
              (KummerTheory.ambientFixedAddSubgroup
                rationalIdeleClassRepresentation)
              hB)))

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass
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
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_r195b19_1
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
    rationalCyclotomicArtinLocalizedGlobalAlgebra_r195b19_1
    (m : ℕ+) (q : Nat.Primes) :
    Algebra ℚ (rationalCyclotomicArtinLocalizedField m q) :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
noncomputable local instance
    rationalCyclotomicArtinLocalizedScalarTower_r195b19_1
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
    rationalCyclotomicArtinLocalizedFiniteDimensional_r195b19_1
    (m : ℕ+) (q : Nat.Primes) :
    FiniteDimensional
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  finitePlaceLocalArtinFiniteDimensional
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsAbelianGalois_r195b19_1
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
    rationalCyclotomicArtinLocalizedIsCyclotomic_r195b19_1
    (m : ℕ+) (q : Nat.Primes) :
    IsCyclotomicExtension {(m : ℕ)}
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  rationalCyclotomicLevel_localizedCompletion_isCyclotomicExtension
    m (rationalCyclotomicArtinPlace q)
noncomputable local instance
    rationalCyclotomicArtinExtensionFiniteDimensional_r195b19_1
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
    rationalCyclotomicArtinExtensionContinuousSMul_r195b19_1
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
    rationalCyclotomicArtinExtensionLocallyCompact_r195b19_1
    (m : ℕ+) (q : Nat.Primes) :
    LocallyCompactSpace
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  LocallyCompactSpace.of_finiteDimensional_of_complete
    (rationalCyclotomicArtinBaseAbv q).Completion
    (rationalCyclotomicArtinExtension m q).1.Completion
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsUltrametricDist_r195b19_1
    (m : ℕ+) (q : Nat.Primes) :
    IsUltrametricDist
      (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionIsUltrametricDist
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))
noncomputable local instance rationalCyclotomicArtinLocalizedValued_r195b19_1
    (m : ℕ+) (q : Nat.Primes) :
    Valued (rationalCyclotomicArtinLocalizedField m q) ℝ≥0 :=
  localizedCompletionFinitePlaceValued
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuativeRel
noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationCompatible_r195b19_1
    (m : ℕ+) (q : Nat.Primes) :
    (Valued.v : Valuation
      (rationalCyclotomicArtinLocalizedField m q) ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _
noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationHasExtension_r195b19_1
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
    rationalCyclotomicArtinLocalizedValuationIsNontrivial_r195b19_1
    (m : ℕ+) (q : Nat.Primes) :
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q)).IsNontrivial :=
  Valuation.IsNontrivial.of_hasExtension
    (ValuativeRel.valuation
      (rationalCyclotomicArtinBaseAbv q).Completion)
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q))
noncomputable local instance
    rationalCyclotomicArtinLocalizedValuativeRelIsNontrivial_r195b19_1
    (m : ℕ+) (q : Nat.Primes) :
    ValuativeRel.IsNontrivial
      (rationalCyclotomicArtinLocalizedField m q) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q))).2 inferInstance
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsValuativeTopology_r195b19_1
    (m : ℕ+) (q : Nat.Primes) :
    IsValuativeTopology
      (rationalCyclotomicArtinLocalizedField m q) :=
  isValuativeTopology_of_valued_ofValuation
    (rationalCyclotomicArtinLocalizedField m q) ℝ≥0
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField_r195b19_1
    (m : ℕ+) (q : Nat.Primes) :
    IsNonarchimedeanLocalField
      (rationalCyclotomicArtinLocalizedField m q) :=
  { toIsValuativeTopology := inferInstance
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := inferInstance }
noncomputable local instance
    rationalCyclotomicArtinLocalizedIntegerAlgebra_r195b19_1
    (m : ℕ+) (q : Nat.Primes) :
    Algebra
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      (rationalCyclotomicArtinLocalizedField m q) :=
  Algebra.ofSubsemiring
    𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsIntegralClosure_r195b19_1
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
    rationalCyclotomicArtinLocalizedIntegerModuleFinite_r195b19_1
    (m : ℕ+) (q : Nat.Primes) :
    Module.Finite
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      𝒪[rationalCyclotomicArtinLocalizedField m q] :=
  integerRing_moduleFinite_of_isIntegralClosure
    (rationalCyclotomicArtinBaseAbv q).Completion
    (rationalCyclotomicArtinLocalizedField m q)
noncomputable def rationalCyclotomicArtinLocalToGlobalMonoidHom
    (m : ℕ+) (q : Nat.Primes) :
    (rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q) →*
        (rationalCyclotomicArtinLevel m ≃ₐ[ℚ]
          rationalCyclotomicArtinLevel m) :=
  finitePlaceLocalToGlobalMonoidHom
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)

theorem rationalCyclotomicArtinPrimitiveRoot_localization
    (m : ℕ+) (q : Nat.Primes) :
    AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (rationalCyclotomicLevelPrimitiveRoot m) =
      rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q) := by
  rfl

theorem rationalCyclotomicArtinLocalizedRoot_pow
    (m : ℕ+) (q : Nat.Primes) :
    (rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q)) ^ q.1 =
      rationalCyclotomicGlobalToLocalizedAlgHom
        m (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) := by
  calc
    (rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q)) ^ q.1 =
      (rationalCyclotomicGlobalToLocalizedAlgHom
        m (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicLevelPrimitiveRoot m)) ^ q.1 :=
      congrArg (fun z => z ^ q.1)
        (rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot m
          (rationalCyclotomicArtinPlace q)).symm
    _ = rationalCyclotomicGlobalToLocalizedAlgHom
        m (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) :=
      (map_pow
        (rationalCyclotomicGlobalToLocalizedAlgHom
          m (rationalCyclotomicArtinPlace q))
        (rationalCyclotomicLevelPrimitiveRoot m) q.1).symm

end Reciprocity
end GlobalClassFieldTheory
end
end


