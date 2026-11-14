-- Prove2me | Definitions.Def_OAIQ244Duke114
-- name    : OAIQ244Duke114
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T23:45:28.323853+00:00
-- url     : https://prove2.me/theorems/5c1472e0-910a-42dd-99c1-532ef4a32bfa
-- title:
--   Definitions bundle OAIQ244Duke114 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 2 definitions and 13 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.rationalAbstractFixedFieldIdeleClassEquivFixed`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionFixedFieldGalEquivZHat`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_GlobalClassFields_NormConductor`, `GlobalClassFieldTheory_GlobalClassFields_SUnitKummerNormCore`, `GlobalClassFieldTheory_Reciprocity_CyclotomicTorsionFixedField`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitAbstractFixedField`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_BaseComparison_EmbeddedExtensionQuotient`, `LocalClassFieldTheory_Finite_LocalReciprocity_NormResidue`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormalization`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke074`, `OAIQ244Duke075`, `OAIQ244Duke076`, `OAIQ244Duke077` and `OAIQ244Duke078` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke081` and `OAIQ244Duke116`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
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
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finsupp.Fintype
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
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
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
import Mathlib.RingTheory.LocalRing.Module
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
import Definitions.Def_OAIQ244Duke074
import Definitions.Def_OAIQ244Duke075
import Definitions.Def_OAIQ244Duke076
import Definitions.Def_OAIQ244Duke077
import Definitions.Def_OAIQ244Duke078

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_NormConductor
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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
/-- The actual idele-class norm subgroup is open in the ordinary
idele-class topology. -/
theorem ideleClassNorm_range_isOpen :
    IsOpen
      (((_root_.ideleClassNorm K L).range :
        Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) := by
  exact
    (ideleClassNormConductorialSubgroup
      (K := K) (L := L)).isOpen

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SUnitKummerNormCore
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
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

/-- The chosen Kummer norm support is large enough to represent every
idele class by an idele supported on it. -/
theorem supportedAt_sUnitKummerNormSupport_sup_principalSubgroup_eq_top
    (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IdeleGroup.supportedAt
          (K := K)
          (sUnitKummerNormSupport (K := K) n S : Set _) ⊔
        IdeleGroup.principalSubgroup K =
      ⊤ := by
  apply top_unique
  rw [
    ← IdeleGroup.supportedAt_sup_principalSubgroup_eq_top
      (K := K)]
  apply sup_le_sup
  · apply IdeleGroup.supportedAt_mono
    intro v hv
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ hv)
  · exact le_rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicTorsionFixedField
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.closedFixingSubgroup_normal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.LubinTate.standardLubinTateUnitParameter_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

/-- The Galois group of the actual torsion fixed field in
`ℚ(μ∞)` is the additive group of the profinite integers, written
multiplicatively. -/
noncomputable def rationalCyclotomicTorsionFixedFieldGalEquivZHat :
    (rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
      rationalCyclotomicTorsionFixedField) ≃ₜ*
        Multiplicative ZHat := by
  exact rationalCyclotomicTorsionRestrictionEquiv.symm.trans <|
    torsionQuotientEquivOfZHatMulDecomposition
      (rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField)
      CyclotomicFinitePart
      (rationalCyclotomicCharacterContinuousMulEquiv.trans
        zHatUnitsDecomposition)
      dense_torsion_cyclotomicFinitePart

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitAbstractFixedField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

/-- The actual idele class group of the fixed field represented by a
finite-index closed subgroup is the corresponding fixed part of the
rational absolute idele-class representation.  This is the closed-subgroup
endpoint of `rationalIdeleClassEquivFixed`. -/
noncomputable def rationalAbstractFixedFieldIdeleClassEquivFixed
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))] :
    Additive
        (IdeleClassGroup
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) K)) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K := by
  letI : FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K) :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hfinite
  have hclosed :
      RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) K) =
        K :=
    LocalClassFieldTheory.closedFixingSubgroup_abstractFixedField_eq
      ℚ (SeparableClosure ℚ) K
  exact
    (rationalIdeleClassEquivFixed
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K)).trans
      (AddEquiv.addSubgroupCongr
        (congrArg
          (KummerTheory.ambientFixedAddSubgroup
            rationalIdeleClassRepresentation)
          hclosed))

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_BaseComparison_EmbeddedExtensionQuotient
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Embedded extension quotients

This module identifies extension subgroups transported through an embedded finite Galois extension and constructs the resulting ambient quotient equivalence with the actual Galois group.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- The ambient embedded quotient equivalence sends the class of a transported
intrinsic automorphism to its class in the finite Galois quotient. -/
theorem
    ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk
    (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (tau : (intrinsicAbstractBase F).toSubgroup),
      let jF : E →ₐ[F] SeparableClosure K :=
        { j with commutes' := fun x => rfl }
      let jI : E →ₐ[F] SeparableClosure F :=
        e.symm.toAlgHom.comp jF
      let EI :=
        finiteGaloisAbstractExtensionOfEmbedding F E jI
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
        change
          (AlgHom.fieldRange j).fixingSubgroup ≤
            (AlgHom.fieldRange i).fixingSubgroup
        apply (AlgHom.fieldRange i).fixingSubgroup_le
        intro x hx
        rcases hx with ⟨y, rfl⟩
        exact ⟨algebraMap F E y, rfl⟩
      letI _hSourceNormal :
          (extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below).Normal :=
        EI.normal
      letI _hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      ambientEmbeddedExtensionQuotientEquivGaloisGroup
          K F E j e
          (QuotientGroup.mk
            (intrinsicBaseEquivAmbientEmbeddedField
              K F i e tau)) =
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          F E jI (QuotientGroup.mk tau) := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e tau
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  have hmap :
      (extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below).map
          psi.toMonoidHom =
        extensionSubgroup H₀ J₀ hJH := by
    simpa only [i, jF, jI, EI, H₀, J₀, hJH, psi] using
      map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField
        K F E j e
  change
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        F E jI
        ((QuotientGroup.congr
          (extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below)
          (extensionSubgroup H₀ J₀ hJH)
          psi hmap).symm
          (QuotientGroup.mk
            (psi tau))) =
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        F E jI (QuotientGroup.mk tau)
  congr 1
  change
    QuotientGroup.mk
        (psi.symm (psi tau)) =
      QuotientGroup.mk tau
  rw [psi.symm_apply_apply]

/-- Evaluating the ambient embedded quotient class on an element of `E`
agrees, after applying the embedding, with the original ambient automorphism. -/
theorem
    ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
    (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (rho :
        (closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)).toSubgroup)
      (x : E),
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
        change
          (AlgHom.fieldRange j).fixingSubgroup ≤
            (AlgHom.fieldRange i).fixingSubgroup
        apply (AlgHom.fieldRange i).fixingSubgroup_le
        intro y hy
        rcases hy with ⟨z, rfl⟩
        exact ⟨algebraMap F E z, rfl⟩
      letI _hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      j
          (ambientEmbeddedExtensionQuotientEquivGaloisGroup
            K F E j e (QuotientGroup.mk rho) x) =
        rho.1.1 (j x) := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e rho x
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun y => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  have hRange :
      AlgHom.fieldRange i ≤ AlgHom.fieldRange j := by
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact ⟨algebraMap F E z, rfl⟩
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    exact (AlgHom.fieldRange i).fixingSubgroup_le hRange
  let hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  let tau :
      (intrinsicAbstractBase F).toSubgroup :=
    psi.symm rho
  have hpsi : psi tau = rho :=
    psi.apply_symm_apply rho
  have hquotient :
      ambientEmbeddedExtensionQuotientEquivGaloisGroup
          K F E j e (QuotientGroup.mk rho) =
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          F E jI (QuotientGroup.mk tau) := by
    rw [← hpsi]
    exact
      ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk
        K F E j e tau
  rw [hquotient]
  have haction :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
      F E jI tau x
  calc
    j
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          F E jI (QuotientGroup.mk tau) x) =
        e (tau.1 (jI x)) := by
      rw [show
        j
            (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
              F E jI (QuotientGroup.mk tau) x) =
          e
            (jI
              (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
                F E jI (QuotientGroup.mk tau) x)) by
        change
          j
              (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
                F E jI (QuotientGroup.mk tau) x) =
            e
              (e.symm
                (j
                  (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
                    F E jI (QuotientGroup.mk tau) x)))
        rw [e.apply_symm_apply]]
      exact congrArg e haction
    _ = (psi tau).1.1 (j x) := by
      rw [intrinsicBaseEquivAmbientEmbeddedField_apply_val]
      rfl
    _ = rho.1.1 (j x) := by
      rw [hpsi]

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_NormResidue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceLocalizedIsGalois _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The actual abelian local Artin map

For a finite abelian Galois extension, finite local reciprocity takes values
in the actual Galois group, not merely its abelianization.  This module
provides both the algebraic homomorphism and its continuous refinement for
the native topologies.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory
open scoped IsMulCommutative

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The actual abelian local Artin homomorphism is surjective. -/
theorem abelianLocalArtinMonoidHom_surjective :
    Function.Surjective (abelianLocalArtinMonoidHom K L) :=
  (Abelianization.equivOfComm (H := Gal(L / K))).symm.surjective.comp
    (localArtinMonoidHom_surjective K L)

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormalization
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk _root_.LocalClassFieldTheory.normQuotientMapOfRingEquiv_normClass _root_.LocalClassFieldTheory.principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply _root_.LocalClassFieldTheory.principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk _root_.LocalClassFieldTheory.principalUnitsSuccQuotTraceOfUnramifiedValuation_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
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

section BasePrime

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The canonical abstract prime has normalized valuation one modulo every
positive integer after transport to the actual local field. -/
theorem valuationMap_localAbstractPrimeFieldUnit_mod
    (n : ℕ) (hn : 0 < n) :
    (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
        (Additive.ofMul (localAbstractPrimeFieldUnit K)) : ZMod n) = 1 := by
  let v := localHenselianValuation K
  let pi : ambientFixedAddSubgroup (A_p2 K) (B_p2 K) :=
    v.chosenPrimeElement (intrinsicFiniteAbstractBase K)
  have htransport :
      baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul (localAbstractPrimeFieldUnit K)) =
        pi := by
    change
      baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          ((baseUnitsEquivGaloisAmbientFixed K
            (SeparableClosure K)).symm pi) = pi
    exact
      (baseUnitsEquivGaloisAmbientFixed K
        (SeparableClosure K)).apply_symm_apply pi
  have hvalue :=
    localHenselianValuation_valuationAt_baseUnit K
      (localAbstractPrimeFieldUnit K)
  rw [htransport, v.valuationAt_chosenPrimeElement] at hvalue
  have hvalue := hvalue.symm
  change Int.castRingHom ZHat
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
        (Additive.ofMul (localAbstractPrimeFieldUnit K))) = 1 at hvalue
  have hred := congrArg (zHatReduction n hn) hvalue
  simpa only [zHatReduction_int, zHatReduction_one] using hred

end BasePrime

section UnramifiedPrimeClass

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]

variable
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]

omit [IsUniformAddGroup L] in
/-- In the actual unramified norm quotient, the canonical abstract prime and
the chosen inverse DVR uniformizer define the same normalized generator. -/
theorem normClass_localAbstractPrimeFieldUnit_eq_uniformizer :
    normClass K L (localAbstractPrimeFieldUnit K) =
      normClass K L
        (inverseIntegerRingUniformizerFieldUnit K) := by
  apply
    (normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure K L).injective
  rw [normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure_mk,
    normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure_mk,
    valuationModDegreeMulHom_apply,
    valuationModDegreeMulHom_apply,
    valuationMap_localAbstractPrimeFieldUnit_mod K
      (Module.finrank K L) (Module.finrank_pos),
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply,
    v_inverseIntegerRingUniformizerFieldUnit]
  simp

/-! ## Canonical norm-residue normalization -/

omit [IsUniformAddGroup L] in
/-- The canonical norm-residue symbol sends the transported abstract prime to
the arithmetic Frobenius class. -/
theorem localArtinMonoidHom_localAbstractPrimeFieldUnit :
    localArtinMonoidHom K L (localAbstractPrimeFieldUnit K) =
      Abelianization.of
        (arithmeticFrobeniusOfUnramifiedValuation K L) := by
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L
  let D := localResidueDatum K
  let v := localHenselianValuation K
  let hcf := separableClosureUnits_isClassFormation K
  let E := finiteGaloisAbstractExtensionOfEmbedding K L i
  let Kbase := intrinsicFiniteAbstractBase K
  let KR := Kbase.toFiniteResidueAbstractField D
  let hEfinite : Finite ((B_p2 K).toSubgroup ⧸
      extensionSubgroup (B_p2 K) E.field E.below) :=
    E.finite
  let hKbaseEfinite : Finite (Kbase.field.toSubgroup ⧸
      extensionSubgroup Kbase.field E.field E.below) := by
    exact Finite.of_equiv
      ((B_p2 K).toSubgroup ⧸
        extensionSubgroup (B_p2 K) E.field E.below)
      (extensionQuotientEquivOfEq
        (K := B_p2 K) (L := E.field)
        (K' := Kbase.field) (L' := E.field)
        E.below E.below rfl rfl)
  let hKREfinite : Finite (KR.field.toSubgroup ⧸
      extensionSubgroup KR.field E.field E.below) := by
    exact Finite.of_equiv
      ((B_p2 K).toSubgroup ⧸
        extensionSubgroup (B_p2 K) E.field E.below)
      (extensionQuotientEquivOfEq
        (K := B_p2 K) (L := E.field)
        (K' := KR.field) (L' := E.field)
        E.below E.below rfl rfl)
  let sigma := D.chosenUnramifiedFrobeniusLift KR E.field E.below
  let q := D.unramifiedFrobenius KR E.field E.below
  have hUnramified : E.IsUnramified D := by
    simpa only [D, E, B_p2] using
      finiteGaloisAbstractExtensionOfEmbedding_isUnramified K L i
  let S := D.frobeniusFixedField KR E.field E.below sigma
  let hSB := D.frobeniusFixedField_le
    KR E.field E.below sigma
  let hSBfinite :
      Finite ((B_p2 K).toSubgroup ⧸
        extensionSubgroup (B_p2 K) S hSB) :=
    D.frobeniusFixedField_finite
      KR E.field E.below sigma
  let hSabsoluteFinite :
      Finite ((baseField (G_p3 K)).toSubgroup ⧸
        extensionSubgroup (baseField (G_p3 K)) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite
      Kbase E.field E.below sigma
  let Sfinite : FiniteAbstractField (G_p3 K) := ⟨S, hSabsoluteFinite⟩
  let pi : ambientFixedAddSubgroup (A_p2 K) S :=
    fixedFieldInclusion (A_p2 K) (B_p2 K) S hSB
      (v.chosenPrimeElement Kbase)
  have hpi : v.IsPrimeElement Sfinite pi := by
    simpa only [Kbase, KR, sigma, S, hSB, Sfinite, pi] using
      v.unramifiedFrobenius_includedPrime_isPrime
        Kbase E.field E.below hUnramified
  have hnorm :
      relativeNorm (A_p2 K) (B_p2 K) S hSB pi =
        v.chosenPrimeElement Kbase := by
    simpa only [Kbase, KR, sigma, S, hSB, pi] using
      v.unramifiedFrobenius_primeNorm
        Kbase E.field E.below hUnramified
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  let xNorm : Kˣ :=
    Additive.toMul
      (e.symm (relativeNorm (A_p2 K) (B_p2 K) S hSB pi))
  have hxNorm :
      e (Additive.ofMul xNorm) =
        relativeNorm (A_p2 K) (B_p2 K) S hSB pi := by
    exact e.apply_symm_apply _
  have hsymbol :=
    concreteNormResidueSymbolOfEmbedding_apply_primeNorm
      K L i D v hcf q sigma (by rfl) pi hpi xNorm hxNorm
  dsimp only [xNorm] at hsymbol
  have hx :
      Additive.toMul
          (e.symm (relativeNorm (A_p2 K) (B_p2 K) S hSB pi)) =
        localAbstractPrimeFieldUnit K := by
    rw [hnorm]
    rfl
  change
    concreteNormResidueSymbolOfEmbedding K L i D v hcf
        (Additive.toMul
          (e.symm (relativeNorm (A_p2 K) (B_p2 K) S hSB pi))) =
      Abelianization.of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q)
    at hsymbol
  rw [hx, ← localArtinMonoidHom_eq_of_embedding K L i] at hsymbol
  have hq :
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q =
        arithmeticFrobeniusOfUnramifiedValuation K L := by
    rw [←
      finiteGaloisAbstractUnramifiedFrobenius_eq_arithmeticFrobenius
        K L i]
    rfl
  rw [hq] at hsymbol
  exact hsymbol

/-! ## Equality with the field-facing unramified reciprocity map -/

/-- On an unramified extension, the inverse of the canonical reciprocity
isomorphism is exactly the field-facing Frobenius-normalized isomorphism. -/
theorem abelianizationEquivNormQuotient_symm_eq_unramifiedLocalReciprocityIso :
    (abelianizationEquivNormQuotient K L).symm =
      unramifiedLocalReciprocityIso K L := by
  let p : NormQuotient K L :=
    normClass K L (localAbstractPrimeFieldUnit K)
  let e :=
    normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure K L
  have hep :
      e p =
        Multiplicative.ofAdd
          (1 : ZMod (Module.finrank K L)) := by
    change e
      (normClass K L (localAbstractPrimeFieldUnit K)) = _
    rw [normClass_localAbstractPrimeFieldUnit_eq_uniformizer
      K L]
    rw [normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure_mk,
      valuationModDegreeMulHom_apply,
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply,
      v_inverseIntegerRingUniformizerFieldUnit]
    simp
  have hpowers (z : NormQuotient K L) :
      ∃ m : ℤ, p ^ m = z := by
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective (e z).toAdd
    refine ⟨m, ?_⟩
    apply e.injective
    rw [map_zpow, hep]
    rw [← ofAdd_zsmul]
    apply Multiplicative.ext
    simpa [zsmul_eq_mul] using hm
  have hcanonical :
      (abelianizationEquivNormQuotient K L).symm p =
        Abelianization.of
          (arithmeticFrobeniusOfUnramifiedValuation K L) := by
    change localArtinMonoidHom K L (localAbstractPrimeFieldUnit K) = _
    exact localArtinMonoidHom_localAbstractPrimeFieldUnit K L
  have hactual :
      unramifiedLocalReciprocityIso K L p =
        Abelianization.of
          (arithmeticFrobeniusOfUnramifiedValuation K L) := by
    change unramifiedLocalReciprocityIso K L
      (normClass K L (localAbstractPrimeFieldUnit K)) =
        _
    rw [normClass_localAbstractPrimeFieldUnit_eq_uniformizer
      K L]
    exact
      unramifiedLocalReciprocityIso_inverseIntegerRingUniformizerFieldUnit
        K L
  apply MulEquiv.ext
  intro z
  obtain ⟨m, rfl⟩ := hpowers z
  rw [map_zpow, map_zpow, hcanonical, hactual]

/-- The canonical local norm-residue symbol is the field-facing unramified
Artin map. -/
theorem localArtinMonoidHom_eq_unramifiedLocalArtinMap :
    localArtinMonoidHom K L =
      unramifiedLocalArtinMap K L := by
  apply MonoidHom.ext
  intro x
  change
    (abelianizationEquivNormQuotient K L).symm (normClass K L x) =
      unramifiedLocalReciprocityIso K L
        (normClass K L x)
  rw [abelianizationEquivNormQuotient_symm_eq_unramifiedLocalReciprocityIso K L]

/-- Frobenius normalization on the chosen inverse prime element. -/
@[simp]
theorem localArtinMonoidHom_inverseIntegerRingUniformizerFieldUnit :
    localArtinMonoidHom K L
        (inverseIntegerRingUniformizerFieldUnit K) =
      Abelianization.of
        (arithmeticFrobeniusOfUnramifiedValuation K L) := by
  rw [localArtinMonoidHom_eq_unramifiedLocalArtinMap K L]
  change
    unramifiedLocalReciprocityIso K L
        (normClass K L
          (inverseIntegerRingUniformizerFieldUnit K)) =
      Abelianization.of
        (arithmeticFrobeniusOfUnramifiedValuation K L)
  exact
    unramifiedLocalReciprocityIso_inverseIntegerRingUniformizerFieldUnit
      K L

/-- Full unramified Artin formula for the canonical local norm-residue symbol. -/
theorem localArtinMonoidHom_eq_frobenius_zpow (x : Kˣ) :
    localArtinMonoidHom K L x =
      (Abelianization.of
        (arithmeticFrobeniusOfUnramifiedValuation K L)) ^
          LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
            (Additive.ofMul x) := by
  rw [localArtinMonoidHom_eq_unramifiedLocalArtinMap K L]
  exact unramifiedLocalArtinMap_eq_frobenius_zpow K L x

/-! ## Continuous Frobenius normalization -/

end UnramifiedPrimeClass

section AbelianUnramifiedPrimeClass

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]

/-- The canonical local Artin map for an abelian unramified extension sends
each field unit to actual arithmetic Frobenius raised to its normalized valuation. -/
theorem abelianLocalArtinMonoidHom_eq_frobenius_zpow (x : Kˣ) :
    abelianLocalArtinMonoidHom K L x =
      (arithmeticFrobeniusOfUnramifiedValuation K L) ^
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul x) := by
  simp only [abelianLocalArtinMonoidHom, MonoidHom.coe_comp,
    Function.comp_apply]
  rw [localArtinMonoidHom_eq_frobenius_zpow K L x, map_zpow]
  exact
    congrArg
      (fun σ : Gal(L / K) =>
        σ ^ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul x))
      ((Abelianization.equivOfComm (H := Gal(L / K))).symm_apply_apply
        (arithmeticFrobeniusOfUnramifiedValuation K L))

end AbelianUnramifiedPrimeClass

end LocalClassFieldTheory
end
end


