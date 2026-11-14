-- Prove2me | Definitions.Def_OAIQ244Duke109
-- name    : OAIQ244Duke109
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T03:56:17.193619+00:00
-- url     : https://prove2.me/theorems/948043a2-a934-4ab6-a192-c63ac0830b45
-- title:
--   Definitions bundle OAIQ244Duke109 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 9 definitions and 20 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationLowerSeparableClosureEmbedding`, `GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfieldSeparableClosureEmbedding`, `GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedBaseChangeBaseEquiv`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceNormedOverextensionNormResidueNegOneValue`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionGlobalNormResidueNegOneValue`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNegOneIdeleClass`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionRestriction`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedPlace`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRestrictedOverextensionNormResidueNegOneValue`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_AbstractFixedFieldGlobalNormResidue`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceCompatibility`, `GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke104` and `OAIQ244Duke105` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke111`; the statement `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_neg_one`; the proof of `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextension_globalNormResidueOfEmbedding_neg_one`.
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
import Definitions.Def_OAIQ244Duke104
import Definitions.Def_OAIQ244Duke105

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_AbstractFixedFieldGlobalNormResidue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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
# Global norm residue on actual fixed fields

An abstract finite abelian subextension of the rational absolute Galois
group determines an actual finite abelian extension between its two
fixed number fields.  This file transports the abstract norm-residue
symbol directly to the ordinary idele-class norm quotient of those
fixed fields.

Keeping this construction in one ambient separable closure is essential
for the norm--restriction diagrams: no independently chosen embedding of
either field is introduced.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

section EmbeddedNumberFieldRestriction

variable
    (K K' L L' : Type)
    [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Field L] [NumberField L]
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']

/-- A compatible common embedding reverses the inclusion of the two base
fields into an inclusion of their fixing subgroups. -/
theorem numberFieldEmbeddedBaseSubgroup_le_of_tower
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    (numberFieldEmbeddedBaseSubgroup K' L' j).toSubgroup ≤
      (numberFieldEmbeddedBaseSubgroup K L jLower).toSubgroup := by
  dsimp only
  change
    (numberFieldEmbeddedLowerEmbedding K' L' j).fieldRange.fixingSubgroup ≤
      (numberFieldEmbeddedLowerEmbedding K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))).fieldRange.fixingSubgroup
  apply
    (numberFieldEmbeddedLowerEmbedding K L
      (j.comp (IsScalarTower.toAlgHom ℚ L L'))).fieldRange.fixingSubgroup_le
  intro x hx
  rcases hx with ⟨y, rfl⟩
  refine ⟨algebraMap K K' y, ?_⟩
  change
    j (algebraMap K' L' (algebraMap K K' y)) =
      j (algebraMap L L' (algebraMap K L y))
  rw [← IsScalarTower.algebraMap_apply K K' L',
    ← IsScalarTower.algebraMap_apply K L L']

omit [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Algebra K K'] [Algebra K L] [Algebra K L'] [Algebra K' L']
    [IsScalarTower K K' L'] [IsScalarTower K L L'] in
/-- A compatible common embedding reverses the inclusion of the two top
fields into an inclusion of their fixing subgroups. -/
theorem numberFieldEmbeddedTopSubgroup_le_of_tower
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    (numberFieldEmbeddedTopSubgroup K' L' j).toSubgroup ≤
      (numberFieldEmbeddedTopSubgroup K L jLower).toSubgroup := by
  dsimp only
  change
    j.fieldRange.fixingSubgroup ≤
      (j.comp
        (IsScalarTower.toAlgHom ℚ L L')).fieldRange.fixingSubgroup
  apply
    (j.comp
      (IsScalarTower.toAlgHom ℚ L L')).fieldRange.fixingSubgroup_le
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact ⟨algebraMap L L' y, rfl⟩

end EmbeddedNumberFieldRestriction

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality
attribute [-instance] _root_.ClassFormation.FiniteAbelianSubextension.normOpenAddSubgroupPartialOrder _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Naturality of the global norm-residue symbol

This file records the same-base restriction specialization of abstract
norm-residue naturality in the rational absolute class formation.  All
closed subgroups remain in one fixed separable-closure ambient, so the
statement is directly usable by fixed-field overextension arguments.
-/

open scoped IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

universe u

attribute [local instance] naturalityIdeleClassCommGroup

local instance ideleClassGroupIsMulCommutative_r7c11b6_1
    {F : Type} [Field F] [NumberField F]
    : IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
local instance ideleClassSubgroupNormal_r7c11b6_1
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative
/-- Transporting an additive equivalence between rational ambient fixed
subgroups does not change the underlying direct-limit class. -/
theorem rationalAmbientFixedAddEquiv_transport_apply_val
    {A B : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (hAB : A = B)
    {X : Type} [AddGroup X]
    (e : X ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation A.field)
    (x : X) :
    ((Eq.mp
        (congrArg
          (fun Y : FiniteAbstractField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
            X ≃+ ambientFixedAddSubgroup
              rationalIdeleClassRepresentation Y.field)
          hAB)
        e x).1) =
      (e x).1 := by
  cases hAB
  rfl

/-- Transporting an idele class along a field equality and the corresponding
algebra equivalence leaves its rational direct-limit representative fixed. -/
theorem rationalIdeleClassEquivFixed_congr_apply_val
    {A B : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (h : A = B)
    (e : B ≃ₐ[ℚ] A)
    (he : e.trans (IntermediateField.equivOfEq h) =
      (AlgEquiv.refl : B ≃ₐ[ℚ] B))
    (c : Additive (IdeleClassGroup B)) :
    ((rationalIdeleClassEquivFixed A)
        (MulEquiv.toAdditive (ideleClassCongr e) c)).1 =
      ((rationalIdeleClassEquivFixed B) c).1 := by
  cases h
  have he' : e = AlgEquiv.refl := by
    apply AlgEquiv.ext
    intro x
    have hx := DFunLike.congr_fun he x
    change e x = x at hx
    exact hx
  rw [he']
  have hc :
      MulEquiv.toAdditive
          (ideleClassCongr (AlgEquiv.refl : A ≃ₐ[ℚ] A)) c = c := by
    cases c with
    | ofMul c =>
        exact congrArg Additive.ofMul (ideleClassCongr_refl c)
  rw [hc]

/-- Transporting the target intermediate field of a base-field equivalence
preserves its rational fixed-part representative. -/
theorem rationalIdeleClassEquivFixed_transport_baseEquiv_val
    {T : Type} [Field T] [NumberField T]
    {A B : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (h : A = B) (e : T ≃ₐ[ℚ] B)
    (c : IdeleClassGroup T) :
    ((rationalIdeleClassEquivFixed A)
      (Additive.ofMul
        (ideleClassCongr (K := T) (M := A)
          (e.trans (IntermediateField.equivOfEq h).symm) c))).1 =
    ((rationalIdeleClassEquivFixed B)
      (Additive.ofMul (ideleClassCongr (K := T) (M := B) e c))).1 := by
  cases h
  have he :
      e.trans (IntermediateField.equivOfEq (rfl : A = A)).symm = e := by
    ext x
    rfl
  rw [he]

section EmbeddedNumberFieldRestriction

local instance ideleClassGroupIsMulCommutative_r7c11b6_2
    {F : Type} [Field F] [NumberField F]
    : IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
local instance ideleClassSubgroupNormal_r7c11b6_2
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative
variable
    (K K' L L' : Type)
    [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Field L] [NumberField L]
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']


/-- Rebracketing the compatible tower does not change its embedded lower
fixing subgroup. -/
theorem numberFieldEmbeddedBaseSubgroup_baseChange_eq
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    numberFieldEmbeddedBaseSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j) =
      numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L')) := by
  have hi :
      numberFieldEmbeddedLowerEmbedding K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j) =
        numberFieldEmbeddedLowerEmbedding K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L')) := by
    ext x
    simp only [numberFieldEmbeddedLowerEmbedding, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']
    rw [← IsScalarTower.algebraMap_apply K K' L',
      ← IsScalarTower.algebraMap_apply K L L']
  simp only [numberFieldEmbeddedBaseSubgroup, hi]

omit [Field K] [NumberField K]
    [Algebra K K'] [Algebra K L'] [IsScalarTower K K' L'] in
/-- The top subgroup of the rebracketed base-change tower is the embedded
fixing subgroup of the intermediate field. -/
theorem numberFieldEmbeddedTopSubgroup_baseChange_eq
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    numberFieldEmbeddedTopSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j) =
      numberFieldEmbeddedBaseSubgroup K' L' j := by
  rfl

/-- Reidentify the two presentations of the embedded lower fixing subgroup
without transporting dependent subgroup data through an equality. -/
noncomputable def numberFieldEmbeddedBaseChangeBaseEquiv
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    (numberFieldEmbeddedBaseSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup ≃*
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup :=
  MulEquiv.subgroupCongr
    (congrArg ClosedSubgroup.toSubgroup
      (numberFieldEmbeddedBaseSubgroup_baseChange_eq K K' L L' j))

/-- Under the identity equivalence of the two lower fixing subgroups, the
relative subgroup for the base change is exactly the target presentation. -/
theorem numberFieldEmbeddedBaseChangeExtensionSubgroup_map_eq
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j))
        (numberFieldEmbeddedTopSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j))
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j))).map
          (numberFieldEmbeddedBaseChangeBaseEquiv K K' L L' j).toMonoidHom =
      CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L')))
        (numberFieldEmbeddedBaseSubgroup K' L' j)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j) := by
  let e := numberFieldEmbeddedBaseChangeBaseEquiv K K' L L' j
  have hTop :
      (numberFieldEmbeddedTopSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup =
        (numberFieldEmbeddedBaseSubgroup K' L' j).toSubgroup :=
    congrArg ClosedSubgroup.toSubgroup
      (numberFieldEmbeddedTopSubgroup_baseChange_eq
        (K := K) (K' := K') (L' := L') j)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change
      ((e y :
          (numberFieldEmbeddedBaseSubgroup K L
            (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup) :
          SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ∈
        (numberFieldEmbeddedBaseSubgroup K' L' j).toSubgroup
    dsimp only [e, numberFieldEmbeddedBaseChangeBaseEquiv]
    rw [MulEquiv.subgroupCongr_apply, ← hTop]
    exact hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change
      (((e.symm x :
          (numberFieldEmbeddedBaseSubgroup K K'
            (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup) :
          SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ∈
        (numberFieldEmbeddedTopSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup)
    dsimp only [e, numberFieldEmbeddedBaseChangeBaseEquiv]
    rw [MulEquiv.subgroupCongr_symm_apply, hTop]
    exact hx

/-- Normality of the relative subgroup between the two embedded base fields
in a finite Galois base change. -/
theorem numberFieldEmbeddedBaseChangeExtensionSubgroup_normal
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L')))
      (numberFieldEmbeddedBaseSubgroup K' L' j)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)).Normal := by
  let e := numberFieldEmbeddedBaseChangeBaseEquiv K K' L L' j
  have hNormal :=
    (numberFieldEmbeddedExtensionSubgroup_normal K K'
      (numberFieldEmbeddedLowerEmbedding K' L' j)).map
        e.toMonoidHom e.surjective
  rw [numberFieldEmbeddedBaseChangeExtensionSubgroup_map_eq
    K K' L L' j] at hNormal
  exact hNormal

noncomputable local instance
    numberFieldEmbeddedBaseChangeExtensionSubgroupNormal
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    (CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L')))
      (numberFieldEmbeddedBaseSubgroup K' L' j)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)).Normal :=
  numberFieldEmbeddedBaseChangeExtensionSubgroup_normal K K' L L' j

/-- Finiteness of the relative quotient between the two embedded base fields
in a finite Galois base change. -/
theorem numberFieldEmbeddedBaseChangeExtensionQuotient_finite
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K L
            (j.comp (IsScalarTower.toAlgHom ℚ L L')))
          (numberFieldEmbeddedBaseSubgroup K' L' j)
          (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) := by
  let e := numberFieldEmbeddedBaseChangeBaseEquiv K K' L L' j
  let N :=
    CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j))
      (numberFieldEmbeddedTopSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j))
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K K'
        (numberFieldEmbeddedLowerEmbedding K' L' j))
  let M :=
    CyclicCohomology.extensionSubgroup
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L')))
      (numberFieldEmbeddedBaseSubgroup K' L' j)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)
  let hNNormal : N.Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K K'
      (numberFieldEmbeddedLowerEmbedding K' L' j)
  let hMNormal : M.Normal :=
    numberFieldEmbeddedBaseChangeExtensionSubgroup_normal K K' L L' j
  let hNFinite :
      Finite
        ((numberFieldEmbeddedBaseSubgroup K K'
            (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup ⧸ N) :=
    numberFieldEmbeddedExtensionQuotient_finite K K'
      (numberFieldEmbeddedLowerEmbedding K' L' j)
  have hmap : N.map e.toMonoidHom = M :=
    numberFieldEmbeddedBaseChangeExtensionSubgroup_map_eq K K' L L' j
  have hle : N ≤ M.comap e.toMonoidHom := by
    rw [← hmap]
    exact Subgroup.le_comap_map e.toMonoidHom N
  let f :
      ((numberFieldEmbeddedBaseSubgroup K K'
          (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup ⧸ N) →*
        ((numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup ⧸ M) :=
    QuotientGroup.map N M e.toMonoidHom hle
  have hmk : Function.Surjective
      (QuotientGroup.mk ∘ e :
        (numberFieldEmbeddedBaseSubgroup K K'
            (numberFieldEmbeddedLowerEmbedding K' L' j)).toSubgroup →
          (numberFieldEmbeddedBaseSubgroup K L
              (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup ⧸ M) :=
    QuotientGroup.mk_surjective.comp e.surjective
  have hsurj : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective
      (N := N) M e.toMonoidHom hmk hle
  exact Finite.of_surjective f hsurj

noncomputable local instance
    numberFieldEmbeddedBaseChangeExtensionQuotientFinite
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    Finite
      ((numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K L
            (j.comp (IsScalarTower.toAlgHom ℚ L L')))
          (numberFieldEmbeddedBaseSubgroup K' L' j)
          (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  numberFieldEmbeddedBaseChangeExtensionQuotient_finite K K' L L' j

/-- Reuse the canonical absolute fixed-field witness for the lower embedded
tower.  The base-change relative witness below needs this exact instance path
when forming the absolute finite-dimensional tower. -/
noncomputable local instance
    numberFieldEmbeddedBaseChangeBaseFixedFieldFiniteDimensional
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L')))) :=
  numberFieldEmbeddedAbstractFixedFieldFiniteDimensional K L
    (j.comp (IsScalarTower.toAlgHom ℚ L L'))

noncomputable local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldFiniteDimensional
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L
      (j.comp (IsScalarTower.toAlgHom ℚ L L')))
    (numberFieldEmbeddedBaseSubgroup K' L' j)
    (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)
    (numberFieldEmbeddedAbsoluteQuotientFinite K L
      (j.comp (IsScalarTower.toAlgHom ℚ L L')))
    (numberFieldEmbeddedBaseChangeExtensionQuotientFinite K K' L L' j)

local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldScalarTower
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldAbsoluteFiniteDimensional
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))))
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j))

noncomputable local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldNumberField
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j))

noncomputable local instance
    numberFieldEmbeddedBaseChangeRelativeFixedFieldIsGalois_r7c11b6_1
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L'))))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L
      (j.comp (IsScalarTower.toAlgHom ℚ L L')))
    (numberFieldEmbeddedBaseSubgroup K' L' j)
    (numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j)
    (numberFieldEmbeddedBaseChangeExtensionSubgroupNormal K K' L L' j)
/-- In one common rational-separable-closure realization, the canonical
quotient-to-Galois comparisons intertwine abstract restriction with
ordinary restriction of the actual number-field automorphisms. -/
theorem
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup_restriction
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ)
    (z :
      Abelianization
        (numberFieldEmbeddedFiniteGaloisSubextension
          K' L' j).extensionQuotient) :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    let H :=
      numberFieldEmbeddedBaseSubgroup K L jLower
    let H' :=
      numberFieldEmbeddedBaseSubgroup K' L' j
    let J :=
      numberFieldEmbeddedTopSubgroup K L jLower
    let J' :=
      numberFieldEmbeddedTopSubgroup K' L' j
    let hH'H :=
      numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
    let hJ'J :=
      numberFieldEmbeddedTopSubgroup_le_of_tower K K' L L' j
    let hJH :=
      numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L jLower
    let hJ'H' :=
      numberFieldEmbeddedTopSubgroup_le_baseSubgroup K' L' j
    letI _ :
        (CyclicCohomology.extensionSubgroup H J hJH).Normal :=
      numberFieldEmbeddedExtensionSubgroup_normal K L jLower
    letI _ :
        (CyclicCohomology.extensionSubgroup H' J' hJ'H').Normal :=
      numberFieldEmbeddedExtensionSubgroup_normal K' L' j
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (Additive.toMul
          (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
            K' L' j (Additive.ofMul z))) =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L jLower
          (MonoidHom.toAdditive
            (normResidueNaturalityAbelianizedRestriction
              H H' J J'
              hJH hJ'H'
              hH'H hJ'J)
            (Additive.ofMul z))) := by
  dsimp only
  let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
    j.comp (IsScalarTower.toAlgHom ℚ L L')
  let H :=
    numberFieldEmbeddedBaseSubgroup K L jLower
  let H' :=
    numberFieldEmbeddedBaseSubgroup K' L' j
  let J :=
    numberFieldEmbeddedTopSubgroup K L jLower
  let J' :=
    numberFieldEmbeddedTopSubgroup K' L' j
  let hH'H :=
    numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
  let hJ'J :=
    numberFieldEmbeddedTopSubgroup_le_of_tower K K' L L' j
  let hJH :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup
      K L jLower
  let hJ'H' :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup
      K' L' j
  let hLowerNormal :
      (CyclicCohomology.extensionSubgroup H J hJH).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K L jLower
  let hUpperNormal :
      (CyclicCohomology.extensionSubgroup H' J' hJ'H').Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K' L' j
  let qLower :=
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup
      K L jLower
  let qUpper :=
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup
      K' L' j
  let qLowerRaw :
      (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H J hJH) ≃*
        Gal(L / K) := by
    exact
      { qLower.toEquiv with
        map_mul' := fun x y => qLower.map_mul x y }
  let qUpperRaw :
      (H'.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H' J' hJ'H') ≃*
        Gal(L' / K') := by
    exact
      { qUpper.toEquiv with
        map_mul' := fun x y => qUpper.map_mul x y }
  let restrictActual :
      Gal(L' / K') →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  obtain ⟨q, rfl⟩ :=
    QuotientGroup.mk_surjective z
  obtain ⟨σ, rfl⟩ :=
    (numberFieldEmbeddedFiniteGaloisSubextension
      K' L' j).extensionQuotientMk_surjective q
  change
    restrictActual
        ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
          (qUpperRaw.abelianizationCongr
            (Abelianization.of (QuotientGroup.mk σ)))) =
      (Abelianization.equivOfComm (H := Gal(L / K))).symm
        (qLowerRaw.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            H H' J J' hJH hJ'H' hH'H hJ'J
            (Abelianization.of (QuotientGroup.mk σ))))
  rw [normResidueNaturalityAbelianizedRestriction_of_mk,
    abelianizationCongr_of, abelianizationCongr_of]
  change
    restrictActual (qUpperRaw (QuotientGroup.mk σ)) =
      qLowerRaw
        (QuotientGroup.mk (Subgroup.inclusion hH'H σ))
  apply AlgEquiv.ext
  intro x
  apply jLower.injective
  let hUpperAlgebra : Algebra K' (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K' L' j
  let eUpper :=
    numberFieldEmbeddedSeparableClosureEquiv K' L' j
  let hLowerAlgebra : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L jLower
  let eLower :=
    numberFieldEmbeddedSeparableClosureEquiv K L jLower
  calc
    jLower
        (restrictActual
          (qUpperRaw (QuotientGroup.mk σ)) x) =
        j
          ((qUpperRaw (QuotientGroup.mk σ))
            (algebraMap L L' x)) := by
      exact congrArg j
        (AlgEquiv.restrictNormal_commutes
          ((AlgEquiv.restrictScalarsHom K)
            (qUpperRaw (QuotientGroup.mk σ)))
          L x)
    _ = σ.1.1
        (j (algebraMap L L' x)) := by
      exact
        ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
          ℚ K' L' j eUpper σ (algebraMap L L' x)
    _ = (Subgroup.inclusion hH'H σ).1.1
        (jLower x) := rfl
    _ = jLower
        (qLowerRaw
          (QuotientGroup.mk
            (Subgroup.inclusion hH'H σ)) x) := by
      exact
        (ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
          ℚ K L jLower eLower
          (Subgroup.inclusion hH'H σ) x).symm

/-- In a compatible common embedding, the fixed-part relative norm
between two (Galois-related) base fields is the genuine ordinary
idele-class norm. -/
theorem numberFieldEmbeddedIdeleClassEquivAmbientFixed_relativeNorm
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K') :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    let H :=
      numberFieldEmbeddedBaseSubgroup K L jLower
    let H' :=
      numberFieldEmbeddedBaseSubgroup K' L' j
    let hH'H :=
      numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
    letI _ : Finite
        (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H H' hH'H) :=
      numberFieldEmbeddedBaseChangeExtensionQuotientFinite
        K K' L L' j
    relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (numberFieldEmbeddedIdeleClassEquivAmbientFixed
          K' L' j (Additive.ofMul c)) =
      numberFieldEmbeddedIdeleClassEquivAmbientFixed
        K L jLower
        (Additive.ofMul (_root_.ideleClassNorm K K' c)) := by
  intro jLower H H'
  let hH'H :=
    numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
  let hnormal :=
    numberFieldEmbeddedBaseChangeExtensionSubgroupNormal K K' L L' j
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H
  let E :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ) hH'H
  let _ :
      (CyclicCohomology.extensionSubgroup H H' hH'H).Normal :=
    hnormal
  let _ :
      Finite
        (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H H' hH'H) :=
    numberFieldEmbeddedBaseChangeExtensionQuotientFinite
      K K' L L' j
  let _ :
      Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            H (le_baseField H)) :=
    numberFieldEmbeddedAbsoluteQuotientFinite K L jLower
  let _ : NumberField F :=
    numberFieldEmbeddedAbstractFixedFieldNumberField K L jLower
  let _ : NumberField E :=
    numberFieldEmbeddedBaseChangeRelativeFixedFieldNumberField
      K K' L L' j
  let _ : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ E
    exact
      numberFieldEmbeddedBaseChangeRelativeFixedFieldAbsoluteFiniteDimensional
        K K' L L' j
  let _ : NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) H') :=
    numberFieldEmbeddedAbstractFixedFieldNumberField K' L' j
  have hE :
      E.restrictScalars ℚ =
        abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    IntermediateField.extendScalars_restrictScalars
      (abstractFixedField_le
        ℚ (SeparableClosure ℚ) hH'H)
  let eRel :
      E ≃ₐ[ℚ]
        abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    IntermediateField.equivOfEq hE
  let eK :
      K ≃ₐ[ℚ] F :=
    numberFieldEmbeddedAbstractBaseFieldEquiv K L jLower
  let eK'Base :
      K' ≃ₐ[ℚ]
        abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    numberFieldEmbeddedAbstractBaseFieldEquiv K' L' j
  let eK' : K' ≃ₐ[ℚ] E :=
    eK'Base.trans eRel.symm
  have hcompat (x : K) :
      eK' (algebraMap K K' x) =
        algebraMap F E (eK x) := by
    apply eRel.injective
    apply Subtype.ext
    change
      j (algebraMap K' L' (algebraMap K K' x)) =
        j (algebraMap L L' (algebraMap K L x))
    rw [← IsScalarTower.algebraMap_apply K K' L',
      ← IsScalarTower.algebraMap_apply K L L']
  have hupper :
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          H H' hH'H
          (Additive.ofMul (ideleClassCongr eK' c)) =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed
          K' L' j (Additive.ofMul c) := by
    apply Subtype.ext
    change
      ((rationalIdeleClassEquivFixed (E.restrictScalars ℚ))
          (Additive.ofMul (ideleClassCongr eK' c))).1 =
        ((rationalIdeleClassEquivFixed
            (abstractFixedField ℚ (SeparableClosure ℚ) H'))
          (Additive.ofMul (ideleClassCongr eK'Base c))).1
    exact rationalIdeleClassEquivFixed_transport_baseEquiv_val
      (T := K') (A := E.restrictScalars ℚ)
      (B := abstractFixedField ℚ (SeparableClosure ℚ) H') hE eK'Base c
  have hrelative :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_relativeNorm
      H H' hH'H hnormal
        (Additive.ofMul (ideleClassCongr eK' c))
  change
    relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          H H' hH'H
          (Additive.ofMul (ideleClassCongr eK' c))) =
      rationalAbstractFixedFieldIdeleClassEquivFixed H
        (Additive.ofMul
          (_root_.ideleClassNorm F E
            (ideleClassCongr eK' c)))
    at hrelative
  calc
    relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (numberFieldEmbeddedIdeleClassEquivAmbientFixed
          K' L' j (Additive.ofMul c)) =
      relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          H H' hH'H (Additive.ofMul (ideleClassCongr eK' c))) :=
      congrArg (relativeNorm rationalIdeleClassRepresentation H H' hH'H)
        hupper.symm
    _ = rationalAbstractFixedFieldIdeleClassEquivFixed H
        (Additive.ofMul
          (_root_.ideleClassNorm F E (ideleClassCongr eK' c))) := hrelative
    _ = numberFieldEmbeddedIdeleClassEquivAmbientFixed
        K L jLower (Additive.ofMul (_root_.ideleClassNorm K K' c)) := by
      change
        rationalAbstractFixedFieldIdeleClassEquivFixed H
            (Additive.ofMul
              (_root_.ideleClassNorm F E (ideleClassCongr eK' c))) =
          rationalAbstractFixedFieldIdeleClassEquivFixed H
            (Additive.ofMul
              (ideleClassCongr eK (_root_.ideleClassNorm K K' c)))
      apply congrArg (rationalAbstractFixedFieldIdeleClassEquivFixed H)
      apply congrArg Additive.ofMul
      exact
        (ideleClassCongr_ideleClassNorm
          (K := K) (K' := F) (L := K') (L' := E) eK eK' hcompat c).symm

/-- For one common compatible embedding of a Galois base-change
diamond, the genuine global norm-residue maps commute with ordinary
idele-class norm and actual restriction of automorphisms. -/
theorem globalNormResidueMonoidHomOfEmbedding_norm_restriction
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (globalNormResidueMonoidHomOfEmbedding K' L' j) =
      (globalNormResidueMonoidHomOfEmbedding K L jLower).comp
        (_root_.ideleClassNorm K K') := by
  dsimp only
  let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
    j.comp (IsScalarTower.toAlgHom ℚ L L')
  let H :=
    numberFieldEmbeddedBaseSubgroup K L jLower
  let H' :=
    numberFieldEmbeddedBaseSubgroup K' L' j
  let J :=
    numberFieldEmbeddedTopSubgroup K L jLower
  let J' :=
    numberFieldEmbeddedTopSubgroup K' L' j
  let hJH :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L jLower
  let hJ'H' :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup K' L' j
  let hH'H :=
    numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
  let hJ'J :=
    numberFieldEmbeddedTopSubgroup_le_of_tower K K' L L' j
  let _ :
      (CyclicCohomology.extensionSubgroup H J hJH).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K L jLower
  let _ :
      Finite
        (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H J hJH) :=
    numberFieldEmbeddedExtensionQuotient_finite K L jLower
  let _ :
      (CyclicCohomology.extensionSubgroup H' J' hJ'H').Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K' L' j
  let _ :
      Finite
        (H'.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H' J' hJ'H') :=
    numberFieldEmbeddedExtensionQuotient_finite K' L' j
  let hHH'finite :=
    numberFieldEmbeddedBaseChangeExtensionQuotientFinite K K' L L' j
  let T :
      FiniteAbstractFieldExtension
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    { field := numberFieldEmbeddedFiniteAbstractField K' L' j
      base := numberFieldEmbeddedFiniteAbstractField K L jLower
      below := hH'H
      finiteQuotient := hHH'finite }
  let hTBaseNormal :
      (CyclicCohomology.extensionSubgroup
        T.base.field J hJH).Normal := by
    change
      (CyclicCohomology.extensionSubgroup H J hJH).Normal
    exact numberFieldEmbeddedExtensionSubgroup_normal K L jLower
  let hTBaseFinite :
      Finite
        (T.base.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            T.base.field J hJH) := by
    change
      Finite
        (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H J hJH)
    exact numberFieldEmbeddedExtensionQuotient_finite K L jLower
  let hTFieldNormal :
      (CyclicCohomology.extensionSubgroup
        T.field.field J' hJ'H').Normal := by
    change
      (CyclicCohomology.extensionSubgroup H' J' hJ'H').Normal
    exact numberFieldEmbeddedExtensionSubgroup_normal K' L' j
  let hTFieldFinite :
      Finite
        (T.field.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            T.field.field J' hJ'H') := by
    change
      Finite
        (H'.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H' J' hJ'H')
    exact numberFieldEmbeddedExtensionQuotient_finite K' L' j
  let restrictActual :
      Gal(L' / K') →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  apply MonoidHom.ext
  intro c
  let a :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed
      K' L' j (Additive.ofMul c)
  have hnat :=
    DegreeData.normResidueNaturality_norm_restriction
      (D := rationalCyclotomicDegreeData)
      (A := rationalIdeleClassRepresentation)
      (v := rationalCyclotomicIdeleClassValuationData)
      (hcf := rationalIdeleClassRepresentation_satisfiesClassFieldAxiom)
      (T := T) (L := J) (L' := J')
      (hLnormal := hTBaseNormal)
      (hL'normal := hTFieldNormal)
      (hLKfinite := hTBaseFinite)
      (hL'K'finite := hTFieldFinite)
      hJH hJ'H' hJ'J
  have hnatc :=
    DFunLike.congr_fun hnat
      (finiteNormClass rationalIdeleClassRepresentation
        H' J' hJ'H' a)
  change _ =
    rationalCyclotomicDegreeData.normResidueSymbol
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      T.base
      { field := J
        below := hJH
        normal := hTBaseNormal
        finite := hTBaseFinite }
      (finiteReciprocityNaturalityNormMap
        rationalIdeleClassRepresentation
        T.base.field T.field.field J J'
        hJH hJ'H' T.below hJ'J
        (finiteNormClass rationalIdeleClassRepresentation
          T.field.field J' hJ'H' a)) at hnatc
  rw [finiteReciprocityNaturalityNormMap_finiteNormClass]
    at hnatc
  have hnorm :
      relativeNorm rationalIdeleClassRepresentation
          H H' hH'H a =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed
          K L jLower
          (Additive.ofMul (_root_.ideleClassNorm K K' c)) :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed_relativeNorm
      K K' L L' j c
  calc
    restrictActual
        (globalNormResidueMonoidHomOfEmbedding K' L' j c) =
      restrictActual
        (Additive.toMul
          (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
            K' L' j
            (rationalCyclotomicDegreeData.normResidueSymbol
              rationalIdeleClassRepresentation
              rationalCyclotomicIdeleClassValuationData
              rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
              (numberFieldEmbeddedFiniteAbstractField K' L' j)
              (numberFieldEmbeddedFiniteGaloisSubextension K' L' j)
              (finiteNormClass rationalIdeleClassRepresentation
                H' J' hJ'H' a)))) := by
      rw [globalNormResidueMonoidHomOfEmbedding_apply]
    _ =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L jLower
          (MonoidHom.toAdditive
            (normResidueNaturalityAbelianizedRestriction
              H H' J J' hJH hJ'H' hH'H hJ'J)
            (rationalCyclotomicDegreeData.normResidueSymbol
              rationalIdeleClassRepresentation
              rationalCyclotomicIdeleClassValuationData
              rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
              (numberFieldEmbeddedFiniteAbstractField K' L' j)
              (numberFieldEmbeddedFiniteGaloisSubextension K' L' j)
              (finiteNormClass rationalIdeleClassRepresentation
                H' J' hJ'H' a)))) := by
      exact
        numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup_restriction
          K K' L L' j _
    _ =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L jLower
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            (numberFieldEmbeddedFiniteAbstractField K L jLower)
            (numberFieldEmbeddedFiniteGaloisSubextension K L jLower)
            (finiteNormClass rationalIdeleClassRepresentation
              H J hJH
              (relativeNorm rationalIdeleClassRepresentation
                H H' hH'H a)))) := by
      exact congrArg
        (fun z =>
          Additive.toMul
            (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
              K L jLower z))
        hnatc
    _ =
      globalNormResidueMonoidHomOfEmbedding K L jLower
        (_root_.ideleClassNorm K K' c) := by
      rw [hnorm,
        ← globalNormResidueMonoidHomOfEmbedding_apply]

end EmbeddedNumberFieldRestriction

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceCompatibility
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
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
    infinitePlaceCompatibilityIdeleClassGroupIsMulCommutative_r7c11b6_1
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
/-- The real infinite place of the conjugation fixed field obtained
by restricting the concrete complex place of the overfield. -/
noncomputable def ramifiedInfinitePlaceRealFixedPlace
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    InfinitePlace
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  (infinitePlaceComplexificationOverfieldComplexPlace
      (K := K) (L := L) v).comap
    (algebraMap
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v))

/-- Restriction from the complex-conjugation overextension back to
the original finite abelian extension. -/
noncomputable def ramifiedInfinitePlaceOverextensionRestriction
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal(
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) /
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)) →*
      Gal(L / K) :=
  (AlgEquiv.restrictNormalHom L).comp
    (AlgEquiv.restrictScalarsHom K)

/-- A rational-separable-closure embedding of the complexification
overfield extending the standard embedding of its original top field. -/
noncomputable def
    infinitePlaceComplexificationOverfieldSeparableClosureEmbedding
    (v : InfinitePlace K) :
    infinitePlaceComplexificationOverfield
        (K := K) (L := L) v →ₐ[ℚ]
      SeparableClosure ℚ :=
  Classical.choose
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ)
      (L := L)
      (E :=
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
      (M := SeparableClosure ℚ)
      (AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L))

/-- The embedding of `L` induced by the chosen embedding of its
complexification overfield. -/
noncomputable def
    infinitePlaceComplexificationLowerSeparableClosureEmbedding
    (v : InfinitePlace K) :
    L →ₐ[ℚ] SeparableClosure ℚ :=
  (infinitePlaceComplexificationOverfieldSeparableClosureEmbedding
      (K := K) (L := L) v).comp
    (IsScalarTower.toAlgHom ℚ L
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v))

/-- The upper negative-one idele class used in the overextension diamond. -/
noncomputable def ramifiedInfinitePlaceOverextensionNegOneIdeleClass
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IdeleClassGroup
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  IdeleGroup.infinitePlaceIdeleClass
    (ramifiedInfinitePlaceRealFixedPlace
      (K := K) (L := L) v hRamified)
    (-1 :
      (ramifiedInfinitePlaceRealFixedPlace
        (K := K) (L := L) v hRamified).Completionˣ)

/-- The upper global norm-residue value in the overextension diamond. -/
noncomputable def
    ramifiedInfinitePlaceOverextensionGlobalNormResidueNegOneValue
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal(
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) /
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)) :=
  globalNormResidueMonoidHomOfEmbedding
    (ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified)
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)
    (infinitePlaceComplexificationOverfieldSeparableClosureEmbedding
      (K := K) (L := L) v)
    (ramifiedInfinitePlaceOverextensionNegOneIdeleClass
      (K := K) (L := L) v hRamified)

/-- The upper norm-residue value after actual Galois restriction. -/
noncomputable def
    ramifiedInfinitePlaceRestrictedOverextensionNormResidueNegOneValue
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal(L / K) :=
  ramifiedInfinitePlaceOverextensionRestriction
    (K := K) (L := L) v hRamified
    (ramifiedInfinitePlaceOverextensionGlobalNormResidueNegOneValue
      (K := K) (L := L) v hRamified)

/-- The lower norm-residue value of the normed upper negative-one class. -/
noncomputable def
    ramifiedInfinitePlaceNormedOverextensionNormResidueNegOneValue
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal(L / K) :=
  globalNormResidueMonoidHomOfEmbedding K L
    (infinitePlaceComplexificationLowerSeparableClosureEmbedding
      (K := K) (L := L) v)
    (_root_.ideleClassNorm K
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (ramifiedInfinitePlaceOverextensionNegOneIdeleClass
        (K := K) (L := L) v hRamified))

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end


