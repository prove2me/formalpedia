-- Prove2me | Definitions.Def_OAIQ244Duke065
-- name    : OAIQ244Duke065
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:28:36.938437+00:00
-- url     : https://prove2.me/theorems/71f35af0-43de-415b-8677-7ab32e16a551
-- title:
--   Definitions bundle OAIQ244Duke065 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 6 definitions and 25 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom`, `IdeleGroup.ideleNormContinuousMonoidHom`, `IdeleGroup.integralFiniteNormComponents`, `IdeleGroup.integralIdeleEmbedding`, `IdeleGroup.integralInfiniteNormComponents`, `LocalClassFieldTheory.finiteResidueAbstractBase`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_Extension_IdeleNormComponents`, `AlgebraicNumberTheory_Idele_NormTopology_Continuity`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin`, `KummerTheory_Concrete_SimpleExtensionLocalBehavior`, `LocalClassFieldTheory_Finite_LocalReciprocity_SeparableFixedFieldNorm`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison`, `LocalField_DiscreteValuationField_PadicValuationComparison`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke053`, `OAIQ244Duke054`, `OAIQ244Duke055`, `OAIQ244Duke056`, `OAIQ244Duke059` and `OAIQ244Duke060` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke070`, `OAIQ244Duke072`, `OAIQ244Duke073` and `OAIQ244Duke113`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
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
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
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
import Definitions.Def_OAIQ244Duke053
import Definitions.Def_OAIQ244Duke054
import Definitions.Def_OAIQ244Duke055
import Definitions.Def_OAIQ244Duke056
import Definitions.Def_OAIQ244Duke059
import Definitions.Def_OAIQ244Duke060

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_SeparableFixedFieldNorm
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory KummerTheory

open LocalFieldTheory

open ClassFormation CyclicCohomology

/-!
# Finite local reciprocity: norms from arbitrary finite separable fixed fields

The henselian condition in the abstract class-formation framework quantifies over every finite abstract
field, not only over normal ones.  For an intermediate finite separable field
`E` in a separably closed Galois ambient field, the left cosets of
`Gal(Ω / E)` are canonically the `K`-embeddings `E → Ω`.  This file uses that
identification to compare the abstract class-formation coset norm with the ordinary field
norm, without a normality assumption on `E / K`.
-/

noncomputable section

open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

section NormAsProduct

variable (E : IntermediateField K Ω)
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

/-- Equivariant form of the nonnormal finite-separable norm comparison. -/
theorem relativeNorm_intermediateFieldUnit_of_isSeparable (x : Eˣ) :
    relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup K Ω E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) =
      baseUnitsEquivGaloisAmbientFixed K Ω
        (Additive.ofMul (normUnits K E x)) := by
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  exact relativeNorm_intermediateFieldUnit_val_of_isSeparable K Ω E x

end NormAsProduct

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_IdeleNormComponents
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.chosenFinitePlaceIntegerToLocalizedCompletion_coe _root_.chosenFinitePlaceLocalizedResidueEquiv_apply_mk _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_mk _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.mem_finitePlaceDecompositionGroup_iff _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local components of the ordinary idele norm

The ordinary idele norm is transported from the determinant norm on the
relative idele group. At each place, the canonical local tensor decomposition identifies that
determinant with the product of the ordinary field norms on the completion
factors above the place.  These are the concrete finite- and infinite-place
forms of the local idele norm formula.
-/

open scoped BigOperators NumberField TensorProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

open AlgebraicNumberTheory.Valuations

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The relative-tensor coordinate form underlying the public finite-place
formula below. -/
theorem finiteComponent_norm_eq_prod_extensions
    (v : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let z :=
      (relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)).symm a
    let x :=
      RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) v z
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w =>
        AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w =>
        completionModuleFinite vK hvK w
    Units.mapEquiv
        (_root_.relativeFinitePlaceCompletionAlgEquiv
          (K := K) v).symm.toMulEquiv
        (finiteComponent v (norm K L a)) =
      ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (_root_.finitePlaceLocalTensorDecompositionUnitsComponent
            (K := K) (L := L) v w x) := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let e :=
    relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)
  let z := e.symm a
  let x :=
    RelativeIdeleGroup.finiteComponent
      (K := K) (L := L) v z
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w =>
      AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w =>
      completionModuleFinite vK hvK w
  have hz : e z = a :=
    e.apply_symm_apply a
  change
    Units.mapEquiv
        (_root_.relativeFinitePlaceCompletionAlgEquiv
          (K := K) v).symm.toMulEquiv
        (finiteComponent v (norm K L a)) =
      ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (_root_.finitePlaceLocalTensorDecompositionUnitsComponent
            (K := K) (L := L) v w x)
  rw [← hz, norm_relativeIdeleBaseChangeMulEquiv,
    RelativeIdeleGroup.finiteComponent_norm]
  apply Units.ext
  change
    (_root_.relativeFinitePlaceCompletionAlgEquiv
        (K := K) v).symm
        (Algebra.norm (v.adicCompletion K)
          (x : v.adicCompletion K ⊗[K] L)) =
      (((∏ w : AbsoluteValueExtension vK L,
          Units.map (Algebra.norm vK.Completion)
            (_root_.finitePlaceLocalTensorDecompositionUnitsComponent
              (K := K) (L := L) v w x)) :
          vK.Completionˣ) : vK.Completion)
  let x' : (vK.Completion ⊗[K] L)ˣ :=
    Units.mapEquiv
      (_root_.relativeFinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) v).symm.toMulEquiv x
  calc
    (_root_.relativeFinitePlaceCompletionAlgEquiv
        (K := K) v).symm
        (Algebra.norm (v.adicCompletion K)
          (x : v.adicCompletion K ⊗[K] L)) =
        Algebra.norm vK.Completion
          (x' : vK.Completion ⊗[K] L) := by
      exact
        map_norm_tensorProduct_baseChange
          (K := K) (L := L)
          (_root_.relativeFinitePlaceCompletionAlgEquiv
            (K := K) v).symm.toAlgHom
          (x : v.adicCompletion K ⊗[K] L)
    _ = ∏ w : AbsoluteValueExtension vK L,
        Algebra.norm vK.Completion
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK
            (x' : vK.Completion ⊗[K] L) w) := by
      exact
        RelativeIdeleGroup.localNorm_units_eq_prod
          vK hvK x'
    _ =
        (((∏ w : AbsoluteValueExtension vK L,
            Units.map (Algebra.norm vK.Completion)
              (_root_.finitePlaceLocalTensorDecompositionUnitsComponent
                (K := K) (L := L) v w x)) :
            vK.Completionˣ) : vK.Completion) := by
      change _ = Units.coeHom vK.Completion _
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro w _
      rfl

/-- The finite-place form of the ordinary idele norm. Each factor
is the mathlib field norm of the actual idele component at the concrete
finite place corresponding to an exact extension of `v`; the existing
completion equivalence is used only to put that component in the canonical
absolute-value completion. -/
theorem finiteComponent_norm_eq_prod_completion
    (v : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w =>
        AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w =>
        completionModuleFinite vK hvK w
    Units.mapEquiv
        (_root_.relativeFinitePlaceCompletionAlgEquiv
          (K := K) v).symm.toMulEquiv
        (finiteComponent v (norm K L a)) =
      ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (Units.mapEquiv
            (finitePlaceExtensionAdicCompletionRingEquiv
              (K := K) (L := L) v w).symm.toMulEquiv
            (finiteComponent
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) v w).1 a)) := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let e :=
    relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)
  let z := e.symm a
  let x :=
    RelativeIdeleGroup.finiteComponent
      (K := K) (L := L) v z
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w =>
      AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w =>
      completionModuleFinite vK hvK w
  have hz : e z = a :=
    e.apply_symm_apply a
  change
    Units.mapEquiv
        (_root_.relativeFinitePlaceCompletionAlgEquiv
          (K := K) v).symm.toMulEquiv
        (finiteComponent v (norm K L a)) =
      ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (Units.mapEquiv
            (finitePlaceExtensionAdicCompletionRingEquiv
              (K := K) (L := L) v w).symm.toMulEquiv
            (finiteComponent
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) v w).1 a))
  calc
    Units.mapEquiv
        (_root_.relativeFinitePlaceCompletionAlgEquiv
          (K := K) v).symm.toMulEquiv
        (finiteComponent v (norm K L a)) =
        ∏ w : AbsoluteValueExtension vK L,
          Units.map (Algebra.norm vK.Completion)
            (_root_.finitePlaceLocalTensorDecompositionUnitsComponent
              (K := K) (L := L) v w x) :=
      finiteComponent_norm_eq_prod_extensions
        (K := K) (L := L) v a
    _ = ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (Units.mapEquiv
            (finitePlaceExtensionAdicCompletionRingEquiv
              (K := K) (L := L) v w).symm.toMulEquiv
            (finiteComponent
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) v w).1 a)) := by
      apply Finset.prod_congr rfl
      intro w _
      apply congrArg (Units.map (Algebra.norm vK.Completion))
      let W :=
        finitePlaceExtensionEquivAbove
          (K := K) (L := L) v w
      have hcomponent :=
        congrArg (fun b : IdeleGroup L => finiteComponent W.1 b) hz
      change
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z).2 W.1 =
          finiteComponent W.1 a at hcomponent
      rw [relativeIdeleBaseChangeMulEquiv_finite,
        _root_.relativeFiniteIdeleToFiniteIdele_apply,
        _root_.relativeFiniteTensorPiMulEquiv_apply] at hcomponent
      change
        _root_.finitePlaceTensorUnitsEquivAboveAdic
            (K := K) (L := L)
            (_root_.finitePlaceBelow (K := K) W.1)
            (RelativeIdeleGroup.finiteComponent
              (K := K) (L := L)
              (_root_.finitePlaceBelow (K := K) W.1) z)
            ⟨W.1, rfl⟩ =
          finiteComponent W.1 a at hcomponent
      have hcomponent' :
          _root_.finitePlaceTensorUnitsEquivAboveAdic
              (K := K) (L := L) v x W =
            finiteComponent W.1 a := by
        let W₀ : HeightOneSpectrum (𝓞 L) := W.1
        let P : HeightOneSpectrum (𝓞 K) → Prop := fun q =>
          ∀ hq : _root_.finitePlaceBelow (K := K) W₀ = q,
            _root_.finitePlaceTensorUnitsEquivAboveAdic
                (K := K) (L := L) q
                (RelativeIdeleGroup.finiteComponent
                  (K := K) (L := L) q z)
                ⟨W₀, hq⟩ =
              finiteComponent W₀ a
        have hP :
            P (_root_.finitePlaceBelow (K := K) W₀) := by
          intro hq
          simpa only [P, W₀] using hcomponent
        have hW :
            _root_.finitePlaceBelow (K := K) W₀ = v :=
          W.2
        have hPv : P v :=
          hW ▸ hP
        simpa only [P, W₀, x] using hPv W.2
      dsimp only [W] at hcomponent'
      rw [
        _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension
      ] at hcomponent'
      apply
        (Units.mapEquiv
          (finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w).toMulEquiv).injective
      rw [hcomponent']
      exact
        ((Units.mapEquiv
          (finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w).toMulEquiv).apply_symm_apply
          (finiteComponent
            (finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1 a)).symm

/-- The finite-place form of the ordinary idele norm, entirely in
the concrete adic completions.  Thus the component at `v` is the product
of the ordinary field norms of the components at all finite places above
`v`. -/
theorem finiteComponent_norm_eq_prod_exact_index
    (v : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra (v.adicCompletion K)
          ((finitePlaceExtensionEquivAbove
            (K := K) (L := L) v w).1.adicCompletion L) :=
      fun w =>
        (finitePlaceAdicCompletionMap K L v
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) v w)).toAlgebra
    finiteComponent v (norm K L a) =
      ∏ w : AbsoluteValueExtension vK L,
        LocalFieldTheory.normUnits
          (v.adicCompletion K)
          ((finitePlaceExtensionEquivAbove
            (K := K) (L := L) v w).1.adicCompletion L)
          (finiteComponent
            (finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1 a) := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let eBase :=
    _root_.relativeFinitePlaceCompletionAlgEquiv
      (K := K) v
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w =>
      AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w =>
      completionModuleFinite vK hvK w
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra (v.adicCompletion K)
        ((finitePlaceExtensionEquivAbove
          (K := K) (L := L) v w).1.adicCompletion L) :=
    fun w =>
      (finitePlaceAdicCompletionMap K L v
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) v w)).toAlgebra
  have hCompatible
      (w : AbsoluteValueExtension vK L) :
      RingHom.comp
          (algebraMap
            (v.adicCompletion K)
            ((finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1.adicCompletion L))
          eBase.toRingEquiv =
        RingHom.comp
          (finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w).toRingHom
          (algebraMap vK.Completion w.1.Completion) := by
    apply RingHom.ext
    intro x
    change
      finitePlaceAdicCompletionMap K L v
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) v w)
          (eBase x) =
        finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) v w
          (algebraMap vK.Completion w.1.Completion x)
    rw [←
      finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
        K L v w]
    simp [finitePlaceExtensionAdicCompletionMap, eBase, vK]
  have hcompletion :=
    finiteComponent_norm_eq_prod_completion
      (K := K) (L := L) v a
  change
    finiteComponent v (norm K L a) =
      ∏ w : AbsoluteValueExtension vK L,
        LocalFieldTheory.normUnits
          (v.adicCompletion K)
          ((finitePlaceExtensionEquivAbove
            (K := K) (L := L) v w).1.adicCompletion L)
          (finiteComponent
            (finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1 a)
  calc
    finiteComponent v (norm K L a) =
        Units.mapEquiv eBase.toMulEquiv
          (Units.mapEquiv eBase.symm.toMulEquiv
            (finiteComponent v (norm K L a))) := by
      apply Units.ext
      simp
    _ = Units.mapEquiv eBase.toMulEquiv
        (∏ w : AbsoluteValueExtension vK L,
          Units.map (Algebra.norm vK.Completion)
            (Units.mapEquiv
              (finitePlaceExtensionAdicCompletionRingEquiv
                (K := K) (L := L) v w).symm.toMulEquiv
              (finiteComponent
                (finitePlaceExtensionEquivAbove
                  (K := K) (L := L) v w).1 a))) := by
      exact congrArg (Units.mapEquiv eBase.toMulEquiv) hcompletion
    _ = ∏ w : AbsoluteValueExtension vK L,
        Units.mapEquiv eBase.toMulEquiv
          (Units.map (Algebra.norm vK.Completion)
            (Units.mapEquiv
              (finitePlaceExtensionAdicCompletionRingEquiv
                (K := K) (L := L) v w).symm.toMulEquiv
              (finiteComponent
                (finitePlaceExtensionEquivAbove
                  (K := K) (L := L) v w).1 a))) := by
      rw [map_prod]
    _ = ∏ w : AbsoluteValueExtension vK L,
        LocalFieldTheory.normUnits
          (v.adicCompletion K)
          ((finitePlaceExtensionEquivAbove
            (K := K) (L := L) v w).1.adicCompletion L)
          (finiteComponent
            (finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1 a) := by
      apply Finset.prod_congr rfl
      intro w _
      let W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v} :=
        ⟨finitePlaceExtensionCentre (K := K) (L := L) v w,
          finitePlaceBelow_finitePlaceExtensionCentre
            (K := K) (L := L) v w⟩
      let : Algebra (v.adicCompletion K)
          ((finitePlaceExtensionCentre
            (K := K) (L := L) v w).adicCompletion L) :=
        (finitePlaceAdicCompletionMap K L v W).toAlgebra
      let eExtension :=
        finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) v w
      let x : w.1.Completionˣ :=
        Units.mapEquiv eExtension.symm.toMulEquiv
          (finiteComponent
            (finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1 a)
      have hNorm :=
        LocalClassFieldTheory.normUnits_map_ringEquiv
          eBase.toRingEquiv eExtension (hCompatible w) x
      have hx :
          Units.mapEquiv eExtension.toMulEquiv x =
            finiteComponent
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) v w).1 a := by
        exact
          (Units.mapEquiv eExtension.toMulEquiv).apply_symm_apply
            (finiteComponent
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) v w).1 a)
      rw [hx] at hNorm
      change
        Units.mapEquiv eBase.toMulEquiv
            (LocalFieldTheory.normUnits
              vK.Completion w.1.Completion x) =
          LocalFieldTheory.normUnits
            (v.adicCompletion K)
            ((finitePlaceExtensionEquivAbove
              (K := K) (L := L) v w).1.adicCompletion L)
            (finiteComponent
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) v w).1 a)
      exact hNorm

/-- The finite-place form of the ordinary idele norm. The
component at `v` is the product of the ordinary field norms of the actual
idele components at the finite places above `v`. -/
theorem finiteComponent_norm_eq_prod
    (v : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    let eAbove :=
      finitePlaceExtensionEquivAbove
        (K := K) (L := L) v
    letI : Fintype {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v} :=
      Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
    letI : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v},
        Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
      fun W =>
        (finitePlaceAdicCompletionMap
          K L v W).toAlgebra
    finiteComponent v (norm K L a) =
      ∏ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v},
        LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.1.adicCompletion L)
          (finiteComponent W.1 a) := by
  classical
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let eAbove :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
  let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v},
      Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    fun W =>
      (finitePlaceAdicCompletionMap
        K L v W).toAlgebra
  have hexact :=
    finiteComponent_norm_eq_prod_exact_index
      (K := K) (L := L) v a
  change
    finiteComponent v (norm K L a) =
      ∏ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v},
        LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.1.adicCompletion L)
          (finiteComponent W.1 a)
  calc
    finiteComponent v (norm K L a) =
        ∏ w : AbsoluteValueExtension vK L,
          LocalFieldTheory.normUnits
            (v.adicCompletion K)
            ((eAbove w).1.adicCompletion L)
            (finiteComponent (eAbove w).1 a) :=
      by
        simpa only [eAbove, finitePlaceExtensionEquivAbove_coe] using
          hexact
    _ = ∏ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v},
        LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.1.adicCompletion L)
          (finiteComponent W.1 a) := by
      exact
        Fintype.prod_equiv eAbove
          (fun w : AbsoluteValueExtension vK L =>
            LocalFieldTheory.normUnits
              (v.adicCompletion K)
              ((eAbove w).1.adicCompletion L)
              (finiteComponent (eAbove w).1 a))
          (fun W : {W : HeightOneSpectrum (𝓞 L) //
              _root_.finitePlaceBelow (K := K) W = v} =>
            LocalFieldTheory.normUnits
              (v.adicCompletion K) (W.1.adicCompletion L)
              (finiteComponent W.1 a))
          (fun _ => rfl)

/-- The absolute-value-extension-coordinate form underlying the public
archimedean formula below. -/
theorem infiniteComponent_norm_eq_prod_extensions
    (v : InfinitePlace K)
    (a : IdeleGroup L) :
    let vK := v.1
    let hvK : vK.IsNontrivial := v.isNontrivial
    let z :=
      (relativeIdeleBaseChangeMulEquiv
        (K := K) (L := L)).symm a
    let x :=
      RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) v z
    let x' :=
      _root_.infinitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) v x
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w =>
        AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w =>
        completionModuleFinite vK hvK w
    Units.mapEquiv
        (_root_.infinitePlaceCompletionAlgEquiv
          (K := K) v).toMulEquiv
        (infiniteComponent v (norm K L a)) =
      ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
            vK hvK x' w) := by
  classical
  let vK := v.1
  let hvK : vK.IsNontrivial := v.isNontrivial
  let e :=
    relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)
  let z := e.symm a
  let x :=
    RelativeIdeleGroup.infiniteComponent
      (K := K) (L := L) v z
  let x' :=
    _root_.infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v x
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w =>
      AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w =>
      completionModuleFinite vK hvK w
  have hz : e z = a :=
    e.apply_symm_apply a
  change
    Units.mapEquiv
        (_root_.infinitePlaceCompletionAlgEquiv
          (K := K) v).toMulEquiv
        (infiniteComponent v (norm K L a)) =
      ∏ w : AbsoluteValueExtension vK L,
        Units.map (Algebra.norm vK.Completion)
          (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
            vK hvK x' w)
  rw [← hz, norm_relativeIdeleBaseChangeMulEquiv,
    RelativeIdeleGroup.infiniteComponent_norm]
  apply Units.ext
  change
    _root_.infinitePlaceCompletionAlgEquiv
        (K := K) v
        (Algebra.norm v.Completion
          (x : v.Completion ⊗[K] L)) =
      (((∏ w : AbsoluteValueExtension vK L,
          Units.map (Algebra.norm vK.Completion)
            (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
              vK hvK x' w)) :
          vK.Completionˣ) : vK.Completion)
  calc
    _root_.infinitePlaceCompletionAlgEquiv
        (K := K) v
        (Algebra.norm v.Completion
          (x : v.Completion ⊗[K] L)) =
        Algebra.norm vK.Completion
          (x' : vK.Completion ⊗[K] L) := by
      exact
        map_norm_tensorProduct_baseChange
          (K := K) (L := L)
          (_root_.infinitePlaceCompletionAlgEquiv
            (K := K) v).toAlgHom
          (x : v.Completion ⊗[K] L)
    _ = ∏ w : AbsoluteValueExtension vK L,
        Algebra.norm vK.Completion
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK
            (x' : vK.Completion ⊗[K] L) w) := by
      exact
        RelativeIdeleGroup.localNorm_units_eq_prod
          vK hvK x'
    _ =
        (((∏ w : AbsoluteValueExtension vK L,
            Units.map (Algebra.norm vK.Completion)
              (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
                vK hvK x' w)) :
            vK.Completionˣ) : vK.Completion) := by
      change _ = Units.coeHom vK.Completion _
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro w _
      rfl

/-- The completion-coordinate form underlying the public archimedean
formula below, already reindexed by concrete infinite places. -/
theorem infiniteComponent_norm_eq_prod_completion
    (v : InfinitePlace K)
    (a : IdeleGroup L) :
    let vK := v.1
    let hvK : vK.IsNontrivial := v.isNontrivial
    let eAbove :=
      _root_.infinitePlaceAboveEquivExtension
        (K := K) (L := L) v
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w =>
        AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w =>
        completionModuleFinite vK hvK w
    letI : Fintype {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v} :=
      Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove.symm
    letI : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v},
        W.1.1.LiesOver vK :=
      fun W =>
        ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    letI : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v},
        Algebra vK.Completion W.1.1.Completion :=
      fun W =>
        AbsoluteValue.completionAlgebra vK W.1.1
          (eAbove W).2
    letI : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v},
        Module.Finite vK.Completion W.1.1.Completion :=
      fun W =>
        completionModuleFinite vK hvK (eAbove W)
    Units.mapEquiv
        (_root_.infinitePlaceCompletionAlgEquiv
          (K := K) v).toMulEquiv
        (infiniteComponent v (norm K L a)) =
      ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        Units.map (Algebra.norm vK.Completion)
          (Units.mapEquiv
            (InfinitePlace.Completion.equiv W.1).toMulEquiv
            (infiniteComponent W.1 a)) := by
  classical
  let vK := v.1
  let hvK : vK.IsNontrivial := v.isNontrivial
  let e :=
    relativeIdeleBaseChangeMulEquiv
      (K := K) (L := L)
  let z := e.symm a
  let x :=
    RelativeIdeleGroup.infiniteComponent
      (K := K) (L := L) v z
  let x' :=
    _root_.infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) v x
  let eAbove :=
    _root_.infinitePlaceAboveEquivExtension
      (K := K) (L := L) v
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w =>
      AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w =>
      completionModuleFinite vK hvK w
  let : Fintype {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove.symm
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v},
      W.1.1.LiesOver vK :=
    fun W =>
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v},
      Algebra vK.Completion W.1.1.Completion :=
    fun W =>
      AbsoluteValue.completionAlgebra vK W.1.1
        (eAbove W).2
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v},
      Module.Finite vK.Completion W.1.1.Completion :=
    fun W =>
      completionModuleFinite vK hvK (eAbove W)
  have hz : e z = a :=
    e.apply_symm_apply a
  change
    Units.mapEquiv
        (_root_.infinitePlaceCompletionAlgEquiv
          (K := K) v).toMulEquiv
        (infiniteComponent v (norm K L a)) =
      ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        Units.map (Algebra.norm vK.Completion)
          (Units.mapEquiv
            (InfinitePlace.Completion.equiv W.1).toMulEquiv
            (infiniteComponent W.1 a))
  calc
    Units.mapEquiv
        (_root_.infinitePlaceCompletionAlgEquiv
          (K := K) v).toMulEquiv
        (infiniteComponent v (norm K L a)) =
        ∏ w : AbsoluteValueExtension vK L,
          Units.map (Algebra.norm vK.Completion)
            (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
              vK hvK x' w) :=
      infiniteComponent_norm_eq_prod_extensions
        (K := K) (L := L) v a
    _ = ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        Units.map (Algebra.norm vK.Completion)
          (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
            vK hvK x' (eAbove W)) := by
      exact
        (eAbove.prod_comp
          (fun w : AbsoluteValueExtension vK L =>
            Units.map (Algebra.norm vK.Completion)
              (AlgebraicNumberTheory.Valuations.localTensorUnitsEquivCompletionProduct
                vK hvK x' w))).symm
    _ = ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        Units.map (Algebra.norm vK.Completion)
          (Units.mapEquiv
            (InfinitePlace.Completion.equiv W.1).toMulEquiv
            (infiniteComponent W.1 a)) := by
      apply Finset.prod_congr rfl
      intro W _
      apply congrArg (Units.map (Algebra.norm vK.Completion))
      have hcomponent :=
        congrArg (fun b : IdeleGroup L => infiniteComponent W.1 b) hz
      change
        _root_.infinitePlaceTensorUnitsEquivAbove
            (K := K) (L := L)
            (_root_.infinitePlaceBelow (K := K) W.1)
            ((_root_.relativeIdeleToLocalData
              (K := K) (L := L) z).infinite
              (_root_.infinitePlaceBelow (K := K) W.1))
            ⟨W.1, rfl⟩ =
          infiniteComponent W.1 a at hcomponent
      simp only [_root_.relativeIdeleToLocalData] at hcomponent
      have hcomponentFixed :
          _root_.infinitePlaceTensorUnitsEquivAbove
              (K := K) (L := L) v x W =
            infiniteComponent W.1 a := by
        let W₀ : InfinitePlace L := W.1
        let P : InfinitePlace K → Prop := fun q =>
          ∀ hq : _root_.infinitePlaceBelow (K := K) W₀ = q,
            _root_.infinitePlaceTensorUnitsEquivAbove
                (K := K) (L := L) q
                (RelativeIdeleGroup.infiniteComponent
                  (K := K) (L := L) q z)
                ⟨W₀, hq⟩ =
              infiniteComponent W₀ a
        have hP :
            P (_root_.infinitePlaceBelow (K := K) W₀) := by
          intro hq
          simpa only [P, W₀] using hcomponent
        have hW :
            _root_.infinitePlaceBelow (K := K) W₀ = v :=
          W.2
        have hPv : P v :=
          hW ▸ hP
        simpa only [P, W₀, x] using hPv W.2
      rw [_root_.infinitePlaceTensorUnitsEquivAbove_apply]
        at hcomponentFixed
      apply
        (Units.mapEquiv
          (InfinitePlace.Completion.equiv W.1).symm.toMulEquiv).injective
      rw [hcomponentFixed]
      apply Units.ext
      exact
        ((InfinitePlace.Completion.equiv W.1).symm_apply_apply _).symm

/-- The archimedean form of the ordinary idele norm. The component
at `v` is the product of the ordinary field norms of the actual idele
components at the infinite places above `v`. -/
theorem infiniteComponent_norm_eq_prod
    (v : InfinitePlace K)
    (a : IdeleGroup L) :
    let vK := v.1
    let hvK : vK.IsNontrivial := v.isNontrivial
    let eAbove :=
      _root_.infinitePlaceAboveEquivExtension
        (K := K) (L := L) v
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : Fintype {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v} :=
      Fintype.ofEquiv
        (AbsoluteValueExtension vK L) eAbove.symm
    letI : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v},
        W.1.1.LiesOver v.1 :=
      fun W =>
        ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    infiniteComponent v (norm K L a) =
      ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        LocalFieldTheory.normUnits
          v.Completion W.1.Completion
          (infiniteComponent W.1 a) := by
  classical
  let vK := v.1
  let hvK : vK.IsNontrivial := v.isNontrivial
  let eBase :=
    _root_.infinitePlaceCompletionAlgEquiv
      (K := K) v
  let eAbove :=
    _root_.infinitePlaceAboveEquivExtension
      (K := K) (L := L) v
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : Fintype {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove.symm
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w =>
      AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w =>
      completionModuleFinite vK hvK w
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v},
      W.1.1.LiesOver v.1 :=
    fun W =>
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v},
      Algebra vK.Completion W.1.1.Completion :=
    fun W =>
      AbsoluteValue.completionAlgebra vK W.1.1
        (eAbove W).2
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v},
      Module.Finite vK.Completion W.1.1.Completion :=
    fun W =>
      completionModuleFinite vK hvK (eAbove W)
  have hcompletion :=
    infiniteComponent_norm_eq_prod_completion
      (K := K) (L := L) v a
  change
    infiniteComponent v (norm K L a) =
      ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        LocalFieldTheory.normUnits
          v.Completion W.1.Completion
          (infiniteComponent W.1 a)
  calc
    infiniteComponent v (norm K L a) =
        Units.mapEquiv eBase.symm.toMulEquiv
          (Units.mapEquiv eBase.toMulEquiv
            (infiniteComponent v (norm K L a))) := by
      apply Units.ext
      simp
    _ = Units.mapEquiv eBase.symm.toMulEquiv
        (∏ W : {W : InfinitePlace L //
            _root_.infinitePlaceBelow (K := K) W = v},
          Units.map (Algebra.norm vK.Completion)
            (Units.mapEquiv
              (InfinitePlace.Completion.equiv W.1).toMulEquiv
              (infiniteComponent W.1 a))) := by
      exact
        congrArg (Units.mapEquiv eBase.symm.toMulEquiv) hcompletion
    _ = ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        Units.mapEquiv eBase.symm.toMulEquiv
          (Units.map (Algebra.norm vK.Completion)
            (Units.mapEquiv
              (InfinitePlace.Completion.equiv W.1).toMulEquiv
              (infiniteComponent W.1 a))) := by
      rw [map_prod]
    _ = ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v},
        LocalFieldTheory.normUnits
          v.Completion W.1.Completion
          (infiniteComponent W.1 a) := by
      apply Finset.prod_congr rfl
      intro W _
      let eExtension :=
        (InfinitePlace.Completion.equiv W.1).symm
      let x : W.1.1.Completionˣ :=
        Units.mapEquiv
          (InfinitePlace.Completion.equiv W.1).toMulEquiv
          (infiniteComponent W.1 a)
      have hWrapperCompletion :
          RingHom.comp
              (algebraMap v.1.Completion W.1.1.Completion)
              eBase.toRingEquiv =
            RingHom.comp
              (InfinitePlace.Completion.equiv W.1).toRingHom
              (algebraMap v.Completion W.1.Completion) := by
        have hComparison :=
          _root_.infinitePlaceCompletionAlgEquiv_algebraMap
            (K := K) (L := L) v W.1 W.2
        dsimp only [eBase, infinitePlaceCompletionAlgEquiv] at hComparison ⊢
        exact hComparison
      have hCompatible :=
        LocalClassFieldTheory.ringEquiv_compat_symm
          eBase.toRingEquiv
          (InfinitePlace.Completion.equiv W.1)
          hWrapperCompletion
      have hNorm :=
        LocalClassFieldTheory.normUnits_map_ringEquiv
          eBase.symm.toRingEquiv eExtension hCompatible x
      have hx :
          Units.mapEquiv eExtension.toMulEquiv x =
            infiniteComponent W.1 a := by
        apply Units.ext
        change
          (InfinitePlace.Completion.equiv W.1).symm
              ((InfinitePlace.Completion.equiv W.1)
                (infiniteComponent W.1 a : W.1.Completion)) =
            (infiniteComponent W.1 a : W.1.Completion)
        exact
          (InfinitePlace.Completion.equiv W.1).symm_apply_apply _
      rw [hx] at hNorm
      change
        Units.mapEquiv eBase.symm.toMulEquiv
            (LocalFieldTheory.normUnits
              vK.Completion W.1.1.Completion x) =
          LocalFieldTheory.normUnits
            v.Completion W.1.Completion
            (infiniteComponent W.1 a)
      exact hNorm

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormTopology_Continuity
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instContinuousSMulPadicLocalAlgebra _root_.OAI.PrimeDegreePackets.instIsModuleTopologyPadicLocalAlgebra _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseNontriviallyNormedField _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_mk _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.mem_finitePlaceDecompositionGroup_iff _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Continuity of the global idele norm

The norm on ideles in a finite number-field extension is continuous. The
proof works first on the open chart with integral finite components and then
uses the topological-group structure to obtain continuity everywhere.
-/

open scoped BigOperators NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

open AlgebraicNumberTheory.Valuations

universe u v w

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- A concrete finite-place local norm carries concrete integer units to
concrete integer units. -/
theorem finitePlace_normUnits_mem_integerUnits
    (v₀ : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀})
    (z : (W.1.adicCompletionIntegers L).units) :
    letI : Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
    LocalFieldTheory.normUnits
        (v₀.adicCompletion K) (W.1.adicCompletion L)
        ((W.1.adicCompletionIntegers L).units.subtype z) ∈
      (v₀.adicCompletionIntegers K).units := by
  let : Algebra
      (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
  apply
    (FiniteIdeleGroup.localOrder_eq_zero_iff v₀
      (LocalFieldTheory.normUnits
        (v₀.adicCompletion K) (W.1.adicCompletion L)
        ((W.1.adicCompletionIntegers L).units.subtype z))).mp
  rw [FiniteIdeleGroup.localOrder_normUnits]
  rw [(FiniteIdeleGroup.localOrder_eq_zero_iff W.1
    ((W.1.adicCompletionIntegers L).units.subtype z)).mpr z.property]
  simp

omit [FiniteDimensional K L] in
theorem finitePlace_normUnits_continuous
    (v₀ : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀}) :
    letI : Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
    Continuous
      (LocalFieldTheory.normUnits
        (v₀.adicCompletion K) (W.1.adicCompletion L)) := by
  let : Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
  let : IsScalarTower
      K (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    finitePlaceAdicCompletionMap_isScalarTower K L v₀ W
  let : ContinuousSMul
      (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (by
      change Continuous (finitePlaceAdicCompletionMap K L v₀ W)
      exact finitePlaceAdicCompletionMap_continuous K L v₀ W)
  let : FiniteDimensional
      (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    inferInstance
  let : NontriviallyNormedField (v₀.adicCompletion K) :=
    NontriviallyNormedField.ofNormNeOne (by
      obtain ⟨ϖ, hϖ⟩ :=
        IsDiscreteValuationRing.exists_irreducible
          (v₀.adicCompletionIntegers K)
      refine ⟨(ϖ : v₀.adicCompletion K), ?_, ?_⟩
      · intro h
        exact hϖ.ne_zero (Subtype.ext h)
      · exact ne_of_lt (RayClass.local_irreducible_norm_lt_one v₀ hϖ))
  exact
    LocalFieldTheory.normUnits_continuous_of_finiteDimensional
      (v₀.adicCompletion K) (W.1.adicCompletion L)

/-- The product of all finite local norms on the integral finite components. -/
noncomputable def integralFiniteNormComponents
    (a :
      InfiniteIdeleGroup L ×
        (∀ W : HeightOneSpectrum (𝓞 L),
          (W.adicCompletionIntegers L).units)) :
    ∀ v₀ : HeightOneSpectrum (𝓞 K),
      (v₀.adicCompletionIntegers K).units :=
  fun v₀ => by
    classical
    let vK := HeightOneSpectrum.adicAbv K v₀
    let hvK0 : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v₀
    let eAbove :=
      finitePlaceExtensionEquivAbove
        (K := K) (L := L) v₀
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK0
    letI : Fintype {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀} :=
      Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
    letI : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀},
        Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      fun W =>
        (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
    refine
      ⟨∏ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v₀},
        LocalFieldTheory.normUnits
          (v₀.adicCompletion K) (W.1.adicCompletion L)
          ((W.1.adicCompletionIntegers L).units.subtype (a.2 W.1)), ?_⟩
    exact
      Subgroup.prod_mem
        (v₀.adicCompletionIntegers K).units
        (t := Finset.univ)
        (f := fun W : {W : HeightOneSpectrum (𝓞 L) //
            _root_.finitePlaceBelow (K := K) W = v₀} =>
          LocalFieldTheory.normUnits
            (v₀.adicCompletion K) (W.1.adicCompletion L)
            ((W.1.adicCompletionIntegers L).units.subtype (a.2 W.1)))
        (fun W _ =>
          finitePlace_normUnits_mem_integerUnits
            (K := K) (L := L) v₀ W (a.2 W.1))

/-- The finite local norm product is continuous on the integral-idele chart. -/
theorem integralFiniteNormComponents_continuous :
    Continuous (integralFiniteNormComponents K L) := by
  rw [continuous_pi_iff]
  intro v₀
  apply continuous_induced_rng.mpr
  classical
  let vK := HeightOneSpectrum.adicAbv K v₀
  let hvK0 : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v₀
  let eAbove :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v₀
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK0
  let : Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
  let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀},
      Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    fun W =>
      (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
  apply continuous_finsetProd Finset.univ
  intro W _
  exact
    (finitePlace_normUnits_continuous
      (K := K) (L := L) v₀ W).comp
      (continuous_subtype_val.comp
        ((continuous_apply W.1).comp continuous_snd))

/-- The product of the archimedean local norms on the integral-idele chart. -/
noncomputable def integralInfiniteNormComponents
    (a :
      InfiniteIdeleGroup L ×
        (∀ W : HeightOneSpectrum (𝓞 L),
          (W.adicCompletionIntegers L).units)) :
    ∀ v₀ : InfinitePlace K, v₀.Completionˣ :=
  fun v₀ => by
    classical
    letI : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v₀},
        W.1.1.LiesOver v₀.1 :=
      fun W =>
        ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    letI : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v₀},
        Algebra v₀.Completion W.1.Completion :=
      fun W =>
        (NumberField.LiesOver.completionMap
          (v := v₀) (w := W.1)).toAlgebra
    exact
      ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v₀},
        LocalFieldTheory.normUnits
          v₀.Completion W.1.Completion
          (ContinuousMulEquiv.piUnits a.1 W.1)

omit [NumberField L] in
/-- A norm between completions at infinite places is continuous. -/
theorem infinitePlace_normUnits_continuous
    (v₀ : InfinitePlace K)
    (W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v₀}) :
    letI : W.1.1.LiesOver v₀.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    letI : Algebra v₀.Completion W.1.Completion :=
      (NumberField.LiesOver.completionMap
        (v := v₀) (w := W.1)).toAlgebra
    Continuous
      (LocalFieldTheory.normUnits v₀.Completion W.1.Completion) := by
  let : W.1.1.LiesOver v₀.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  let : Algebra v₀.Completion W.1.Completion :=
    (NumberField.LiesOver.completionMap
      (v := v₀) (w := W.1)).toAlgebra
  rcases v₀.isReal_or_isComplex with hvReal | hvComplex
  · rcases W.1.isReal_or_isComplex with hWReal | hWComplex
    · let eBase :=
        InfinitePlace.Completion.ringEquivRealOfIsReal hvReal
      let eExtension :=
        InfinitePlace.Completion.ringEquivRealOfIsReal hWReal
      let eBaseUnits : v₀.Completionˣ ≃* ℝˣ :=
        Units.mapEquiv eBase.toMulEquiv
      let eExtensionUnits : W.1.Completionˣ ≃* ℝˣ :=
        Units.mapEquiv eExtension.toMulEquiv
      let :
          NumberField.ComplexEmbedding.LiesOver
            (InfinitePlace.Completion.extensionEmbedding W.1)
            (InfinitePlace.Completion.extensionEmbedding v₀) :=
        InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
          W.1 hvReal
      have hCompatible :
          RingHom.comp (algebraMap ℝ ℝ) eBase.toRingHom =
            RingHom.comp eExtension.toRingHom
              (algebraMap v₀.Completion W.1.Completion) := by
        ext z
        change
          InfinitePlace.Completion.extensionEmbeddingOfIsReal
              hvReal z =
            InfinitePlace.Completion.extensionEmbeddingOfIsReal
              hWReal ((algebraMap v₀.Completion W.1.Completion) z)
        apply Complex.ofReal_injective
        simpa only [
          InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply] using
          (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
            W.1 (v := v₀)).symm
      have hBaseUnitsContinuous : Continuous eBaseUnits.symm := by
        change Continuous (Units.map eBase.symm.toMonoidHom)
        simpa only [eBase] using
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hvReal).symm.continuous.units_map _
      have hExtensionUnitsContinuous : Continuous eExtensionUnits := by
        change Continuous (Units.map eExtension.toMonoidHom)
        refine
          ((InfinitePlace.Completion.isometryEquivRealOfIsReal hWReal).continuous.units_map _).congr ?_
        intro x
        apply Units.ext
        rfl
      have hNormEq :
          (fun x : W.1.Completionˣ =>
            LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
            fun x =>
              eBaseUnits.symm
                (LocalFieldTheory.normUnits ℝ ℝ (eExtensionUnits x)) := by
        funext x
        apply eBaseUnits.injective
        calc
          eBaseUnits (LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
              LocalFieldTheory.normUnits ℝ ℝ (eExtensionUnits x) := by
            simpa only [eBaseUnits, eExtensionUnits] using
              (LocalClassFieldTheory.normUnits_map_ringEquiv
                eBase eExtension hCompatible x)
          _ = eBaseUnits
              (eBaseUnits.symm
                (LocalFieldTheory.normUnits ℝ ℝ (eExtensionUnits x))) := by
            simp
      change Continuous (fun x : W.1.Completionˣ =>
        LocalFieldTheory.normUnits v₀.Completion W.1.Completion x)
      rw [hNormEq]
      exact hBaseUnitsContinuous.comp
        ((LocalFieldTheory.normUnits_continuous_of_finiteDimensional ℝ ℝ).comp
          hExtensionUnitsContinuous)
    · let eBase :=
        InfinitePlace.Completion.ringEquivRealOfIsReal hvReal
      let eExtension :=
        InfinitePlace.Completion.ringEquivComplexOfIsComplex hWComplex
      let eBaseUnits : v₀.Completionˣ ≃* ℝˣ :=
        Units.mapEquiv eBase.toMulEquiv
      let eExtensionUnits : W.1.Completionˣ ≃* ℂˣ :=
        Units.mapEquiv eExtension.toMulEquiv
      let :
          NumberField.ComplexEmbedding.LiesOver
            (InfinitePlace.Completion.extensionEmbedding W.1)
            (InfinitePlace.Completion.extensionEmbedding v₀) :=
        InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
          W.1 hvReal
      have hCompatible :
          RingHom.comp (algebraMap ℝ ℂ) eBase.toRingHom =
            RingHom.comp eExtension.toRingHom
              (algebraMap v₀.Completion W.1.Completion) := by
        ext z
        simp [eBase, eExtension]
      have hBaseUnitsContinuous : Continuous eBaseUnits.symm := by
        change Continuous (Units.map eBase.symm.toMonoidHom)
        simpa only [eBase] using
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hvReal).symm.continuous.units_map _
      have hExtensionUnitsContinuous : Continuous eExtensionUnits := by
        change Continuous (Units.map eExtension.toMonoidHom)
        refine
          ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex hWComplex).continuous.units_map _).congr ?_
        intro x
        apply Units.ext
        rfl
      have hNormEq :
          (fun x : W.1.Completionˣ =>
            LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
            fun x =>
              eBaseUnits.symm
                (LocalFieldTheory.normUnits ℝ ℂ (eExtensionUnits x)) := by
        funext x
        apply eBaseUnits.injective
        calc
          eBaseUnits (LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
              LocalFieldTheory.normUnits ℝ ℂ (eExtensionUnits x) := by
            simpa only [eBaseUnits, eExtensionUnits] using
              (LocalClassFieldTheory.normUnits_map_ringEquiv
                eBase eExtension hCompatible x)
          _ = eBaseUnits
              (eBaseUnits.symm
                (LocalFieldTheory.normUnits ℝ ℂ (eExtensionUnits x))) := by
            simp
      change Continuous (fun x : W.1.Completionˣ =>
        LocalFieldTheory.normUnits v₀.Completion W.1.Completion x)
      rw [hNormEq]
      exact hBaseUnitsContinuous.comp
        ((LocalFieldTheory.normUnits_continuous_of_finiteDimensional ℝ ℂ).comp
          hExtensionUnitsContinuous)
  · have hWComplex : W.1.IsComplex :=
      InfinitePlace.LiesOver.isComplex_of_isComplex_under W.1 hvComplex
    let eBase :=
      InfinitePlace.Completion.ringEquivComplexOfIsComplex hvComplex
    let eBaseUnits : v₀.Completionˣ ≃* ℂˣ :=
      Units.mapEquiv eBase.toMulEquiv
    have hBaseUnitsContinuous : Continuous eBaseUnits.symm := by
      change Continuous (Units.map eBase.symm.toMonoidHom)
      simpa only [eBase] using
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hvComplex).symm.continuous.units_map _
    rcases
        InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq
          W.1 v₀ with hEmbedding | hConjugate
    · let eExtension :=
        InfinitePlace.Completion.ringEquivComplexOfIsComplex hWComplex
      let eExtensionUnits : W.1.Completionˣ ≃* ℂˣ :=
        Units.mapEquiv eExtension.toMulEquiv
      let :
          NumberField.ComplexEmbedding.LiesOver W.1.embedding v₀.embedding :=
        ⟨hEmbedding⟩
      let :
          NumberField.ComplexEmbedding.LiesOver
            (InfinitePlace.Completion.extensionEmbedding W.1)
            (InfinitePlace.Completion.extensionEmbedding v₀) :=
        InfinitePlace.Completion.liesOver_extensionEmbedding W.1 v₀
      have hCompatible :
          RingHom.comp (algebraMap ℂ ℂ) eBase.toRingHom =
            RingHom.comp eExtension.toRingHom
              (algebraMap v₀.Completion W.1.Completion) := by
        ext z
        change
          InfinitePlace.Completion.extensionEmbedding v₀ z =
            InfinitePlace.Completion.extensionEmbedding W.1
              ((algebraMap v₀.Completion W.1.Completion) z)
        exact
          (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
            W.1 (v := v₀)).symm
      have hExtensionUnitsContinuous : Continuous eExtensionUnits := by
        change Continuous (Units.map eExtension.toMonoidHom)
        refine
          ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex hWComplex).continuous.units_map _).congr ?_
        intro x
        apply Units.ext
        rfl
      have hNormEq :
          (fun x : W.1.Completionˣ =>
            LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
            fun x =>
              eBaseUnits.symm
                (LocalFieldTheory.normUnits ℂ ℂ (eExtensionUnits x)) := by
        funext x
        apply eBaseUnits.injective
        calc
          eBaseUnits (LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
              LocalFieldTheory.normUnits ℂ ℂ (eExtensionUnits x) := by
            simpa only [eBaseUnits, eExtensionUnits] using
              (LocalClassFieldTheory.normUnits_map_ringEquiv
                eBase eExtension hCompatible x)
          _ = eBaseUnits
              (eBaseUnits.symm
                (LocalFieldTheory.normUnits ℂ ℂ (eExtensionUnits x))) := by
            simp
      change Continuous (fun x : W.1.Completionˣ =>
        LocalFieldTheory.normUnits v₀.Completion W.1.Completion x)
      rw [hNormEq]
      exact hBaseUnitsContinuous.comp
        ((LocalFieldTheory.normUnits_continuous_of_finiteDimensional ℂ ℂ).comp
          hExtensionUnitsContinuous)
    · let eExtension :=
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hWComplex).trans
          (starRingAut (R := ℂ))
      let eExtensionUnits : W.1.Completionˣ ≃* ℂˣ :=
        Units.mapEquiv eExtension.toMulEquiv
      let :
          NumberField.ComplexEmbedding.LiesOver
            (ComplexEmbedding.conjugate W.1.embedding) v₀.embedding :=
        ⟨hConjugate⟩
      let :
          NumberField.ComplexEmbedding.LiesOver
            (ComplexEmbedding.conjugate
              (InfinitePlace.Completion.extensionEmbedding W.1))
            (InfinitePlace.Completion.extensionEmbedding v₀) :=
        InfinitePlace.Completion.liesOver_conjugate_extensionEmbedding W.1 v₀
      have hCompatible :
          RingHom.comp (algebraMap ℂ ℂ) eBase.toRingHom =
            RingHom.comp eExtension.toRingHom
              (algebraMap v₀.Completion W.1.Completion) := by
        ext z
        simp [eBase, eExtension, ← ComplexEmbedding.conjugate_coe_eq]
      have hExtensionContinuous : Continuous eExtension := by
        refine
          (InfinitePlace.Completion.isometry_extensionEmbedding W.1).continuous.star.congr ?_
        intro x
        change
          star (InfinitePlace.Completion.extensionEmbedding W.1 x) =
            star (InfinitePlace.Completion.extensionEmbedding W.1 x)
        rfl
      have hExtensionUnitsContinuous : Continuous eExtensionUnits := by
        change Continuous (Units.map eExtension.toMonoidHom)
        exact hExtensionContinuous.units_map _
      have hNormEq :
          (fun x : W.1.Completionˣ =>
            LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
            fun x =>
              eBaseUnits.symm
                (LocalFieldTheory.normUnits ℂ ℂ (eExtensionUnits x)) := by
        funext x
        apply eBaseUnits.injective
        calc
          eBaseUnits (LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
              LocalFieldTheory.normUnits ℂ ℂ (eExtensionUnits x) := by
            simpa only [eBaseUnits, eExtensionUnits] using
              (LocalClassFieldTheory.normUnits_map_ringEquiv
                eBase eExtension hCompatible x)
          _ = eBaseUnits
              (eBaseUnits.symm
                (LocalFieldTheory.normUnits ℂ ℂ (eExtensionUnits x))) := by
            simp
      change Continuous (fun x : W.1.Completionˣ =>
        LocalFieldTheory.normUnits v₀.Completion W.1.Completion x)
      rw [hNormEq]
      exact hBaseUnitsContinuous.comp
        ((LocalFieldTheory.normUnits_continuous_of_finiteDimensional ℂ ℂ).comp
          hExtensionUnitsContinuous)

/-- The archimedean local norm product is continuous on the
integral-idele chart. -/
theorem integralInfiniteNormComponents_continuous :
    Continuous (integralInfiniteNormComponents K L) := by
  rw [continuous_pi_iff]
  intro v₀
  classical
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v₀},
      W.1.1.LiesOver v₀.1 :=
    fun W =>
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v₀},
      Algebra v₀.Completion W.1.Completion :=
    fun W =>
      (NumberField.LiesOver.completionMap
        (v := v₀) (w := W.1)).toAlgebra
  apply continuous_finsetProd Finset.univ
  intro W _
  exact
    (infinitePlace_normUnits_continuous
      (K := K) (L := L) v₀ W).comp
      ((continuous_apply W.1).comp
        (ContinuousMulEquiv.piUnits.continuous.comp continuous_fst))

/-- The open chart consisting of arbitrary infinite components and integral
finite components. -/
def integralIdeleEmbedding
    (F : Type w) [Field F] [NumberField F] :
    (InfiniteIdeleGroup F ×
        (∀ v₀ : HeightOneSpectrum (𝓞 F),
          (v₀.adicCompletionIntegers F).units)) →
      IdeleGroup F :=
  Prod.map id
    (RestrictedProduct.structureMap
      (fun v₀ : HeightOneSpectrum (𝓞 F) =>
        (v₀.adicCompletion F)ˣ)
      (fun v₀ : HeightOneSpectrum (𝓞 F) =>
        ((v₀.adicCompletionIntegers F).units :
          Set (v₀.adicCompletion F)ˣ))
      Filter.cofinite)

/-- The integral-idele chart is an open subspace of the idele group. -/
theorem integralIdeleEmbedding_isOpenEmbedding
    (F : Type w) [Field F] [NumberField F] :
    Topology.IsOpenEmbedding (integralIdeleEmbedding F) := by
  exact
    Topology.IsOpenEmbedding.id.prodMap
      (RestrictedProduct.isOpenEmbedding_structureMap
        (isOpen_finiteLocalUnits F))

/-- The finite part of the norm on the integral chart is the restricted
product structure map of the finite local norm products. -/
theorem norm_integralIdeleEmbedding_finite
    (a :
      InfiniteIdeleGroup L ×
        (∀ W : HeightOneSpectrum (𝓞 L),
          (W.adicCompletionIntegers L).units)) :
    (norm K L (integralIdeleEmbedding L a)).2 =
      RestrictedProduct.structureMap
        (fun v₀ : HeightOneSpectrum (𝓞 K) =>
          (v₀.adicCompletion K)ˣ)
        (fun v₀ : HeightOneSpectrum (𝓞 K) =>
          ((v₀.adicCompletionIntegers K).units :
            Set (v₀.adicCompletion K)ˣ))
        Filter.cofinite
        (integralFiniteNormComponents K L a) := by
  classical
  apply RestrictedProduct.ext
  intro v₀
  let vK := HeightOneSpectrum.adicAbv K v₀
  let hvK0 : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v₀
  let eAbove :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v₀
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK0
  let : Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
  let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀},
      Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    fun W =>
      (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
  change
    finiteComponent v₀
        (norm K L (integralIdeleEmbedding L a)) =
      ∏ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v₀},
        LocalFieldTheory.normUnits
          (v₀.adicCompletion K) (W.1.adicCompletion L)
          ((W.1.adicCompletionIntegers L).units.subtype (a.2 W.1))
  rw [finiteComponent_norm_eq_prod]
  rfl

/-- The infinite part of the norm on the integral chart is the product of
the archimedean local norms. -/
theorem norm_integralIdeleEmbedding_infinite
    (a :
      InfiniteIdeleGroup L ×
        (∀ W : HeightOneSpectrum (𝓞 L),
          (W.adicCompletionIntegers L).units)) :
    (norm K L (integralIdeleEmbedding L a)).1 =
      ContinuousMulEquiv.piUnits.symm
        (integralInfiniteNormComponents K L a) := by
  classical
  apply ContinuousMulEquiv.piUnits.injective
  funext v₀
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v₀},
      W.1.1.LiesOver v₀.1 :=
    fun W =>
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  let vK := v₀.1
  let hvK : vK.IsNontrivial := v₀.isNontrivial
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  change
    infiniteComponent v₀
        (norm K L (integralIdeleEmbedding L a)) =
      ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v₀},
        LocalFieldTheory.normUnits
          v₀.Completion W.1.Completion
          (ContinuousMulEquiv.piUnits a.1 W.1)
  rw [infiniteComponent_norm_eq_prod]
  let eAbove :=
    infinitePlaceAboveEquivExtension (K := K) (L := L) v₀
  have hUniv :
      @Finset.univ
          {W : InfinitePlace L //
            _root_.infinitePlaceBelow (K := K) W = v₀}
          (Fintype.ofEquiv (AbsoluteValueExtension v₀.1 L) eAbove.symm) =
        @Finset.univ
          {W : InfinitePlace L //
            _root_.infinitePlaceBelow (K := K) W = v₀}
          (Subtype.fintype fun W =>
            _root_.infinitePlaceBelow (K := K) W = v₀) := by
    ext W
    simp
  rw [hUniv]
  rfl

/-- The actual idele norm is continuous on the open integral-idele chart. -/
theorem norm_comp_integralIdeleEmbedding_continuous :
    Continuous
      ((norm K L : IdeleGroup L → IdeleGroup K) ∘
        integralIdeleEmbedding L) := by
  let target :
      (InfiniteIdeleGroup L ×
          (∀ W : HeightOneSpectrum (𝓞 L),
            (W.adicCompletionIntegers L).units)) →
        IdeleGroup K :=
    fun a =>
      (ContinuousMulEquiv.piUnits.symm
          (integralInfiniteNormComponents K L a),
        RestrictedProduct.structureMap
          (fun v₀ : HeightOneSpectrum (𝓞 K) =>
            (v₀.adicCompletion K)ˣ)
          (fun v₀ : HeightOneSpectrum (𝓞 K) =>
            ((v₀.adicCompletionIntegers K).units :
              Set (v₀.adicCompletion K)ˣ))
          Filter.cofinite
          (integralFiniteNormComponents K L a))
  have hInfinite :
      Continuous (fun a =>
        ContinuousMulEquiv.piUnits.symm
          (integralInfiniteNormComponents K L a)) :=
    ContinuousMulEquiv.piUnits.symm.continuous.comp
      (integralInfiniteNormComponents_continuous K L)
  have hFinite :
      Continuous (fun a =>
        RestrictedProduct.structureMap
          (fun v₀ : HeightOneSpectrum (𝓞 K) =>
            (v₀.adicCompletion K)ˣ)
          (fun v₀ : HeightOneSpectrum (𝓞 K) =>
            ((v₀.adicCompletionIntegers K).units :
              Set (v₀.adicCompletion K)ˣ))
          Filter.cofinite
          (integralFiniteNormComponents K L a)) :=
    (RestrictedProduct.isOpenEmbedding_structureMap
      (isOpen_finiteLocalUnits K)).continuous.comp
        (integralFiniteNormComponents_continuous K L)
  have hTarget : Continuous target :=
    hInfinite.prodMk hFinite
  rw [show
      ((norm K L : IdeleGroup L → IdeleGroup K) ∘
          integralIdeleEmbedding L) = target by
    funext a
    apply Prod.ext
    · exact norm_integralIdeleEmbedding_infinite K L a
    · exact norm_integralIdeleEmbedding_finite K L a]
  exact hTarget

/-- The norm on the idele group of a finite extension is continuous. -/
theorem norm_continuous :
    Continuous (norm K L) := by
  have hChartAt :
      ContinuousAt
        ((norm K L : IdeleGroup L → IdeleGroup K) ∘
          integralIdeleEmbedding L)
        (1 :
          InfiniteIdeleGroup L ×
            (∀ W : HeightOneSpectrum (𝓞 L),
              (W.adicCompletionIntegers L).units)) :=
    (norm_comp_integralIdeleEmbedding_continuous K L).continuousAt
  have hAt :
      ContinuousAt (norm K L) (1 : IdeleGroup L) := by
    have hAtChart :
        ContinuousAt (norm K L)
          (integralIdeleEmbedding L
            (1 :
              InfiniteIdeleGroup L ×
                (∀ W : HeightOneSpectrum (𝓞 L),
                  (W.adicCompletionIntegers L).units))) :=
      ((integralIdeleEmbedding_isOpenEmbedding L).continuousAt_iff
        (g := (norm K L : IdeleGroup L → IdeleGroup K))).mp hChartAt
    have hOne :
        integralIdeleEmbedding L
          (1 :
            InfiniteIdeleGroup L ×
              (∀ W : HeightOneSpectrum (𝓞 L),
                (W.adicCompletionIntegers L).units)) =
          (1 : IdeleGroup L) := by
      apply Prod.ext
      · rfl
      · apply RestrictedProduct.ext
        intro W
        rfl
    rw [hOne] at hAtChart
    exact hAtChart
  exact continuous_of_continuousAt_one (norm K L) hAt

/-- The idele norm bundled as a continuous monoid homomorphism. -/
noncomputable def ideleNormContinuousMonoidHom :
    IdeleGroup L →ₜ* IdeleGroup K where
  __ := norm K L
  continuous_toFun := norm_continuous K L

@[simp]
theorem ideleNormContinuousMonoidHom_apply
    (a : IdeleGroup L) :
    ideleNormContinuousMonoidHom K L a = norm K L a :=
  rfl

end IdeleGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


noncomputable def finiteResidueAbstractBase
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    DegreeData.FiniteResidueAbstractField (localResidueDatum K) :=
  (intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField (localResidueDatum K)

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
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

theorem finitePlaceArtinCompletionHasExtension
    {K' : Type}
    [Field K'] [NumberField K'] [Algebra K K']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
    let C := vK.Completion
    let D := vK'.Completion
    let hvKna : IsNonarchimedean (vK : K → ℝ) :=
      NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
    let hvK'na : IsNonarchimedean (vK' : K' → ℝ) :=
      NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W
    letI : IsUltrametricDist C :=
      finitePlaceArtinCompletionIsUltrametricDist vK hvKna
    letI : Valued C ℝ≥0 :=
      finitePlaceArtinCompletionValued vK hvKna
    letI : ValuativeRel C :=
      finitePlaceArtinCompletionValuativeRel vK hvKna
    let vC : Valuation C ℝ≥0 := Valued.v
    letI : vC.Compatible :=
      Valuation.Compatible.ofValuation vC
    letI : IsUltrametricDist D :=
      finitePlaceArtinCompletionIsUltrametricDist vK' hvK'na
    letI : Valued D ℝ≥0 :=
      finitePlaceArtinCompletionValued vK' hvK'na
    letI : ValuativeRel D :=
      finitePlaceArtinCompletionValuativeRel vK' hvK'na
    let vD : Valuation D ℝ≥0 := Valued.v
    letI : vD.Compatible :=
      Valuation.Compatible.ofValuation vD
    letI : Algebra C D :=
      (finitePlaceArtinRelativeCompletionRingHom
        (K := K) (K' := K') v W hW).toAlgebra
    (ValuativeRel.valuation C).HasExtension
      (ValuativeRel.valuation D) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
  let C := vK.Completion
  let D := vK'.Completion
  let eC :
      C ≃+* v.adicCompletion K :=
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let eD :
      D ≃+* W.adicCompletion K' :=
    (relativeFinitePlaceCompletionAlgEquiv W).toRingEquiv
  let concreteBaseMap :
      v.adicCompletion K →+* W.adicCompletion K' :=
    finitePlaceAdicCompletionMap K K' v ⟨W, hW⟩
  let : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
    concreteBaseMap.toAlgebra
  let : Algebra C D :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
  let : IsUltrametricDist C :=
    finitePlaceArtinCompletionIsUltrametricDist vK hvKna
  let : Valued C ℝ≥0 :=
    finitePlaceArtinCompletionValued vK hvKna
  let vC : Valuation C ℝ≥0 := Valued.v
  let : ValuativeRel C :=
    finitePlaceArtinCompletionValuativeRel vK hvKna
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let hvK'na : IsNonarchimedean (vK' : K' → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W
  let : IsUltrametricDist D :=
    finitePlaceArtinCompletionIsUltrametricDist vK' hvK'na
  let : Valued D ℝ≥0 :=
    finitePlaceArtinCompletionValued vK' hvK'na
  let vD : Valuation D ℝ≥0 := Valued.v
  let : ValuativeRel D :=
    finitePlaceArtinCompletionValuativeRel vK' hvK'na
  let : vD.Compatible :=
    Valuation.Compatible.ofValuation vD
  exact
    finitePlaceArtinHasExtension_of_norm
      eC eD concreteBaseMap
      (by intro x; rfl)
      (relativeFinitePlaceCompletionAlgEquiv_symm_norm W)
      (fun x =>
        (relativeFinitePlaceCompletionRingHom_isometry
          v).norm_map_of_map_zero
            (map_zero
              (relativeFinitePlaceCompletionRingHom v)) x)
      (finitePlaceAdicCompletionMap_norm_le_one_iff
        K K' v ⟨W, hW⟩)
      (fun _ => rfl)
      (fun _ => rfl)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois
attribute [-simp] _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.ideleClassCongr_mk _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Archimedean Artin homomorphisms

At a ramified infinite place, the local extension is complex over
real.  Its Artin homomorphism sends the sign of a real unit to the
corresponding complex-conjugation element of the decomposition group.
At an unramified infinite place the decomposition group, and hence the
local homomorphism, is trivial.
-/

open scoped BigOperators Classical IsMulCommutative NumberField
  NumberField.LiesOver
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open HilbertRamification
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

variable [IsAbelianGalois K L]

/-- The product of the actual archimedean local Artin homomorphisms
over the finite set of infinite places of `K`. -/
noncomputable def infinitePlaceGlobalArtinMonoidHom :
    IdeleGroup K →* (L ≃ₐ[K] L) :=
  ∏ v : InfinitePlace K,
    (chosenInfinitePlaceArtinMonoidHom
      (K := K) (L := L) v).comp
      (IdeleGroup.infiniteComponent v)

omit [NumberField L] in
/-- Every archimedean factor is trivial on a finite one-place idele. -/
@[simp]
theorem infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    infinitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (finitePlaceIdele v x) =
  1 := by
  unfold infinitePlaceGlobalArtinMonoidHom
  rw [MonoidHom.finsetProd_apply]
  apply Finset.prod_eq_one
  intro w _
  change
    chosenInfinitePlaceArtinMonoidHom
      (K := K) (L := L) w
      (IdeleGroup.infiniteComponent w
        (finitePlaceIdele v x)) =
      1
  have hcomponent :
      IdeleGroup.infiniteComponent w
          (finitePlaceIdele v x) =
        (1 : w.Completionˣ) :=
    finitePlaceIdele_infiniteComponent v w x
  rw [hcomponent]
  exact map_one _

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SimpleExtensionLocalBehavior
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instLocallyCompactSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceLocalTensorUnitsEquiv_infiniteLocalIdeleInclusion_coe _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramified finite places in simple Kummer extensions

This file proves the local unit case of the Kummer ramification criterion.
If both `b` and the exponent `n` are units at a finite place, then the
chosen localization of `K(ⁿ√b) / K` at that place is unramified.

The proof uses the existing algebraic localization, mathlib's minimal
polynomial API, and the complete-DVF different criterion.  No auxiliary
Kummer extension or alternative notion of unramifiedness is introduced.
-/

open scoped NumberField Classical NNReal TensorProduct ValuativeRel
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalFieldTheory
open LocalClassFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type} [Field K] [NumberField K]

/-- A finite Galois number-field extension generated by an `n`-th root of a
unit is unramified at every chosen completion where both the radicand and
`n` are units.

This is the source-producing Kummer criterion: the proof works on the
actual localized completion, proves that the chosen root generates it,
and applies the derivative/different criterion to `X ^ n - b`. -/
theorem
    kummerGeneratedExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
    {L : Type}
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ+)
    (b : Kˣ)
    (beta : Lˣ)
    (hbeta :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom b)
    (hgen :
      IntermediateField.adjoin K
        ({(beta : L)} : Set L) = ⊤)
    (v : HeightOneSpectrum (𝓞 K))
    (hb : v.valuation K (b : K) = 1)
    (hn : v.valuation K ((n : ℕ) : K) = 1) :
    ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K v
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let C := vK.Completion
  let F := LocalizedCompletion vK w
  let : FiniteDimensional C F :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois C F :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  let : NontriviallyNormedField C :=
    absoluteValueExtension_completionNontriviallyNormedField vK hvK
  let : LocallyCompactSpace C :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let : IsUltrametricDist C :=
    completionIsUltrametricDist vK hvKna
  let : Valued C ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let vCNorm : Valuation C ℝ≥0 := Valued.v
  let : vCNorm.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation (K := C)).IsNontrivial)
  let : ValuativeRel C :=
    finitePlaceCompletionValuativeRel vK hvKna
  let : vCNorm.Compatible :=
    Valuation.Compatible.ofValuation vCNorm
  let : ValuativeRel.IsNontrivial C :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vCNorm).2
      inferInstance
  let vC := ValuativeRel.valuation C
  let : vC.IsNontrivial := inferInstance
  let : IsValuativeTopology C :=
    isValuativeTopology_of_valued_ofValuation C ℝ≥0
  let : IsNonarchimedeanLocalField C :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let : FiniteDimensional C w.1.Completion :=
    completionModuleFinite vK hvK w
  let : ContinuousSMul C w.1.Completion :=
    continuousSMul_of_algebraMap _ _
      (AbsoluteValue.completionMap_isometry vK w.1 w.2).continuous
  let : LocallyCompactSpace w.1.Completion :=
    LocallyCompactSpace.of_finiteDimensional_of_complete
      C w.1.Completion
  let eCompletion : F ≃ᵢ w.1.Completion :=
    { toEquiv :=
        (localizedCompletionEquivCompletion
          vK hvK w).toEquiv
      isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl }
  let : LocallyCompactSpace F :=
    (eCompletion.toHomeomorph.locallyCompactSpace_iff).2
      inferInstance
  let : IsUltrametricDist F :=
    localizedCompletionIsUltrametricDist
      vK w hvKna
  let : Valued F ℝ≥0 :=
    localizedCompletionFinitePlaceValued
      vK w hvKna
  let : ValuativeRel F :=
    localizedCompletionFinitePlaceValuativeRel
      vK w hvKna
  let vFNorm : Valuation F ℝ≥0 := Valued.v
  let : vFNorm.Compatible :=
    Valuation.Compatible.ofValuation vFNorm
  let vF := ValuativeRel.valuation F
  let : Valuation.HasExtension vC vF :=
    localizedCompletionValuationHasExtension
      vK w hvKna
  let : vF.IsNontrivial :=
    valuativeRelExtension_isNontrivial (C := C) (F := F)
  let : ValuativeRel.IsNontrivial F :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vF).2
      inferInstance
  let : IsValuativeTopology F :=
    isValuativeTopology_of_valued_ofValuation F ℝ≥0
  let : IsNonarchimedeanLocalField F :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let : Algebra 𝒪[C] F :=
    Algebra.ofSubsemiring 𝒪[C]
  let :=
    localizedCompletionIsIntegralClosureWithExtension
      vK w hvK hvKna
  let : Module.Finite 𝒪[C] 𝒪[F] :=
    integerRing_moduleFinite_of_isIntegralClosure C F

  have hbAbv : vK (b : K) = 1 := by
    rw [HeightOneSpectrum.adicAbv_def, hb]
    simp
  have hnAbv : vK ((n : ℕ) : K) = 1 := by
    rw [HeightOneSpectrum.adicAbv_def, hn]
    simp
  have hbNorm :
      ‖algebraMap K C (b : K)‖ = 1 := by
    calc
      ‖algebraMap K C (b : K)‖ = vK (b : K) :=
        AbsoluteValue.completionAbsoluteValue_coe vK (b : K)
      _ = 1 := hbAbv
  let bC : C := algebraMap K C (b : K)
  have hbCNorm : vCNorm bC = 1 := by
    change ‖bC‖₊ = 1
    exact NNReal.eq (by simpa [bC] using hbNorm)
  have hbCVal : vC bC = 1 :=
    (ValuativeRel.isEquiv vCNorm vC).eq_one_iff_eq_one.mp hbCNorm
  have hnNorm : ‖((n : ℕ) : C)‖ = 1 := by
    calc
      ‖((n : ℕ) : C)‖ =
          ‖algebraMap K C ((n : ℕ) : K)‖ := by
            rw [map_natCast]
      _ = vK ((n : ℕ) : K) :=
        AbsoluteValue.completionAbsoluteValue_coe vK ((n : ℕ) : K)
      _ = 1 := hnAbv
  let nC : C := (n : ℕ)
  have hnCNorm : vCNorm nC = 1 := by
    change ‖nC‖₊ = 1
    exact NNReal.eq (by simpa [nC] using hnNorm)
  have hnCVal : vC nC = 1 :=
    (ValuativeRel.isEquiv vCNorm vC).eq_one_iff_eq_one.mp hnCNorm
  let betaL : L := (beta : L)
  let betaF : F :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 betaL
  have hbetaLpow :
      betaL ^ (n : ℕ) = algebraMap K L (b : K) :=
    congrArg Units.val hbeta
  have hbetaFpow :
      betaF ^ (n : ℕ) =
        algebraMap C F (algebraMap K C (b : K)) := by
    have hmap :=
      congrArg
        (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2)
        hbetaLpow
    simpa only [betaF, map_pow,
      AbsoluteValue.toAlgebraicLocalization_algebraMap] using hmap
  have hbetaWpow : (w.1 betaL) ^ (n : ℕ) = 1 := by
    calc
      (w.1 betaL) ^ (n : ℕ) = w.1 (betaL ^ (n : ℕ)) := by
        rw [map_pow]
      _ = w.1 (algebraMap K L (b : K)) := by rw [hbetaLpow]
      _ = vK (b : K) := w.2 (b : K)
      _ = 1 := hbAbv
  have hbetaW : w.1 betaL = 1 :=
    (pow_eq_one_iff_of_nonneg (w.1.nonneg betaL) n.ne_zero).mp
      hbetaWpow
  have hbetaNorm : ‖betaF‖ = 1 := by
    change
      AbsoluteValue.algebraicLocalizationAbsoluteValue
          vK w.1 w.2 betaF = 1
    rw [
      AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization,
      hbetaW]
  have hbetaFNorm : vFNorm betaF = 1 := by
    change ‖betaF‖₊ = 1
    exact NNReal.eq hbetaNorm
  have hbetaFVal : vF betaF = 1 :=
    (ValuativeRel.isEquiv vFNorm vF).eq_one_iff_eq_one.mp hbetaFNorm
  have hglobal : IntermediateField.adjoin K {betaL} = ⊤ := by
    simpa only [betaL] using hgen
  have hR : IntermediateField.adjoin C {betaF} = ⊤ := by
    simpa only [C, F, betaF] using
      localizedCompletion_adjoin_image_eq_top_of_adjoin_eq_top
        vK w betaL hglobal
  have hgenF : Algebra.adjoin C {betaF} = ⊤ := by
    apply
      (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic betaF)).mp
    exact hR
  change IsNonarchimedeanLocalField.IsUnramifiedValuedExtension C F
  exact
    isUnramifiedValuedExtension_of_unit_kummer_generator
      n bC betaF hbCVal hnCVal hbetaFVal hbetaFpow hgenF

/-- A chosen simple Kummer extension is unramified at a finite place where its
radicand and exponent are units.  This is the direct specialization of
the generated-extension derivative criterion above. -/
theorem
    chosenSimpleKummerExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
    (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ)
    (v : HeightOneSpectrum (𝓞 K))
    (hb : v.valuation K (b : K) = 1)
    (hn : v.valuation K ((n : ℕ) : K) = 1) :
    let L := chosenSimpleKummerExtension K n hnK b
    letI : FiniteDimensional K L :=
      chosenSimpleKummerExtension_finiteDimensional K n hnK b
    letI : IsAbelianGalois K L :=
      chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    letI : NumberField L :=
      NumberField.of_module_finite K L
    ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  let L := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let : NumberField L :=
    NumberField.of_module_finite K L
  let beta : Lˣ :=
    chosenSimpleKummerRootUnit K n hnK b
  apply
    kummerGeneratedExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
      (K := K) (L := L) n b beta
  · dsimp only [L, beta]
    exact chosenSimpleKummerRootUnit_pow K n hnK b
  · simpa [L, beta] using
      chosenSimpleKummerExtension_adjoin_root_eq_top K n hnK b
  · exact hb
  · exact hn

omit [NumberField K] in
/-- At an infinite place where the radicand is already an `n`-th
power, the determinant norm from the simple Kummer tensor algebra is
surjective.  The proof identifies the decomposition group with the
trivial group and then uses the canonical local tensor norm theorem. -/
theorem
    chosenSimpleKummerExtension_infiniteTensorNormSubgroup_eq_top_of_mem_nthPowerSubgroup
    (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ)
    (w : InfinitePlace K)
    (hb :
      Units.map
            (algebraMap K w.Completion).toMonoidHom b ∈
        (powMonoidHom (n : ℕ) :
          w.Completionˣ →* w.Completionˣ).range) :
    let E := chosenSimpleKummerExtension K n hnK b
    letI : FiniteDimensional K E :=
      chosenSimpleKummerExtension_finiteDimensional K n hnK b
    letI : IsAbelianGalois K E :=
      chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    infiniteTensorNormSubgroup
      (K := K) (L := E) w = ⊤ := by
  let E := chosenSimpleKummerExtension K n hnK b
  let : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let vK : AbsoluteValue K ℝ := w.1
  let hvK : vK.IsNontrivial := w.isNontrivial
  let u : AbsoluteValueExtension vK E :=
    pullbackAbsoluteValueExtension
      vK hvK IsAlgClosed.lift
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) u.1
  let : SMul K u.1.Completion := hK.toSMul
  let : Algebra vK.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra vK u.1 u.2
  let := localizedCompletionGlobalAlgebra vK u
  let := localizedCompletionIsScalarTower vK u
  let C := vK.Completion
  let F := LocalizedCompletion vK u
  let eK : w.Completion ≃+* C :=
    (infinitePlaceCompletionAlgEquiv
      (K := K) w).toRingEquiv
  let eC : w.Completionˣ ≃* Cˣ :=
    Units.mapEquiv eK.toMulEquiv
  let : FiniteDimensional C F :=
    localizedCompletionModuleFinite vK hvK u
  let : IsGalois C F :=
    HilbertRamification.algebraicLocalization_isGalois vK u
  let beta : Eˣ :=
    chosenSimpleKummerRootUnit K n hnK b
  have hbeta :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K E).toMonoidHom b := by
    dsimp only [E, beta]
    exact chosenSimpleKummerRootUnit_pow K n hnK b
  have hbC :
      Units.map
            (algebraMap K C).toMonoidHom b ∈
        (powMonoidHom (n : ℕ) : Cˣ →* Cˣ).range := by
    obtain ⟨y, hy⟩ :=
      (MonoidHom.mem_range
        (G := w.Completionˣ)).mp hb
    refine
      (MonoidHom.mem_range
        (G := Cˣ)).mpr ⟨eC y, ?_⟩
    rw [powMonoidHom_apply] at hy ⊢
    calc
      (eC y) ^ (n : ℕ) =
          eC (y ^ (n : ℕ)) :=
        (map_pow eC y (n : ℕ)).symm
      _ =
          eC
            (Units.map
              (algebraMap K w.Completion).toMonoidHom b) :=
        congrArg eC hy
      _ =
          Units.map
            (algebraMap K C).toMonoidHom b := by
        apply Units.ext
        simpa [eC, eK, C, vK] using
          (infinitePlaceCompletionAlgEquiv
            (K := K) w).commutes (b : K)
  have hfixed :
      (beta : E) ∈
        IntermediateField.fixedField
          (absoluteValueDecompositionGroup K u.1) := by
    apply
      kummerRadicand_root_mem_decompositionFixedField_of_mem_nthPowerSubgroup
        (K := K) (L := E) vK hvK u n hmu b beta hbeta
    exact hbC
  let D : Subgroup (E ≃ₐ[K] E) :=
    absoluteValueDecompositionGroup K u.1
  have hgen :
      IntermediateField.adjoin K ({(beta : E)} : Set E) = ⊤ := by
    simpa [E, beta] using
      chosenSimpleKummerExtension_adjoin_root_eq_top K n hnK b
  have hle :
      IntermediateField.adjoin K ({(beta : E)} : Set E) ≤
        IntermediateField.fixedField D := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' : x = (beta : E) :=
      Set.mem_singleton_iff.mp hx
    subst x
    change
      (beta : E) ∈
        IntermediateField.fixedField
          (absoluteValueDecompositionGroup K u.1)
    exact hfixed
  have htop :
      IntermediateField.fixedField D = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact hle
  have hD : D = ⊥ := by
    rw [← IntermediateField.fixingSubgroup_fixedField D,
      htop, IntermediateField.fixingSubgroup_top]
  let eLocal :
      D ≃* (F ≃ₐ[C] F) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK u
  have hdegree :
      Module.finrank C F = 1 := by
    calc
      Module.finrank C F =
          Nat.card (F ≃ₐ[C] F) :=
        (IsGalois.card_aut_eq_finrank C F).symm
      _ = Nat.card D :=
        (Nat.card_congr eLocal.toEquiv).symm
      _ = 1 := by
        rw [hD]
        simp
  let : Module.Free C F :=
    Module.Free.of_divisionRing C F
  have hNormTop :
      localNormSubgroup C F = ⊤ := by
    apply top_unique
    intro x _
    refine
      ⟨Units.map (algebraMap C F).toMonoidHom x, ?_⟩
    apply Units.ext
    change
      Algebra.norm C (algebraMap C F (x : C)) =
        (x : C)
    rw [Algebra.norm_algebraMap, hdegree, pow_one]
  have hLocalTensorTop :
      localTensorNormSubgroup
          (K := K) (L := E) vK =
        ⊤ := by
    rw [localTensorNormSubgroup_eq_localNormSubgroup
      (K := K) (L := E) vK u hvK]
    exact hNormTop
  let eA :
      (w.Completion ⊗[K] E) ≃+*
        LocalTensorAlgebra (L := E) vK :=
    (infinitePlaceLocalTensorAlgEquiv
      (K := K) (L := E) w).toRingEquiv
  let eU :
      (w.Completion ⊗[K] E)ˣ ≃*
        (LocalTensorAlgebra (L := E) vK)ˣ :=
    infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := E) w
  have hnorm
      (z : (w.Completion ⊗[K] E)ˣ) :
      eC
          (infiniteTensorDetNorm
            (K := K) (L := E) w z) =
        localTensorDetNorm
          (K := K) (L := E) vK (eU z) := by
    apply Units.ext
    change
      eK
          (Algebra.norm w.Completion
            (z : w.Completion ⊗[K] E)) =
        Algebra.norm C
          (eA (z : w.Completion ⊗[K] E))
    exact
      _root_.map_norm_tensorProduct_baseChange
        (K := K) (L := E)
        (infinitePlaceCompletionAlgEquiv
          (K := K) w).toAlgHom
        (z : w.Completion ⊗[K] E)
  apply top_unique
  intro x _
  have hx :
      eC x ∈
        localTensorNormSubgroup
          (K := K) (L := E) vK := by
    rw [hLocalTensorTop]
    trivial
  obtain ⟨z, hz⟩ := hx
  refine ⟨eU.symm z, ?_⟩
  apply eC.injective
  rw [hnorm, eU.apply_symm_apply, hz]

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicValuationComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValuativeRel _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

/-- The valuation selected by the concrete p-adic local-field package is
equivalent to mathlib's canonical valuation on `ℚ_[p]`. -/
theorem padicLocalField_valuation_isEquiv_valuativeRelValuation
    (p : ℕ) [Fact p.Prime] :
    (padicLocalField p).toCompleteDVF.valuation.IsEquiv
      (ValuativeRel.valuation ℚ_[p]) := by
  change
    (padicDVRValuation p).IsEquiv
      (ValuativeRel.valuation ℚ_[p])
  exact padicDVRValuation_isEquiv_valuativeRelValuation p

end Qp
end Examples
end DiscreteValuationField
end LocalFieldTheory
end
end


