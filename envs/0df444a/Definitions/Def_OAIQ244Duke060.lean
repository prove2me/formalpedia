-- Prove2me | Definitions.Def_OAIQ244Duke060
-- name    : OAIQ244Duke060
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:18:57.591239+00:00
-- url     : https://prove2.me/theorems/35c073a0-4255-4f98-982c-b7dfb74eb3a9
-- title:
--   Definitions bundle OAIQ244Duke060 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 133 declarations of OpenAI's Lean: 35 definitions, 4 instances and 94 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.finitePlaceArtinRelativeCompletionRingHom`, `GlobalClassFieldTheory.Reciprocity.finitePlaceRelativeNormUnits`, `GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionIntegerRingEquivPadicInt`, `GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionRingEquivPadic`, `LocalClassFieldTheory.unramifiedNormClass`, `LocalClassFieldTheory.unramifiedNormSubgroup`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityContinuousMulEquivZMod`, `LocalFieldTheory.Padic.padicFreeContinuousAddEquiv`, `LocalFieldTheory.Padic.padicPrincipalUnitDirectTopology`, `LocalFieldTheory.Padic.padicPrincipalUnitStandardTopology`, `LocalFieldTheory.Padic.padicResidueEquivZMod`, `LubinTate.standardLubinTateFormalAdd`, `LubinTate.standardLubinTateFormalGroupRightDisplacementFactor`, `LubinTate.standardLubinTateLevelAutomorphismCoefficientUniformSpace`, `LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv`, `LubinTate.standardLubinTateLevelAutomorphismTargetWithIdeal`, `LubinTate.standardLubinTateLevelIntegerToSeparableClosure`, `LubinTate.standardLubinTatePrimitiveActionAlgebra`, `LubinTate.standardLubinTatePrimitiveActionCoefficientUniformSpace`, `LubinTate.standardLubinTatePrimitiveActionTargetWithIdeal`, `LubinTate.standardLubinTatePrimitiveDisplacementTargetWithIdeal`, `LubinTate.standardLubinTatePrimitiveLevelAction`, `LubinTate.standardLubinTatePrimitivePointIntegerAction`, `LubinTate.standardLubinTatePrimitivePointIterateInteger`, `LubinTate.standardLubinTatePrimitiveRootAction`, `LubinTate.standardLubinTateUnitParameter`, `LubinTate.standardLubinTateUnitParameterAlgEquiv`, `LubinTate.standardLubinTateUnitParameterAlgHom`, `LubinTate.standardLubinTateUnitParameterChosenRepresentative`, `LubinTate.standardLubinTateUnitParameterClass`, `LubinTate.standardLubinTateUnitParameterEquivGal`, `LubinTate.standardLubinTateUnitParameterLevelRoot`, `LubinTate.standardLubinTateUnitParameterRoot`, `LubinTate.standardLubinTateUnitParameterToGal`, `LubinTate.standardLubinTateUnitParameterToGalHom`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_CrossLocalRestriction`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `LocalClassFieldTheory_Finite_Existence_UnramifiedNormSubgroup`, `LocalClassFieldTheory_Finite_LocalReciprocity_FiniteSubgroupResidueDegree`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison`, `LocalField_DiscreteValuationField_FieldUnitFactors`, `LocalField_Padic_UnitDecomposition`, `LubinTate_FiniteLevel_CompletedEvaluation`, `LubinTate_FiniteLevel_CompletedIterates`, `LubinTate_FiniteLevel_FiniteParameters`, `LubinTate_FiniteLevel_LevelAbelian`, `LubinTate_FiniteLevel_LevelAutomorphisms`, `LubinTate_FiniteLevel_NormSubgroup`, `LubinTate_FiniteLevel_PrimitiveAction`, `LubinTate_FiniteLevel_PrimitiveDisplacement`, `LubinTate_FiniteLevel_PrimitiveUniformizer`, `LubinTate_FormalModule_StandardFormalGroup`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke046`, `OAIQ244Duke047`, `OAIQ244Duke048`, `OAIQ244Duke049`, `OAIQ244Duke050`, `OAIQ244Duke051` and `OAIQ244Duke052` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke062`, `OAIQ244Duke065`, `OAIQ244Duke066`, `OAIQ244Duke067` and `OAIQ244Duke068`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
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
import Definitions.Def_OAIQ244Duke046
import Definitions.Def_OAIQ244Duke047
import Definitions.Def_OAIQ244Duke048
import Definitions.Def_OAIQ244Duke049
import Definitions.Def_OAIQ244Duke050
import Definitions.Def_OAIQ244Duke051
import Definitions.Def_OAIQ244Duke052

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FiniteSubgroupResidueDegree
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open CyclicCohomology RamificationTheory ClassFormation

open LocalFieldTheory

/-!
# Finite local reciprocity: residue degree of a finite abstract field

This file compares the residue action used by localResidueDatum with the
same residue action after changing the ground field to the fixed field of a
closed subgroup.  The comparison is made on the common selected
residue field, so it also applies when the fixed field is not normal over the
original local field.
-/

noncomputable section

open scoped Pointwise ValuativeRel
open _root_.RamificationTheory.HilbertRamification.ValuationSubring
open Field.absoluteGaloisGroup

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

attribute [local instance] LocalClassFieldTheory.localAbstractFixedResidueIntermediateFieldAlgebra
noncomputable local instance localAbstractFixedResidueIntermediateFieldSMul_r9ad29a_1
    (H : ClosedSubgroup (Gal(SeparableClosure K / K))) :
    SMul
      (decompositionResidueField K (localSeparableValuationSubring K))
      (localAbstractFixedResidueIntermediateField K H) :=
  @Algebra.toSMul _ _ _ _
    (localAbstractFixedResidueIntermediateFieldAlgebra K H)
attribute [local instance] LocalClassFieldTheory.localAbstractFixedResidueIntermediateFieldModule
/-- **Finite local reciprocity, pointwise fixed-field degree comparison.**
The normalized degree on a finite abstract field is the ordinary intrinsic
absolute residue degree after changing the finite residue base to the
residue subfield selected by that fixed field. -/
theorem localResidueDatum_normalizedDegree_eq_residueAbsoluteDegreeIn
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (sigma : H.field.toSubgroup) :
    let F := localAbstractFixedResidueIntermediateField K H.field
    letI : Algebra
        (decompositionResidueField K (localSeparableValuationSubring K))
        F := F.algebra
    letI : Module
        (decompositionResidueField K (localSeparableValuationSubring K))
        F := Algebra.toModule
    letI : FiniteDimensional
        (decompositionResidueField K (localSeparableValuationSubring K))
        F :=
      localAbstractFixedResidueIntermediateField_finiteDimensional K H.field
    letI : Finite F := Module.finite_of_finite
      (decompositionResidueField K (localSeparableValuationSubring K))
    letI : Fintype F := Fintype.ofFinite F
    (localResidueDatum K).normalizedDegree
        (H.toFiniteResidueAbstractField (localResidueDatum K)) sigma =
      residueAbsoluteDegreeIn F
        (selectedResidueField (localSeparableValuationSubring K))
        (localAbstractFixedResidueActionOverIntermediateField
          K H.field sigma) := by
  let A := localSeparableValuationSubring K
  let k := decompositionResidueField K A
  let Omega := selectedResidueField A
  let F := localAbstractFixedResidueIntermediateField K H.field
  let : Algebra k F := F.algebra
  let : FiniteDimensional k F :=
    localAbstractFixedResidueIntermediateField_finiteDimensional K H.field
  let : Finite F := Module.finite_of_finite k
  let : Fintype F := Fintype.ofFinite F
  let HF := H.toFiniteResidueAbstractField (localResidueDatum K)
  let tau : Omega ≃ₐ[F] Omega :=
    localAbstractFixedResidueActionOverIntermediateField K H.field sigma
  have htau :
      tau.restrictScalars k =
        localSeparableResidueAlgAction K sigma.1 := by
    apply AlgEquiv.ext
    intro x
    rfl
  have hbase :=
    residueAbsoluteDegreeIn_restrictScalars k Omega F tau
  rw [htau] at hbase
  have hdegree :
      (HF.residueDegree : ℕ) =
        Module.finrank k F :=
    localResidueDatum_residueDegree_eq_selectedResidueFinrank K H
  apply Multiplicative.ext
  apply zHatMulNat_injective
    HF.residueDegree.property
  change
    (HF.residueDegree : ℕ) •
        ((localResidueDatum K).normalizedDegree HF sigma).toAdd =
      (HF.residueDegree : ℕ) •
        (residueAbsoluteDegreeIn F Omega tau).toAdd
  rw [(localResidueDatum K).residueDegree_nsmul_normalizedDegree HF,
    hdegree]
  change
    (residueAbsoluteDegreeIn k Omega
      (localSeparableResidueAlgAction K sigma.1)).toAdd =
        Module.finrank k F •
          (residueAbsoluteDegreeIn F Omega tau).toAdd
  exact congrArg Multiplicative.toAdd hbase

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_CrossLocalRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Cross-base restriction of finite-place Artin homomorphisms

This module compares localized completions in a square of number fields with different base fields and transports restriction through the corresponding decomposition groups.
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

/-- The continuous ring homomorphism between base completions attached to a finite place lying above another. -/
noncomputable def finitePlaceArtinRelativeCompletionRingHom
    {K' : Type} [Field K'] [NumberField K']
    [Algebra K K']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion →+*
      (NumberField.HeightOneSpectrum.adicAbv K' W).Completion :=
  let eC :=
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let eD :=
    (relativeFinitePlaceCompletionAlgEquiv W).toRingEquiv
  eD.symm.toRingHom.comp
    ((finitePlaceAdicCompletionMap
      K K' v ⟨W, hW⟩).comp eC.toRingHom)

/-- The finite-place map between the relative base completions is continuous. -/
theorem finitePlaceArtinRelativeCompletionRingHom_continuous
    {K' : Type} [Field K'] [NumberField K']
    [Algebra K K']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v) :
    Continuous
      (finitePlaceArtinRelativeCompletionRingHom
        (K := K) (K' := K') v W hW) := by
  let eD :=
    (relativeFinitePlaceCompletionAlgEquiv W).toRingEquiv
  have hDsymm : Isometry eD.symm :=
    AddMonoidHomClass.isometry_of_norm eD.symm
      (relativeFinitePlaceCompletionAlgEquiv_symm_norm W)
  exact
    hDsymm.continuous.comp
      ((finitePlaceAdicCompletionMap_continuous
        K K' v ⟨W, hW⟩).comp
        (relativeFinitePlaceCompletionRingHom_isometry v).continuous)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
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

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] [IsGalois K L]
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] in
/-- Pulling the selected extension valuation on `Kˢᵉᵖ` back along a finite
separable embedding gives the given local valuation on the source field. -/
theorem localSeparableValuationSubring_comap_embedding
    [Algebra.IsSeparable K L] :
    (localSeparableValuationSubring K).comap i.toRingHom =
      (ValuativeRel.valuation L).valuationSubring := by
  let A := localSeparableValuationSubring K
  let B := A.comap i.toRingHom
  let C := (ValuativeRel.valuation L).valuationSubring
  have hBext : (localCompleteDVF K).valuation.HasExtension B.valuation := by
    apply
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change i (algebraMap K L x) ∈ A ↔
      x ∈ (localCompleteDVF K).valuation.valuationSubring
    rw [i.commutes]
    exact localSeparableValuationSubring_pullback K x
  have hCext : (localCompleteDVF K).valuation.HasExtension C.valuation := by
    apply
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
      (localCompleteDVF K).valuation x ≤ 1
    rw [_root_.Valuation.HasExtension.val_map_le_one_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    rfl
  obtain ⟨target, htarget, _hintegral, _hFundamental⟩ :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.exists_integralClosure_standard_fundamental_identity
      (K := K) (L := L) (localCompleteDVF K)
  let : IsScalarTower (localCompleteDVF K).valuationSubring
      target.valuationSubring L :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_isScalarTower_of_hasExtension
      (localCompleteDVF K).valuation target.valuation
  have hB : target.valuation.valuationSubring = B :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.target_valuationSubring_eq_of_finite_separable
      (localCompleteDVF K) target B
  have hC : target.valuation.valuationSubring = C :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.target_valuationSubring_eq_of_finite_separable
      (localCompleteDVF K) target C
  exact hB.symm.trans hC

/-! ## Comparison of unramifiedness -/

/-! ## Frobenius normalization -/

end

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
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

noncomputable def finitePlaceRelativeNormUnits
    {K' : Type}
    [Field K'] [NumberField K'] [Algebra K K']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v) :
    (finitePlaceNormCompletion K' W)ˣ →*
      (finitePlaceNormCompletion K v)ˣ := by
  letI : Algebra
      (finitePlaceNormCompletion K v)
      (finitePlaceNormCompletion K' W) :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  exact LocalFieldTheory.normUnits
    (finitePlaceNormCompletion K v)
    (finitePlaceNormCompletion K' W)

theorem finitePlaceArtinConcreteNormUnits
    {K' : Type}
    [Field K'] [NumberField K'] [Algebra K K']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v)
    (x : (W.adicCompletion K')ˣ) :
      finitePlaceCompletionUnitsContinuousMulEquiv v
        (finitePlaceRelativeNormUnits
          (K := K) (K' := K') v W hW
          ((finitePlaceCompletionUnitsContinuousMulEquiv W).symm x)) =
      finitePlaceConcreteNormUnits
        (K := K) (K' := K') v W hW x := by
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
  let eCUnits :
      Cˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  let eDUnits :
      Dˣ ≃* (W.adicCompletion K')ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv W
  have hCUnits :
      eCUnits = Units.mapEquiv eC.toMulEquiv := by
    change
      Units.mapEquiv
          (finitePlaceCompletionRingEquiv v).toMulEquiv =
        Units.mapEquiv eC.toMulEquiv
    rw [finitePlaceCompletionRingEquiv_eq_relative]
  have hDUnits :
      eDUnits = Units.mapEquiv eD.toMulEquiv := by
    change
      Units.mapEquiv
          (finitePlaceCompletionRingEquiv W).toMulEquiv =
        Units.mapEquiv eD.toMulEquiv
    rw [finitePlaceCompletionRingEquiv_eq_relative]
  let concreteBaseMap :
      v.adicCompletion K →+* W.adicCompletion K' :=
    finitePlaceAdicCompletionMap K K' v ⟨W, hW⟩
  let : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
    concreteBaseMap.toAlgebra
  let : Algebra C D :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  have hBaseMap (y : C) :
      eD (algebraMap C D y) =
        concreteBaseMap (eC y) := by
    change
      eD (eD.symm (concreteBaseMap (eC y))) =
        concreteBaseMap (eC y)
    rw [eD.apply_symm_apply]
  have hBaseCompatible :
      RingHom.comp
          (algebraMap
            (v.adicCompletion K) (W.adicCompletion K'))
          eC =
        RingHom.comp eD (algebraMap C D) := by
    apply RingHom.ext
    intro y
    exact (hBaseMap y).symm
  change
    eCUnits
        (LocalFieldTheory.normUnits C D
          (eDUnits.symm x)) =
      LocalFieldTheory.normUnits
        (v.adicCompletion K) (W.adicCompletion K') x
  rw [hCUnits, hDUnits]
  calc
    Units.mapEquiv eC.toMulEquiv
        (LocalFieldTheory.normUnits C D
          (Units.mapEquiv eD.symm.toMulEquiv x)) =
      LocalFieldTheory.normUnits
        (v.adicCompletion K) (W.adicCompletion K')
        (Units.mapEquiv eD.toMulEquiv
          (Units.mapEquiv eD.symm.toMulEquiv x)) :=
      finitePlaceArtinNormUnits_map_ringEquiv
        eC eD hBaseCompatible
        (Units.mapEquiv eD.symm.toMulEquiv x)
    _ =
      LocalFieldTheory.normUnits
        (v.adicCompletion K) (W.adicCompletion K') x := by
      congr 1
      change
        (Units.mapEquiv eD.toMulEquiv)
            ((Units.mapEquiv eD.toMulEquiv).symm x) = x
      exact (Units.mapEquiv eD.toMulEquiv).apply_symm_apply x

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_Existence_UnramifiedNormSubgroup
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

/-- A reduced valuation vanishes exactly when `n` divides the original valuation. -/
theorem valuationModDegree_eq_zero_iff_dvd (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x : Additive Kˣ) :
    valuationModDegree K n x = 0 ↔
      (n : Int) ∣ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x := by
  rw [valuationModDegree_apply]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd
    (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x) n

/-- The unramified norm subgroup of degree `n`: field units whose normalized
valuation lies in `nℤ`. -/
def unramifiedNormSubgroup (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) : Subgroup Kˣ where
  carrier := {x | (n : Int) ∣
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)}
  one_mem' := by
    change (n : Int) ∣
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul (1 : Kˣ))
    rw [show Additive.ofMul (1 : Kˣ) = 0 by rfl, map_zero]
    exact dvd_zero (n : Int)
  mul_mem' := by
    intro x y hx hy
    change (n : Int) ∣
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul (x * y))
    rw [show Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y by rfl,
      map_add]
    exact dvd_add hx hy
  inv_mem' := by
    intro x hx
    change (n : Int) ∣
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x⁻¹)
    rw [show Additive.ofMul x⁻¹ = -Additive.ofMul x by rfl, map_neg]
    exact dvd_neg.mpr hx

/-- Characterizes the unramified norm subgroup by divisibility of the normalized valuation. -/
theorem mem_unramifiedNormSubgroup_iff (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x : Kˣ) :
    x ∈ unramifiedNormSubgroup K n ↔
      (n : Int) ∣ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) :=
  Iff.rfl

/-- The quotient map from field units to degree-`n` unramified norm classes. -/
def unramifiedNormClass (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) :
    Kˣ →* Kˣ ⧸ unramifiedNormSubgroup K n :=
  QuotientGroup.mk' (unramifiedNormSubgroup K n)


end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instContinuousSMulPadicLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceLocalizedIsGalois
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
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

section AbelianTower

variable [IsAbelianGalois K L]

/-- The norm from a complex archimedean completion to a real completion
is positive under the canonical real coordinate. -/
theorem infinitePlace_normUnits_real_complex_pos
    {K' : Type}
    [Field K'] [NumberField K'] [Algebra K K']
    (v : InfinitePlace K) (W : InfinitePlace K')
    (hW : W.comap (algebraMap K K') = v)
    (hvReal : v.IsReal) (hWComplex : W.IsComplex)
    (x : W.Completionˣ) :
    letI : W.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
    0 <
      InfinitePlace.Completion.ringEquivRealOfIsReal
        hvReal
        (LocalFieldTheory.normUnits
          v.Completion W.Completion x :
            v.Completion) := by
  let : W.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
  let eReal :
      v.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal
      hvReal
  let eComplex :
      W.Completion ≃+* ℂ :=
    InfinitePlace.Completion.ringEquivComplexOfIsComplex
      hWComplex
  let :
      NumberField.ComplexEmbedding.LiesOver
        (InfinitePlace.Completion.extensionEmbedding W)
        (InfinitePlace.Completion.extensionEmbedding v) :=
    InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
      W hvReal
  have hCompatible :
      RingHom.comp (algebraMap ℝ ℂ) eReal =
        RingHom.comp eComplex
          (algebraMap v.Completion W.Completion) := by
    ext z
    simp [eReal, eComplex]
  have hNorm :=
    LocalClassFieldTheory.normUnits_map_ringEquiv
      eReal eComplex hCompatible x
  have hNormVal := congrArg Units.val hNorm
  change
    0 <
      ((Units.mapEquiv eReal.toMulEquiv
        (LocalFieldTheory.normUnits
          v.Completion W.Completion x) : ℝˣ) : ℝ)
  rw [hNormVal]
  change
    0 <
      Algebra.norm ℝ
        (eComplex (x : W.Completion))
  rw [Algebra.norm_complex_apply, Complex.normSq_pos]
  exact (map_ne_zero eComplex).2 (Units.ne_zero x)

/-- The norm between real archimedean completions agrees with the
transported local unit under their canonical real coordinates. -/
theorem infinitePlace_normUnits_real_real
    {K' : Type}
    [Field K'] [NumberField K'] [Algebra K K']
    (v : InfinitePlace K) (W : InfinitePlace K')
    (hW : W.comap (algebraMap K K') = v)
    (hvReal : v.IsReal) (hWReal : W.IsReal)
    (x : W.Completionˣ) :
    letI : W.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
    Units.mapEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal).toMulEquiv
        (LocalFieldTheory.normUnits
          v.Completion W.Completion x) =
      Units.mapEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal
          hWReal).toMulEquiv x := by
  let : W.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
  let eBase :
      v.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal
      hvReal
  let eExtension :
      W.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal
      hWReal
  let :
      NumberField.ComplexEmbedding.LiesOver
        (InfinitePlace.Completion.extensionEmbedding W)
        (InfinitePlace.Completion.extensionEmbedding v) :=
    InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
      W hvReal
  have hCompatible :
      RingHom.comp (algebraMap ℝ ℝ) eBase =
        RingHom.comp eExtension
          (algebraMap v.Completion W.Completion) := by
    ext z
    change
      InfinitePlace.Completion.extensionEmbeddingOfIsReal
          hvReal z =
        InfinitePlace.Completion.extensionEmbeddingOfIsReal
          hWReal ((algebraMap v.Completion W.Completion) z)
    apply Complex.ofReal_injective
    simpa only [
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply] using
      (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
        W (v := v)).symm
  simpa only [
    LocalFieldTheory.normUnits,
    Algebra.norm_self,
    Units.map_id,
    MonoidHom.id_apply
  ] using
    LocalClassFieldTheory.normUnits_map_ringEquiv
      eBase eExtension hCompatible x

omit [NumberField L] in
/-- The archimedean Artin map attached to specified places carries a
local norm to the restriction of the upper Artin element. -/
theorem infinitePlaceArtinMonoidHomOfPlace_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : InfinitePlace K) (W : InfinitePlace K')
    (w' : InfinitePlace L')
    (hW : W.comap (algebraMap K K') = v)
    (hw' : w'.comap (algebraMap K' L') = W) :
    let w := w'.comap (algebraMap L L')
    let hw : w.comap (algebraMap K L) = v := by
      dsimp only [w]
      rw [← InfinitePlace.comap_comp,
        ← IsScalarTower.algebraMap_eq K L L',
        IsScalarTower.algebraMap_eq K K' L',
        InfinitePlace.comap_comp, hw', hW]
    letI : W.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (infinitePlaceArtinMonoidHomOfPlace
          (K := K') (L := L') W w' hw') =
      (infinitePlaceArtinMonoidHomOfPlace
        (K := K) (L := L) v w hw).comp
        (LocalFieldTheory.normUnits
          v.Completion W.Completion) := by
  let w := w'.comap (algebraMap L L')
  have hw :
      w.comap (algebraMap K L) = v := by
    dsimp only [w]
    rw [← InfinitePlace.comap_comp,
      ← IsScalarTower.algebraMap_eq K L L',
      IsScalarTower.algebraMap_eq K K' L',
      InfinitePlace.comap_comp, hw', hW]
  let : W.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hW⟩
  dsimp only
  by_cases hUpperUnramified : w'.IsUnramified K'
  · by_cases hLowerUnramified : w.IsUnramified K
    · have hLowerUnramified' :
          (w'.comap (algebraMap L L')).IsUnramified K := by
        simpa only [w] using hLowerUnramified
      unfold infinitePlaceArtinMonoidHomOfPlace
      rw [dite_eq_left hUpperUnramified, dite_eq_left hLowerUnramified']
      simp
    · have hLowerUnramified' :
          ¬ (w'.comap (algebraMap L L')).IsUnramified K := by
        simpa only [w] using hLowerUnramified
      have hLowerRamified : w.IsRamified K :=
        hLowerUnramified
      have hvReal : v.IsReal := by
        rw [← hw]
        exact hLowerRamified.isReal
      have hw'Complex : w'.IsComplex := by
        rw [← InfinitePlace.not_isReal_iff_isComplex]
        intro hw'Real
        have hwReal : w.IsReal := by
          exact hw'Real.comap (algebraMap L L')
        exact
          (InfinitePlace.not_isComplex_iff_isReal.mpr
            hwReal) hLowerRamified.isComplex
      have hWComplex : W.IsComplex := by
        rcases
            InfinitePlace.isUnramified_iff.mp
              hUpperUnramified with
          hw'Real | hWComplex
        · exact
            (InfinitePlace.not_isReal_iff_isComplex.mpr
              hw'Complex hw'Real).elim
        · simpa only [hw'] using hWComplex
      apply MonoidHom.ext
      intro x
      have hPositive :=
        infinitePlace_normUnits_real_complex_pos
          (K := K) v W hW hvReal hWComplex x
      have hSign :
          LocalClassFieldTheory.realUnitsSign
              (Units.mapEquiv
                (InfinitePlace.Completion.ringEquivRealOfIsReal
                  hvReal).toMulEquiv
                (LocalFieldTheory.normUnits
                  v.Completion W.Completion x)) =
            1 :=
        MonoidHom.mem_ker.mp
          ((LocalClassFieldTheory.mem_realUnitsSign_ker_iff _).2
            hPositive)
      unfold infinitePlaceArtinMonoidHomOfPlace
      rw [dite_eq_left hUpperUnramified, dite_eq_right hLowerUnramified']
      simp only [MonoidHom.comp_apply]
      dsimp
      split_ifs with hsign
      · exact map_one _
      · exact (hsign hSign).elim
  · have hUpperRamified : w'.IsRamified K' :=
      hUpperUnramified
    have hWReal : W.IsReal := by
      rw [← hw']
      exact hUpperRamified.isReal
    have hvReal : v.IsReal := by
      rw [← hW]
      exact hWReal.comap (algebraMap K K')
    let sigmaUpper :=
      ramifiedInfinitePlaceConjugation
        (K := K') w' hUpperRamified
    let sigmaRestricted : L ≃ₐ[K] L :=
      ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)) sigmaUpper
    have hSigmaUpper :=
      ramifiedInfinitePlaceConjugation_isConj
        (K := K') w' hUpperRamified
    let phi : L →+* ℂ :=
      (InfinitePlace.embedding w').comp
        (algebraMap L L')
    have hphi :
        NumberField.ComplexEmbedding.IsConj
          phi sigmaRestricted := by
      apply RingHom.ext
      intro x
      change
        star
            (InfinitePlace.embedding w'
              (algebraMap L L' x)) =
          InfinitePlace.embedding w'
            (algebraMap L L' (sigmaRestricted x))
      rw [show
        algebraMap L L' (sigmaRestricted x) =
          sigmaUpper (algebraMap L L' x) by
          dsimp [sigmaRestricted]
          change
            algebraMap L L'
                ((AlgEquiv.restrictNormal
                  (AlgEquiv.restrictScalars K sigmaUpper) L) x) =
              sigmaUpper (algebraMap L L' x)
          rw [AlgEquiv.restrictNormal_commutes]
          rfl]
      exact (hSigmaUpper.eq (algebraMap L L' x)).symm
    have hmk : InfinitePlace.mk phi = w := by
      change
        InfinitePlace.mk
            ((InfinitePlace.embedding w').comp
              (algebraMap L L')) =
          w'.comap (algebraMap L L')
      conv_rhs => rw [← InfinitePlace.mk_embedding w']
      rw [InfinitePlace.comap_mk]
    have hSign (x : W.Completionˣ) :
        LocalClassFieldTheory.realUnitsSign
            (Units.mapEquiv
              (InfinitePlace.Completion.ringEquivRealOfIsReal
                hWReal).toMulEquiv x) =
          LocalClassFieldTheory.realUnitsSign
            (Units.mapEquiv
              (InfinitePlace.Completion.ringEquivRealOfIsReal
                hvReal).toMulEquiv
              (LocalFieldTheory.normUnits
                v.Completion W.Completion x)) := by
      rw [infinitePlace_normUnits_real_real
        (K := K) v W hW hvReal hWReal x]
    by_cases hLowerUnramified : w.IsUnramified K
    · have hLowerUnramified' :
          (w'.comap (algebraMap L L')).IsUnramified K := by
        simpa only [w] using hLowerUnramified
      have hSigmaRestricted : sigmaRestricted = 1 :=
        hphi.isUnramified_mk_iff.mp
          (hmk.symm ▸ hLowerUnramified)
      apply MonoidHom.ext
      intro x
      unfold infinitePlaceArtinMonoidHomOfPlace
      rw [dite_eq_right hUpperUnramified, dite_eq_left hLowerUnramified']
      simp only [MonoidHom.comp_apply]
      dsimp
      split_ifs with hsign
      · change
          ((AlgEquiv.restrictNormalHom L).comp
            (AlgEquiv.restrictScalarsHom K)) 1 =
            1
        exact map_one _
      · simpa [sigmaRestricted, sigmaUpper] using hSigmaRestricted
    · have hLowerUnramified' :
          ¬ (w'.comap (algebraMap L L')).IsUnramified K := by
        simpa only [w] using hLowerUnramified
      have hLowerRamified : w.IsRamified K :=
        hLowerUnramified
      let sigmaLower :=
        ramifiedInfinitePlaceConjugation
          (K := K) w hLowerRamified
      have hSigmaLower :=
        ramifiedInfinitePlaceConjugation_isConj
          (K := K) w hLowerRamified
      have hSigmaRestrictedNe :
          sigmaRestricted ≠ 1 := by
        intro hSigmaRestricted
        have :
            (InfinitePlace.mk phi).IsUnramified K :=
          hphi.isUnramified_mk_iff.mpr
            hSigmaRestricted
        exact hLowerUnramified (hmk ▸ this)
      have hSigmaRestrictedMem :
          sigmaRestricted ∈
            MulAction.stabilizer
              (L ≃ₐ[K] L) w := by
        rw [← hmk,
          InfinitePlace.mem_stabilizer_mk_iff]
        exact Or.inr hphi
      have hSigmaRestrictedAtW :
          NumberField.ComplexEmbedding.IsConj
            (InfinitePlace.embedding w)
            sigmaRestricted := by
        rw [← InfinitePlace.mk_embedding w,
          InfinitePlace.mem_stabilizer_mk_iff] at hSigmaRestrictedMem
        exact
          hSigmaRestrictedMem.resolve_left
            hSigmaRestrictedNe
      have hSigmaEq :
          sigmaRestricted = sigmaLower :=
        hSigmaRestrictedAtW.ext hSigmaLower
      apply MonoidHom.ext
      intro x
      unfold infinitePlaceArtinMonoidHomOfPlace
      rw [dite_eq_right hUpperUnramified, dite_eq_right hLowerUnramified']
      simp only [MonoidHom.comp_apply]
      dsimp
      split_ifs with hsignUpper hsignLower hsignLower
      · exact map_one _
      · exact (hsignLower ((hSign x).symm.trans hsignUpper)).elim
      · exact (hsignUpper ((hSign x).trans hsignLower)).elim
      · simpa [sigmaRestricted, sigmaUpper, sigmaLower] using hSigmaEq

end AbelianTower

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_PrimitiveUniformizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHom_apply_ofAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_mul_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeries_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_expSeries_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_one_ofWithZeroValuation _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Uniformizers in standard Lubin--Tate level fields

Let `F` be a local field, let `π` be a chosen uniformizer, and let
`Lₙ = K(λₙ)` be the simple extension generated by a chosen root of the
standard primitive division polynomial.  This file puts the integral-closure
complete discrete valuation on `Lₙ` and proves that `λₙ` is a uniformizer.

The valuation calculation uses the actual Eisenstein polynomial.  Its
constant coefficient has target additive valuation equal to the ramification
index, while every nonconstant lower term lies one step deeper in the target
maximal-ideal filtration.  Comparing with the leading term and the
fundamental identity forces the normalized additive valuation of `λₙ` to be
one.
-/

noncomputable section

open scoped Polynomial

universe u v w x

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} [Field K]

attribute [local instance] LubinTate.standardLubinTateLevelField_finiteDimensionalInstance
attribute [local instance] LubinTate.standardLubinTateLevelField_isSeparableInstance
attribute [local instance] LubinTate.standardLubinTateLevelValuationSubring_isScalarTower
/-- The image of any base-field uniformizer in a standard finite level has
additive valuation equal to the degree of that level.  The uniformizer used
here need not be the parameter defining the Lubin--Tate level. -/
theorem standardLubinTateUniformizerInteger_map_addVal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {ϖ : F.valuationSubring}
    (hϖ : F.toCompleteDVF.valuation.IsUniformizer (ϖ : K))
    (n : ℕ) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (integerMap F.toCompleteDVF.toDVF
          (standardLubinTateLevelCompleteDVF hπ n).toDVF ϖ) =
      (((Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n : ℕ) : ℕ∞) := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hϖIrreducible : Irreducible ϖ := by
    exact
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).2
        (F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hϖ)
  have hdegree :
      degree F.toCompleteDVF.toDVF target.toDVF =
        (Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n := by
    simpa [target, degree] using
      standardLubinTateLevelField_finrank hπ n
  calc
    IsDiscreteValuationRing.addVal target.valuationSubring
        (integerMap F.toCompleteDVF.toDVF target.toDVF ϖ) =
        (ramificationIndex F.toCompleteDVF.toDVF target.toDVF : ℕ∞) :=
      addVal_integerMap_eq_ramificationIndex_of_irreducible
        F.toCompleteDVF target
        hϖIrreducible
    _ = (degree F.toCompleteDVF.toDVF target.toDVF : ℕ∞) := by
      rw [standardLubinTateLevel_ramificationIndex_eq_degree hπ n]
    _ = (((Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n : ℕ) : ℕ∞) := by
      exact_mod_cast hdegree

/-- The image of the parameter uniformizer has additive valuation equal to
the standard finite-level degree. -/
theorem standardLubinTateBaseUniformizerInteger_map_addVal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    IsDiscreteValuationRing.addVal
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
        (integerMap F.toCompleteDVF.toDVF
          (standardLubinTateLevelCompleteDVF hπ n).toDVF π) =
      (((Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n : ℕ) : ℕ∞) :=
  standardLubinTateUniformizerInteger_map_addVal hπ hπ n

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_NormSubgroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHom_apply_ofAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_mul_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeries_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_expSeries_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.coe_fieldNormUnitsQuotientKerEquivFieldNormSubgroup_mk _root_.LocalFieldTheory.DiscreteValuationField.fieldNormFiltrationQuotientMap_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.fieldNormFiltrationQuotientMap_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.fieldNormMapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.fieldNormUnitsQuotientKerEquivFieldNormSubgroup_mk _root_.LocalFieldTheory.DiscreteValuationField.fieldNormUnits_algebraMap _root_.LocalFieldTheory.DiscreteValuationField.mem_fieldNormFiltrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.valuedFieldNorm_toHom _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The norm subgroup of a standard Lubin--Tate level

This file introduces the local norm subgroup attached to a standard finite
Lubin--Tate level.  The norm identity for the negative primitive generator
shows that the chosen base uniformizer is an actual norm.  Consequently its
entire cyclic subgroup of integral powers lies in the norm subgroup.

The higher-principal-unit contribution is intentionally left to the later
norm calculation.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The chosen base uniformizer is an actual norm from every standard
finite level. -/
theorem standardLubinTateBaseUniformizerUnit_mem_normSubgroup
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateBaseUniformizerUnit hπ ∈
      standardLubinTateNormSubgroup hπ n := by
  let : FiniteDimensional K (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let y : (standardLubinTateLevelField hπ n)ˣ :=
    Units.mk0 (-standardLubinTateLevelGenerator hπ n)
      (neg_ne_zero.mpr (by
        intro hzero
        apply chosenStandardLubinTatePrimitiveRoot_ne_zero hπ n
        simpa using congrArg Subtype.val hzero))
  have hyNorm :
      LocalFieldTheory.normUnits K
          (standardLubinTateLevelField hπ n) y =
        standardLubinTateBaseUniformizerUnit hπ := by
    apply Units.ext
    exact standardLubinTate_norm_neg_levelGenerator hπ n
  have hyMem :
      LocalFieldTheory.normUnits K
          (standardLubinTateLevelField hπ n) y ∈
        LocalFieldTheory.localNormSubgroup K
          (standardLubinTateLevelField hπ n) :=
    ⟨y, rfl⟩
  rw [hyNorm] at hyMem
  exact hyMem

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_StandardFormalGroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHom_apply_ofAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_mul_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeries_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_expSeries_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_one_ofWithZeroValuation _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The standard Lubin--Tate formal group

The recursive same-uniformizer intertwiner applied to the standard
Lubin--Tate series produces the formal group law and all of its scalar
endomorphisms.  The structural identities are proved from the uniqueness of
an intertwiner with prescribed linear term.

This file also records the substitution closure properties of
`SameUniformizer.Intertwines`.  They are useful independently of the
standard series: intertwiners remain intertwiners after a change of
variables, after substituting an intertwining family, and after
one-variable power-series composition.
-/

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u v w w'

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

section LinearTerms

variable {R : Type*} [CommRing R]
variable {σ : Type w} [Fintype σ]
variable {τ : Type w'} [Fintype τ]

/-- A variable has the corresponding standard-basis linear term. -/
theorem hasLinearTerm_X (i : σ) :
    HasLinearTerm (MvPowerSeries.X i : MvPowerSeries σ R)
      (fun j => if j = i then (1 : R) else 0) := by
  rw [HasLinearTerm, linearForm_basis i, sub_self]
  simp

end LinearTerms

section StandardFormalGroup

variable (hπ :
  F.toCompleteDVF.valuation.IsUniformizer (π : K))

/-- The standard formal-group series has linear term `X + Y`. -/
theorem standardFormalGroupPowerSeries_hasLinearTerm :
    HasLinearTerm (standardFormalGroupPowerSeries hπ)
      (fun _ : Fin 2 => 1) :=
  recursiveIntertwiner_hasLinearTerm hπ
    (standardSeries hπ) (standardSeries hπ) (fun _ => 1)

/-- The standard formal-group series commutes with the standard
Lubin--Tate series. -/
theorem standardFormalGroupPowerSeries_intertwines :
    Intertwines (standardSeries hπ) (standardSeries hπ)
      (standardFormalGroupPowerSeries hπ) :=
  recursiveIntertwiner_intertwines hπ
    (standardSeries hπ) (standardSeries hπ) (fun _ => 1)

theorem standardFormalGroupPowerSeries_subst_hasLinearTerm
    {τ : Type w} [Fintype τ]
    {G₀ G₁ : MvPowerSeries τ F.valuationSubring}
    {M₀ M₁ : τ → F.valuationSubring}
    (hG₀ : HasLinearTerm G₀ M₀)
    (hG₁ : HasLinearTerm G₁ M₁) :
    HasLinearTerm
      (MvPowerSeries.subst ![G₀, G₁]
        (standardFormalGroupPowerSeries hπ))
      (fun j => M₀ j + M₁ j) := by
  have h :=
    (standardFormalGroupPowerSeries_hasLinearTerm hπ).subst
      (G := ![G₀, G₁]) (M := ![M₀, M₁])
      (by
        intro i
        fin_cases i
        · exact hG₀
        · exact hG₁)
  simpa [Fin.sum_univ_two] using h

theorem standardFormalGroupPowerSeries_subst_intertwines
    {τ : Type w} [Fintype τ]
    {G₀ G₁ : MvPowerSeries τ F.valuationSubring}
    {M₀ M₁ : τ → F.valuationSubring}
    (hG₀ : HasLinearTerm G₀ M₀)
    (hG₁ : HasLinearTerm G₁ M₁)
    (hI₀ : Intertwines (standardSeries hπ)
      (standardSeries hπ) G₀)
    (hI₁ : Intertwines (standardSeries hπ)
      (standardSeries hπ) G₁) :
    Intertwines (standardSeries hπ) (standardSeries hπ)
      (MvPowerSeries.subst ![G₀, G₁]
        (standardFormalGroupPowerSeries hπ)) := by
  apply
    (standardFormalGroupPowerSeries_intertwines hπ).subst
      (standardFormalGroupPowerSeries_hasLinearTerm hπ).hasSubst
      (MvPowerSeries.hasSubst_of_constantCoeff_zero
        (fun i => by
          fin_cases i
          · exact hG₀.constantCoeff_eq_zero
          · exact hG₁.constantCoeff_eq_zero))
  intro i
  fin_cases i
  · exact hI₀
  · exact hI₁

/-- The left identity law, proved by uniqueness of the linear-term-one
intertwiner. -/
theorem standardFormalGroupPowerSeries_subst_X_zero :
    MvPowerSeries.subst
        ![(MvPowerSeries.X () :
            PowerSeries F.valuationSubring), 0]
        (standardFormalGroupPowerSeries hπ) =
      (MvPowerSeries.X () :
        PowerSeries F.valuationSubring) := by
  have hX :
      HasLinearTerm
        (MvPowerSeries.X () :
          PowerSeries F.valuationSubring)
        (fun _ : Unit => 1) := by
    simpa using
      (hasLinearTerm_X (R := F.valuationSubring) ())
  have hzero :
      HasLinearTerm
        (0 : PowerSeries F.valuationSubring)
        (fun _ : Unit => 0) :=
    hasLinearTerm_zero
  have hleft :=
    standardFormalGroupPowerSeries_subst_hasLinearTerm
      hπ hX hzero
  have hleft' :
      HasLinearTerm
        (MvPowerSeries.subst
          ![(MvPowerSeries.X () :
              PowerSeries F.valuationSubring), 0]
          (standardFormalGroupPowerSeries hπ))
        (fun _ : Unit => 1) := by
    simpa using hleft
  have hIleft :=
    standardFormalGroupPowerSeries_subst_intertwines
      hπ hX hzero
        (intertwines_X (standardSeries hπ) ())
        (intertwines_zero
          (standardSeries hπ) (standardSeries hπ))
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardSeries hπ) (standardSeries hπ)
      (fun _ : Unit => 1)
      hleft' hIleft hX
      (intertwines_X (standardSeries hπ) ())

end StandardFormalGroup

section StandardEndomorphisms

variable (hπ :
  F.toCompleteDVF.valuation.IsUniformizer (π : K))

/-- The scalar `1` acts by the identity series. -/
theorem standardLubinTateEndomorphism_one :
    standardLubinTateEndomorphism hπ 1 =
      PowerSeries.X := by
  have hX :
      HasLinearTerm
        (PowerSeries.X :
          PowerSeries F.valuationSubring)
        (fun _ : Unit => 1) := by
    simpa [PowerSeries.X] using
      (hasLinearTerm_X (R := F.valuationSubring) ())
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardSeries' hπ) (standardSeries' hπ)
      (fun _ : Unit => 1)
      (standardLubinTateEndomorphism_hasLinearTerm hπ 1)
      (standardLubinTateEndomorphism_intertwines hπ 1)
      hX (intertwines_X (standardSeries' hπ) ())

/-- The scalar `0` acts by the zero series. -/
theorem standardLubinTateEndomorphism_zero :
    standardLubinTateEndomorphism hπ 0 = 0 := by
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardSeries' hπ) (standardSeries' hπ)
      (fun _ : Unit => 0)
      (standardLubinTateEndomorphism_hasLinearTerm hπ 0)
      (standardLubinTateEndomorphism_intertwines hπ 0)
      hasLinearTerm_zero
      (intertwines_zero
        (standardSeries' hπ) (standardSeries' hπ))

/-- Addition of scalars is addition in the standard formal group. -/
theorem standardLubinTateEndomorphism_add
    (a b : F.valuationSubring) :
    standardLubinTateEndomorphism hπ (a + b) =
      MvPowerSeries.subst
        ![
          standardLubinTateEndomorphism hπ a,
          standardLubinTateEndomorphism hπ b]
        (standardFormalGroupPowerSeries hπ) := by
  have hright :=
    standardFormalGroupPowerSeries_subst_hasLinearTerm
      hπ
      (standardLubinTateEndomorphism_hasLinearTerm hπ a)
      (standardLubinTateEndomorphism_hasLinearTerm hπ b)
  have hright' :
      HasLinearTerm
        (MvPowerSeries.subst
          ![
            standardLubinTateEndomorphism hπ a,
            standardLubinTateEndomorphism hπ b]
          (standardFormalGroupPowerSeries hπ))
        (fun _ : Unit => a + b) := by
    simpa using hright
  have hIright :=
    standardFormalGroupPowerSeries_subst_intertwines
      hπ
      (standardLubinTateEndomorphism_hasLinearTerm hπ a)
      (standardLubinTateEndomorphism_hasLinearTerm hπ b)
      (standardLubinTateEndomorphism_intertwines hπ a)
      (standardLubinTateEndomorphism_intertwines hπ b)
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardSeries' hπ) (standardSeries' hπ)
      (fun _ : Unit => a + b)
      (standardLubinTateEndomorphism_hasLinearTerm hπ (a + b))
      (standardLubinTateEndomorphism_intertwines hπ (a + b))
      hright' hIright

end StandardEndomorphisms

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_CompletedEvaluation
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHom_apply_ofAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_mul_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeries_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_expSeries_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_one_ofWithZeroValuation _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Analytic evaluation in standard Lubin--Tate level fields

The scalar endomorphisms of a Lubin--Tate formal module are genuine infinite
power series.  This file evaluates them in the complete valuation ring of a
standard finite level.

The coefficient map is the canonical map of valuation rings attached to the
valued extension.  The target carries its maximal-ideal adic topology.  The
chosen primitive division point is a uniformizer, hence is topologically
nilpotent and is therefore a valid evaluation point.
-/

noncomputable section

open Filter
open scoped PowerSeries
open scoped PowerSeries.WithPiTopology

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open SameUniformizer

variable {K : Type u} [Field K]

attribute [local instance 50] LubinTate.standardLubinTateLevelCoefficientUniformSpace
attribute [local instance] LubinTate.standardLubinTateLevelTargetWithIdeal
  LubinTate.standardLubinTateLevelTargetCompleteSpace LubinTate.standardLubinTateLevelTargetT2Space

/-- The value of `[1]` is the evaluation point. -/
@[simp]
theorem standardLubinTateEndomorphismEvalAt_one
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    standardLubinTateEndomorphismEvalAt hπ n x hx 1 = x := by
  rw [standardLubinTateEndomorphismEvalAt,
    standardLubinTateEndomorphism_one,
    standardLubinTateLevelPowerSeriesEval_X]

/-- The value of `[0]` is zero. -/
@[simp]
theorem standardLubinTateEndomorphismEvalAt_zero
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    standardLubinTateEndomorphismEvalAt hπ n x hx 0 = 0 := by
  rw [standardLubinTateEndomorphismEvalAt,
    standardLubinTateEndomorphism_zero, map_zero]

/-- Multiplication of scalars becomes composition after analytic
evaluation. -/
theorem standardLubinTateEndomorphismEvalAt_mul
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (a b : F.valuationSubring) :
    standardLubinTateEndomorphismEvalAt hπ n x hx (a * b) =
      standardLubinTateEndomorphismEvalAt hπ n
        (standardLubinTateEndomorphismEvalAt hπ n x hx b)
        (standardLubinTateEndomorphismEvalAt_hasEval hπ n x hx b) a := by
  rw [standardLubinTateEndomorphismEvalAt,
    standardLubinTateEndomorphism_mul]
  exact standardLubinTateLevelPowerSeriesEval_subst hπ n x hx
    (standardLubinTateEndomorphism hπ b)
    (standardLubinTateEndomorphism hπ a)
    (standardLubinTateEndomorphism_hasLinearTerm hπ b).hasSubst
    (standardLubinTateEndomorphismEvalAt_hasEval hπ n x hx b)

/-- At the primitive point, multiplication of scalars is analytic
composition of their values. -/
theorem standardLubinTateEndomorphismValue_mul
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a b : F.valuationSubring) :
    standardLubinTateEndomorphismValue hπ n (a * b) =
      standardLubinTateEndomorphismEvalAt hπ n
        (standardLubinTateEndomorphismValue hπ n b)
        (standardLubinTateEndomorphismValue_hasEval hπ n b) a :=
  standardLubinTateEndomorphismEvalAt_mul hπ n
    (standardLubinTatePrimitivePointInteger hπ n)
    (standardLubinTatePrimitivePointInteger_hasEval hπ n) a b

/-- The primitive-point value of `[1]` is the primitive point itself. -/
@[simp]
theorem standardLubinTateEndomorphismValue_one
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTateEndomorphismValue hπ n 1 =
      standardLubinTatePrimitivePointInteger hπ n :=
  standardLubinTateEndomorphismEvalAt_one hπ n
    (standardLubinTatePrimitivePointInteger hπ n)
    (standardLubinTatePrimitivePointInteger_hasEval hπ n)

/-- The primitive-point value of `[0]` is zero. -/
@[simp]
theorem standardLubinTateEndomorphismValue_zero
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTateEndomorphismValue hπ n 0 = 0 :=
  standardLubinTateEndomorphismEvalAt_zero hπ n
    (standardLubinTatePrimitivePointInteger hπ n)
    (standardLubinTatePrimitivePointInteger_hasEval hπ n)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_PrimitiveAction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHom_apply_ofAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_mul_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeries_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_expSeries_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_one_ofWithZeroValuation _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The standard Lubin--Tate action on primitive division points

The formal scalar endomorphism `[a]` is in general an infinite power
series.  It is therefore evaluated on the primitive point only after that
point has been placed in the complete integral closure constructed in
`PrimitiveUniformizer`.  Unit scalars preserve the exact torsion level, so
their analytic values are again roots of the primitive division
polynomial.

The action is faithful precisely modulo the higher principal-unit subgroup
`U^(n + 1)`.  This is the finite-level congruence needed to descend the
action from valuation-ring units to the standard finite unit parameters.
-/

noncomputable section

open scoped Polynomial PowerSeries

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open ValuationTheory.DiscreteValuationField

variable {K : Type u} [Field K]

namespace SameUniformizer

variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- The standard Lubin--Tate series itself has the prescribed linear term
`π X`. -/
theorem standardLubinTateSeries_hasLinearTerm
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    HasLinearTerm (standardLubinTateSeries hπ).toPowerSeries
      (fun _ : Unit => π) := by
  have hlinear :
      (standardLubinTateSeries hπ).toPowerSeries -
          linearForm (fun _ : Unit => π) =
        (PowerSeries.X : PowerSeries F.valuationSubring) ^
          Nat.card F.residueField := by
    simp [LubinTateSeries.standardLubinTateSeries_toPowerSeries,
      standardLubinTatePowerSeries, linearForm]
    rw [PowerSeries.C_apply, PowerSeries.X_apply]
    ring
  rw [HasLinearTerm, hlinear, ← PowerSeries.order_eq_order,
    PowerSeries.order_X_pow]
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- The scalar endomorphism attached to the uniformizer is the defining
standard Lubin--Tate series. -/
theorem standardLubinTateEndomorphism_uniformizer
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    standardLubinTateEndomorphism hπ π =
      (standardLubinTateSeries hπ).toPowerSeries := by
  apply
    eq_of_hasLinearTerm_of_intertwines hπ
      (standardLubinTateSeries hπ) (standardLubinTateSeries hπ)
      (fun _ : Unit => π)
      (standardLubinTateEndomorphism_hasLinearTerm hπ π)
      (standardLubinTateEndomorphism_intertwines hπ π)
      (standardLubinTateSeries_hasLinearTerm hπ)
  rw [Intertwines]
  change
    MvPowerSeries.subst
        (fun _ : Unit =>
          (standardLubinTateSeries hπ).toPowerSeries)
        (standardLubinTateSeries hπ).toPowerSeries =
      MvPowerSeries.subst
        (fun i : Unit =>
          inVariable (standardLubinTateSeries hπ) i)
        (standardLubinTateSeries hπ).toPowerSeries
  congr 1
  funext i
  cases i
  exact
    (PowerSeries.X_subst
      (standardLubinTateSeries hπ).toPowerSeries).symm

end SameUniformizer

section AnalyticAction

variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

noncomputable local instance
    standardLubinTatePrimitiveActionCoefficientUniformSpace :
    UniformSpace F.valuationSubring :=
  ⊥

noncomputable local instance
    standardLubinTatePrimitiveActionTargetWithIdeal
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    WithIdeal
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring where
  i := (standardLubinTateLevelCompleteDVF hπ n).maximalIdeal

noncomputable local instance
    standardLubinTatePrimitiveActionTargetCompleteSpace
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    CompleteSpace
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

noncomputable local instance
    standardLubinTatePrimitiveActionTargetT2Space
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    T2Space
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

noncomputable local instance
    standardLubinTatePrimitiveActionAlgebra
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Algebra F.valuationSubring
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  (standardLubinTateLevelCoefficientHom hπ n).toAlgebra

/-- Analytic addition in the standard formal group on the integer ring of a
finite level. -/
noncomputable def standardLubinTateFormalAdd
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x y :
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  MvPowerSeries.eval₂
    (standardLubinTateLevelCoefficientHom hπ n) ![x, y]
    (SameUniformizer.standardFormalGroupPowerSeries hπ)

/-- Analytic evaluation of scalar addition is addition in the standard
formal group. -/
theorem standardLubinTateEndomorphismEvalAt_add
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (a b : F.valuationSubring) :
    standardLubinTateEndomorphismEvalAt hπ n x hx (a + b) =
      standardLubinTateFormalAdd hπ n
        (standardLubinTateEndomorphismEvalAt hπ n x hx a)
        (standardLubinTateEndomorphismEvalAt hπ n x hx b) := by
  let ea := SameUniformizer.standardLubinTateEndomorphism hπ a
  let eb := SameUniformizer.standardLubinTateEndomorphism hπ b
  have hea0 : PowerSeries.constantCoeff ea = 0 :=
    (SameUniformizer.standardLubinTateEndomorphism_hasLinearTerm
      hπ a).constantCoeff_eq_zero
  have heb0 : PowerSeries.constantCoeff eb = 0 :=
    (SameUniformizer.standardLubinTateEndomorphism_hasLinearTerm
      hπ b).constantCoeff_eq_zero
  have hab :
      MvPowerSeries.HasSubst (![ea, eb] :
        Fin 2 → PowerSeries F.valuationSubring) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun i => by
        fin_cases i
        · exact hea0
        · exact heb0)
  rw [standardLubinTateEndomorphismEvalAt,
    SameUniformizer.standardLubinTateEndomorphism_add]
  simp only [standardLubinTateFormalAdd,
    standardLubinTateLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom]
  have hcoeff :
      algebraMap F.valuationSubring
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring =
        standardLubinTateLevelCoefficientHom hπ n := by
    rfl
  have hsubst :=
    MvPowerSeries.eval₂_subst
      (R := F.valuationSubring) (S := F.valuationSubring)
      (T :=
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
      (a := (![ea, eb] :
        Fin 2 → PowerSeries F.valuationSubring))
      hab (b := fun _ : Unit => x) (PowerSeries.hasEval hx)
      (SameUniformizer.standardFormalGroupPowerSeries hπ)
  rw [hcoeff] at hsubst
  have hvalues :
      (fun s : Fin 2 =>
        MvPowerSeries.eval₂
          (standardLubinTateLevelCoefficientHom hπ n)
          (fun _ : Unit => x) (![ea, eb] s)) =
        ![
          MvPowerSeries.eval₂
            (standardLubinTateLevelCoefficientHom hπ n)
            (fun _ : Unit => x) ea,
          MvPowerSeries.eval₂
            (standardLubinTateLevelCoefficientHom hπ n)
            (fun _ : Unit => x) eb] := by
    funext s
    fin_cases s <;> rfl
  rw [hvalues] at hsubst
  simpa only [ea, eb, standardLubinTateEndomorphismEvalAt,
    standardLubinTateLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂,
    Function.const_apply] using hsubst

/-- At the primitive point, addition of scalars is analytic formal-group
addition of their values. -/
theorem standardLubinTateEndomorphismValue_add
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (a b : F.valuationSubring) :
    standardLubinTateEndomorphismValue hπ n (a + b) =
      standardLubinTateFormalAdd hπ n
        (standardLubinTateEndomorphismValue hπ n a)
        (standardLubinTateEndomorphismValue hπ n b) :=
  standardLubinTateEndomorphismEvalAt_add hπ n
    (standardLubinTatePrimitivePointInteger hπ n)
    (standardLubinTatePrimitivePointInteger_hasEval hπ n) a b

theorem standardLubinTateEndomorphismEvalAt_eq_of_point_eq
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x y : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy : x = y) (a : F.valuationSubring) :
    standardLubinTateEndomorphismEvalAt hπ n x hx a =
      standardLubinTateEndomorphismEvalAt hπ n y hy a := by
  subst y
  rfl

/-- Every standard scalar endomorphism fixes the zero point. -/
theorem standardLubinTateEndomorphismEvalAt_zero_point
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (a : F.valuationSubring) :
    standardLubinTateEndomorphismEvalAt hπ n 0
        PowerSeries.HasEval.zero a = 0 := by
  have h :=
    standardLubinTateEndomorphismEvalAt_mul hπ n 0
      PowerSeries.HasEval.zero a 0
  simpa using h.symm

/-- A unit scalar acts injectively on the topologically nilpotent elements
of a finite-level integer ring. -/
theorem standardLubinTateEndomorphismEvalAt_unit_injective
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ)
    {x y : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy :
      standardLubinTateEndomorphismEvalAt hπ n x hx
          (u : F.valuationSubring) =
        standardLubinTateEndomorphismEvalAt hπ n y hy
          (u : F.valuationSubring)) :
    x = y := by
  let ux :=
    standardLubinTateEndomorphismEvalAt hπ n x hx
      (u : F.valuationSubring)
  let uy :=
    standardLubinTateEndomorphismEvalAt hπ n y hy
      (u : F.valuationSubring)
  let hux : PowerSeries.HasEval ux :=
    standardLubinTateEndomorphismEvalAt_hasEval hπ n x hx
      (u : F.valuationSubring)
  let huy : PowerSeries.HasEval uy :=
    standardLubinTateEndomorphismEvalAt_hasEval hπ n y hy
      (u : F.valuationSubring)
  calc
    x =
        standardLubinTateEndomorphismEvalAt hπ n x hx
          (((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
            (u : F.valuationSubring)) := by simp
    _ =
        standardLubinTateEndomorphismEvalAt hπ n ux hux
          ((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring) :=
      standardLubinTateEndomorphismEvalAt_mul hπ n x hx
        ((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring)
        (u : F.valuationSubring)
    _ =
        standardLubinTateEndomorphismEvalAt hπ n uy huy
          ((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring) := by
      apply
        standardLubinTateEndomorphismEvalAt_eq_of_point_eq
          hπ n ux uy hux huy
      exact hxy
    _ =
        standardLubinTateEndomorphismEvalAt hπ n y hy
          (((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
            (u : F.valuationSubring)) :=
      (standardLubinTateEndomorphismEvalAt_mul hπ n y hy
        ((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring)
        (u : F.valuationSubring)).symm
    _ = y := by simp

/-- Evaluating `[π ^ r]` is the same as evaluating the `r`-fold standard
division-polynomial iterate. -/
theorem standardLubinTateEndomorphismEvalAt_uniformizer_pow
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (r : ℕ) :
    standardLubinTateEndomorphismEvalAt hπ n x hx (π ^ r) =
      Polynomial.eval₂
        (standardLubinTateLevelCoefficientHom hπ n) x
        (standardLubinTatePolynomialIterate F π r) := by
  induction r with
  | zero =>
      simp [standardLubinTatePolynomialIterate_zero]
  | succ r ih =>
      rw [pow_succ',
        standardLubinTateEndomorphismEvalAt_mul]
      rw [standardLubinTateEndomorphismEvalAt,
        SameUniformizer.standardLubinTateEndomorphism_uniformizer,
        ← standardLubinTatePolynomial_toPowerSeries_eq_series hπ,
        standardLubinTateLevelPowerSeriesEval_coe, ih,
        standardLubinTatePolynomialIterate_succ,
        Polynomial.eval₂_comp]

/-- A valuation-ring unit acts on the chosen primitive point by analytic
evaluation of its standard scalar endomorphism. -/
noncomputable def standardLubinTatePrimitivePointIntegerAction
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  standardLubinTateEndomorphismValue hπ n
    (u : F.valuationSubring)

/-- A unit translate of the primitive point is still topologically
nilpotent. -/
theorem standardLubinTatePrimitivePointIntegerAction_hasEval
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    PowerSeries.HasEval
      (standardLubinTatePrimitivePointIntegerAction hπ n u) :=
  standardLubinTateEndomorphismValue_hasEval hπ n
    (u : F.valuationSubring)

/-- The unit `1` fixes the chosen primitive point. -/
@[simp]
theorem standardLubinTatePrimitivePointIntegerAction_one
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTatePrimitivePointIntegerAction hπ n 1 =
      standardLubinTatePrimitivePointInteger hπ n := by
  simp [standardLubinTatePrimitivePointIntegerAction]

/-- Multiplication of unit parameters is composition of their analytic
actions. -/
theorem standardLubinTatePrimitivePointIntegerAction_mul
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u w : F.valuationSubringˣ) :
    standardLubinTatePrimitivePointIntegerAction hπ n (u * w) =
      standardLubinTateEndomorphismEvalAt hπ n
        (standardLubinTatePrimitivePointIntegerAction hπ n w)
        (standardLubinTatePrimitivePointIntegerAction_hasEval hπ n w)
        (u : F.valuationSubring) := by
  simpa [standardLubinTatePrimitivePointIntegerAction] using
    standardLubinTateEndomorphismValue_mul hπ n
      (u : F.valuationSubring) (w : F.valuationSubring)

/-- The primitive level-`n + 1` point has exact scalar annihilator
`m^(n + 1)`. -/
theorem standardLubinTateEndomorphismValue_eq_zero_iff_mem_maximalIdeal_pow
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (a : F.valuationSubring) :
    standardLubinTateEndomorphismValue hπ n a = 0 ↔
      a ∈ F.toCompleteDVF.maximalIdeal ^ (n + 1) := by
  let lambda := standardLubinTatePrimitivePointInteger hπ n
  let hlambda := standardLubinTatePrimitivePointInteger_hasEval hπ n
  constructor
  · intro haZero
    by_cases ha : a = 0
    · subst a
      exact (F.toCompleteDVF.maximalIdeal ^ (n + 1)).zero_mem
    have hπirr : Irreducible π :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2
        (F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ)
    obtain ⟨r, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπirr
    let z :=
      standardLubinTateEndomorphismEvalAt hπ n lambda hlambda
        (π ^ r)
    let hz : PowerSeries.HasEval z :=
      standardLubinTateEndomorphismEvalAt_hasEval hπ n
        lambda hlambda (π ^ r)
    have huzero :
        standardLubinTateEndomorphismEvalAt hπ n z hz
            (u : F.valuationSubring) = 0 := by
      calc
        standardLubinTateEndomorphismEvalAt hπ n z hz
            (u : F.valuationSubring) =
            standardLubinTateEndomorphismValue hπ n
              ((u : F.valuationSubring) * π ^ r) := by
          exact
            (standardLubinTateEndomorphismEvalAt_mul hπ n
              lambda hlambda (u : F.valuationSubring) (π ^ r)).symm
        _ = standardLubinTateEndomorphismValue hπ n a := by
          rw [hu]
        _ = 0 := haZero
    have hzZero : z = 0 := by
      apply
        standardLubinTateEndomorphismEvalAt_unit_injective
          hπ n u hz PowerSeries.HasEval.zero
      rw [huzero,
        standardLubinTateEndomorphismEvalAt_zero_point]
    have hnr : n + 1 ≤ r := by
      by_contra hnot
      have hrn : r ≤ n := by omega
      have hne :=
        standardLubinTatePrimitivePointInteger_iterate_ne_zero_of_le
          hπ n hrn
      apply hne
      change
        Polynomial.eval₂
            (standardLubinTateLevelCoefficientHom hπ n) lambda
            (standardLubinTatePolynomialIterate F π r) = 0
      calc
        _ =
            standardLubinTateEndomorphismEvalAt hπ n lambda hlambda
              (π ^ r) :=
          (standardLubinTateEndomorphismEvalAt_uniformizer_pow
            hπ n lambda hlambda r).symm
        _ = 0 := by simpa [z] using hzZero
    rw [F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [hu]
    rcases pow_dvd_pow π hnr with ⟨c, hc⟩
    refine ⟨(u : F.valuationSubring) * c, ?_⟩
    rw [hc]
    ring
  · intro ha
    rw [F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    rcases ha with ⟨d, hd⟩
    have ha' : a = d * π ^ (n + 1) := by
      rw [hd, mul_comm]
    have hkill :
        standardLubinTateEndomorphismValue hπ n (π ^ (n + 1)) =
          0 := by
      rw [standardLubinTateEndomorphismValue,
        standardLubinTateEndomorphismEvalAt_uniformizer_pow]
      simpa [standardLubinTateLevelCoefficientHom] using
        standardLubinTatePrimitivePointInteger_iterate_succ_eq_zero
          hπ n
    calc
      standardLubinTateEndomorphismValue hπ n a =
          standardLubinTateEndomorphismValue hπ n
            (d * π ^ (n + 1)) := by rw [ha']
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTateEndomorphismValue hπ n
              (π ^ (n + 1)))
            (standardLubinTateEndomorphismValue_hasEval hπ n
              (π ^ (n + 1))) d :=
        standardLubinTateEndomorphismValue_mul hπ n d
          (π ^ (n + 1))
      _ =
          standardLubinTateEndomorphismEvalAt hπ n 0
            PowerSeries.HasEval.zero d := by
        apply
          standardLubinTateEndomorphismEvalAt_eq_of_point_eq
            hπ n
        exact hkill
      _ = 0 :=
        standardLubinTateEndomorphismEvalAt_zero_point hπ n d

/-- A unit fixes the primitive level-`n + 1` point exactly when it belongs
to `U^(n + 1)`. -/
theorem
    standardLubinTatePrimitivePointIntegerAction_eq_self_iff_mem_higherPrincipalUnitGroup
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    standardLubinTatePrimitivePointIntegerAction hπ n u =
        standardLubinTatePrimitivePointInteger hπ n ↔
      u ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF
        (n + 1) := by
  rw [CompleteDVF.higherPrincipalUnitGroup.mem_iff]
  constructor
  · intro hu
    apply
      (standardLubinTateEndomorphismValue_eq_zero_iff_mem_maximalIdeal_pow
        hπ n ((u : F.valuationSubring) - 1)).mp
    have huone :
        standardLubinTateEndomorphismValue hπ n
            (u : F.valuationSubring) =
          standardLubinTateEndomorphismValue hπ n 1 := by
      calc
        standardLubinTateEndomorphismValue hπ n
            (u : F.valuationSubring) =
            standardLubinTatePrimitivePointIntegerAction hπ n u :=
          rfl
        _ = standardLubinTatePrimitivePointInteger hπ n := hu
        _ = standardLubinTateEndomorphismValue hπ n 1 :=
          (standardLubinTateEndomorphismValue_one hπ n).symm
    calc
      standardLubinTateEndomorphismValue hπ n
          ((u : F.valuationSubring) - 1) =
          standardLubinTateFormalAdd hπ n
            (standardLubinTateEndomorphismValue hπ n
              (u : F.valuationSubring))
            (standardLubinTateEndomorphismValue hπ n (-1)) := by
              simpa [sub_eq_add_neg] using
                standardLubinTateEndomorphismValue_add hπ n
                  (u : F.valuationSubring) (-1)
      _ =
          standardLubinTateFormalAdd hπ n
            (standardLubinTateEndomorphismValue hπ n 1)
            (standardLubinTateEndomorphismValue hπ n (-1)) := by
              rw [huone]
      _ = standardLubinTateEndomorphismValue hπ n (1 + (-1)) :=
        (standardLubinTateEndomorphismValue_add hπ n 1 (-1)).symm
      _ = 0 := by simp
  · intro hu
    have hzero :
        standardLubinTateEndomorphismValue hπ n
            ((u : F.valuationSubring) - 1) = 0 :=
      (standardLubinTateEndomorphismValue_eq_zero_iff_mem_maximalIdeal_pow
        hπ n ((u : F.valuationSubring) - 1)).2 hu
    change
      standardLubinTateEndomorphismValue hπ n
          (u : F.valuationSubring) =
        standardLubinTatePrimitivePointInteger hπ n
    calc
      standardLubinTateEndomorphismValue hπ n
          (u : F.valuationSubring) =
          standardLubinTateEndomorphismValue hπ n
            (1 + ((u : F.valuationSubring) - 1)) := by
              congr 1
              ring
      _ =
          standardLubinTateFormalAdd hπ n
            (standardLubinTateEndomorphismValue hπ n 1)
            (standardLubinTateEndomorphismValue hπ n
              ((u : F.valuationSubring) - 1)) :=
        standardLubinTateEndomorphismValue_add hπ n 1
          ((u : F.valuationSubring) - 1)
      _ =
          standardLubinTateFormalAdd hπ n
            (standardLubinTateEndomorphismValue hπ n 1)
            (standardLubinTateEndomorphismValue hπ n 0) := by
              rw [hzero, standardLubinTateEndomorphismValue_zero]
      _ = standardLubinTateEndomorphismValue hπ n (1 + 0) :=
        (standardLubinTateEndomorphismValue_add hπ n 1 0).symm
      _ = standardLubinTatePrimitivePointInteger hπ n := by simp

/-- Two unit actions give the same primitive integer point exactly when
their quotient lies in `U^(n + 1)`. -/
theorem
    standardLubinTatePrimitivePointIntegerAction_eq_iff_div_mem_higherPrincipalUnitGroup
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u w : F.valuationSubringˣ) :
    standardLubinTatePrimitivePointIntegerAction hπ n u =
        standardLubinTatePrimitivePointIntegerAction hπ n w ↔
      u / w ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF
        (n + 1) := by
  constructor
  · intro huw
    apply
      (standardLubinTatePrimitivePointIntegerAction_eq_self_iff_mem_higherPrincipalUnitGroup
        hπ n (u / w)).mp
    calc
      standardLubinTatePrimitivePointIntegerAction hπ n (u / w) =
          standardLubinTatePrimitivePointIntegerAction hπ n
            (w⁻¹ * u) := by
              congr 1
              simp [div_eq_mul_inv, mul_comm]
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTatePrimitivePointIntegerAction hπ n u)
            (standardLubinTatePrimitivePointIntegerAction_hasEval hπ n u)
            ((w⁻¹ : F.valuationSubringˣ) : F.valuationSubring) :=
        standardLubinTatePrimitivePointIntegerAction_mul hπ n w⁻¹ u
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTatePrimitivePointIntegerAction hπ n w)
            (standardLubinTatePrimitivePointIntegerAction_hasEval hπ n w)
            ((w⁻¹ : F.valuationSubringˣ) : F.valuationSubring) := by
              apply
                standardLubinTateEndomorphismEvalAt_eq_of_point_eq
                  hπ n
              exact huw
      _ =
          standardLubinTatePrimitivePointIntegerAction hπ n (w⁻¹ * w) :=
        (standardLubinTatePrimitivePointIntegerAction_mul
          hπ n w⁻¹ w).symm
      _ = standardLubinTatePrimitivePointInteger hπ n := by simp
  · intro huw
    have hfixed :=
      (standardLubinTatePrimitivePointIntegerAction_eq_self_iff_mem_higherPrincipalUnitGroup
        hπ n (u / w)).2 huw
    calc
      standardLubinTatePrimitivePointIntegerAction hπ n u =
          standardLubinTatePrimitivePointIntegerAction hπ n
            (w * (u / w)) := by
              congr 1
              simp [div_eq_mul_inv, mul_left_comm]
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTatePrimitivePointIntegerAction hπ n (u / w))
            (standardLubinTatePrimitivePointIntegerAction_hasEval
              hπ n (u / w))
            (w : F.valuationSubring) :=
        standardLubinTatePrimitivePointIntegerAction_mul hπ n w (u / w)
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTatePrimitivePointInteger hπ n)
            (standardLubinTatePrimitivePointInteger_hasEval hπ n)
            (w : F.valuationSubring) := by
              apply
                standardLubinTateEndomorphismEvalAt_eq_of_point_eq
                  hπ n
              exact hfixed
      _ = standardLubinTatePrimitivePointIntegerAction hπ n w := rfl

/-- The analytic unit action, viewed in the finite-level field. -/
noncomputable def standardLubinTatePrimitiveLevelAction
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    standardLubinTateLevelField hπ n :=
  (standardLubinTatePrimitivePointIntegerAction hπ n u :
    standardLubinTateLevelField hπ n)

/-- The natural embedding of the finite-level integer ring into the fixed
separable closure. -/
noncomputable def standardLubinTateLevelIntegerToSeparableClosure
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring →+*
      SeparableClosure K :=
  (standardLubinTateLevelField hπ n).val.toRingHom.comp
    (standardLubinTateLevelCompleteDVF hπ n).valuation.valuationSubring.subtype

/-- The natural embedding of the finite-level integer ring into the fixed
separable closure is injective. -/
theorem standardLubinTateLevelIntegerToSeparableClosure_injective
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Function.Injective
      (standardLubinTateLevelIntegerToSeparableClosure hπ n) := by
  intro x y hxy
  change
    (standardLubinTateLevelField hπ n).val
        (x : standardLubinTateLevelField hπ n) =
      (standardLubinTateLevelField hπ n).val
        (y : standardLubinTateLevelField hπ n) at hxy
  apply Subtype.ext
  exact (standardLubinTateLevelField hπ n).val.injective hxy

/-- On base coefficients, the level-integer embedding is the fixed
embedding of the base field into its separable closure. -/
theorem standardLubinTateLevelIntegerToSeparableClosure_comp_coefficientHom
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTateLevelIntegerToSeparableClosure hπ n).comp
        (standardLubinTateLevelCoefficientHom hπ n) =
      (algebraMap K (SeparableClosure K)).comp
        (algebraMap F.valuationSubring K) := by
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply]
  change
    ((standardLubinTateLevelField hπ n).val
      (((standardLubinTateLevelCoefficientHom hπ n) a :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :
        standardLubinTateLevelField hπ n)) =
      algebraMap K (SeparableClosure K)
        (algebraMap F.valuationSubring K a)
  rw [standardLubinTateLevelCoefficientHom_apply]
  exact (standardLubinTateLevelField hπ n).val.commutes
    (algebraMap F.valuationSubring K a)

/-- The analytic unit action, transported from the level integer ring to
the chosen finite-level field. -/
noncomputable def standardLubinTatePrimitiveRootAction
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    SeparableClosure K :=
  standardLubinTateLevelIntegerToSeparableClosure hπ n
    (standardLubinTatePrimitivePointIntegerAction hπ n u)

/-- Coercing the finite-level action to the fixed separable closure gives
the primitive-root action. -/
@[simp]
theorem standardLubinTatePrimitiveLevelAction_coe
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    ((standardLubinTatePrimitiveLevelAction hπ n u :
        standardLubinTateLevelField hπ n) : SeparableClosure K) =
      standardLubinTatePrimitiveRootAction hπ n u :=
  rfl

/-- The identity unit fixes the chosen primitive root. -/
@[simp]
theorem standardLubinTatePrimitiveRootAction_one
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTatePrimitiveRootAction hπ n 1 =
      chosenStandardLubinTatePrimitiveRoot hπ n := by
  change
    standardLubinTateLevelIntegerToSeparableClosure hπ n
        (standardLubinTatePrimitivePointIntegerAction hπ n 1) =
      chosenStandardLubinTatePrimitiveRoot hπ n
  rw [standardLubinTatePrimitivePointIntegerAction_one]
  change
    ((standardLubinTatePrimitivePointInteger hπ n :
        standardLubinTateLevelField hπ n) : SeparableClosure K) =
      chosenStandardLubinTatePrimitiveRoot hπ n
  rw [standardLubinTatePrimitivePointInteger_coe]
  exact standardLubinTateLevelGenerator_coe hπ n

/-- Equality of primitive-root actions can be checked already in the
finite-level integer ring. -/
theorem standardLubinTatePrimitiveRootAction_eq_iff_integerAction_eq
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u w : F.valuationSubringˣ) :
    standardLubinTatePrimitiveRootAction hπ n u =
        standardLubinTatePrimitiveRootAction hπ n w ↔
      standardLubinTatePrimitivePointIntegerAction hπ n u =
        standardLubinTatePrimitivePointIntegerAction hπ n w := by
  change
    standardLubinTateLevelIntegerToSeparableClosure hπ n
        (standardLubinTatePrimitivePointIntegerAction hπ n u) =
      standardLubinTateLevelIntegerToSeparableClosure hπ n
        (standardLubinTatePrimitivePointIntegerAction hπ n w) ↔
      standardLubinTatePrimitivePointIntegerAction hπ n u =
        standardLubinTatePrimitivePointIntegerAction hπ n w
  constructor
  · intro h
    exact
      (standardLubinTateLevelIntegerToSeparableClosure_injective hπ n) h
  · exact congrArg (standardLubinTateLevelIntegerToSeparableClosure hπ n)

/-- Two unit actions give the same primitive root exactly when their
quotient lies in `U^(n + 1)`. -/
theorem
    standardLubinTatePrimitiveRootAction_eq_iff_div_mem_higherPrincipalUnitGroup
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u w : F.valuationSubringˣ) :
    standardLubinTatePrimitiveRootAction hπ n u =
        standardLubinTatePrimitiveRootAction hπ n w ↔
      u / w ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF
        (n + 1) := by
  rw [standardLubinTatePrimitiveRootAction_eq_iff_integerAction_eq,
    standardLubinTatePrimitivePointIntegerAction_eq_iff_div_mem_higherPrincipalUnitGroup]

/-- Unit parameters in the same higher-principal-unit coset give the same
primitive root. -/
theorem
    standardLubinTatePrimitiveRootAction_eq_of_div_mem_higherPrincipalUnitGroup
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    {u w : F.valuationSubringˣ}
    (huw :
      u / w ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF
        (n + 1)) :
    standardLubinTatePrimitiveRootAction hπ n u =
      standardLubinTatePrimitiveRootAction hπ n w :=
  (standardLubinTatePrimitiveRootAction_eq_iff_div_mem_higherPrincipalUnitGroup
    hπ n u w).2 huw

/-- A unit translate of the chosen primitive point is again a root of the
level-`n + 1` primitive division polynomial. -/
theorem standardLubinTatePrimitiveRootAction_isRoot
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (u : F.valuationSubringˣ) :
    ((standardLubinTatePrimitivePolynomialOverField F π n).map
      (algebraMap K (SeparableClosure K))).IsRoot
        (standardLubinTatePrimitiveRootAction hπ n u) := by
  let lambda := standardLubinTatePrimitivePointInteger hπ n
  let hlambda : PowerSeries.HasEval lambda :=
    standardLubinTatePrimitivePointInteger_hasEval hπ n
  let y := standardLubinTatePrimitivePointIntegerAction hπ n u
  let hy : PowerSeries.HasEval y :=
    standardLubinTatePrimitivePointIntegerAction_hasEval hπ n u
  have hkillLambda :
      standardLubinTateEndomorphismValue hπ n (π ^ (n + 1)) = 0 := by
    rw [standardLubinTateEndomorphismValue,
      standardLubinTateEndomorphismEvalAt_uniformizer_pow]
    simpa [standardLubinTateLevelCoefficientHom] using
      standardLubinTatePrimitivePointInteger_iterate_succ_eq_zero hπ n
  have hySucc :
      Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n) y
          (standardLubinTatePolynomialIterate F π (n + 1)) = 0 := by
    rw [← standardLubinTateEndomorphismEvalAt_uniformizer_pow
      hπ n y hy (n + 1)]
    calc
      standardLubinTateEndomorphismEvalAt hπ n y hy
          (π ^ (n + 1)) =
          standardLubinTateEndomorphismValue hπ n
            (π ^ (n + 1) * (u : F.valuationSubring)) := by
        simpa [y, standardLubinTatePrimitivePointIntegerAction] using
          (standardLubinTateEndomorphismValue_mul hπ n
            (π ^ (n + 1)) (u : F.valuationSubring)).symm
      _ =
          standardLubinTateEndomorphismValue hπ n
            ((u : F.valuationSubring) * π ^ (n + 1)) := by
        rw [mul_comm]
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTateEndomorphismValue hπ n (π ^ (n + 1)))
            (standardLubinTateEndomorphismValue_hasEval hπ n
              (π ^ (n + 1)))
            (u : F.valuationSubring) :=
        standardLubinTateEndomorphismValue_mul hπ n
          (u : F.valuationSubring) (π ^ (n + 1))
      _ =
          standardLubinTateEndomorphismEvalAt hπ n 0
            PowerSeries.HasEval.zero (u : F.valuationSubring) := by
        apply
          standardLubinTateEndomorphismEvalAt_eq_of_point_eq
            hπ n
        exact hkillLambda
      _ = 0 :=
        standardLubinTateEndomorphismEvalAt_zero_point hπ n
          (u : F.valuationSubring)
  have hyN :
      Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n) y
          (standardLubinTatePolynomialIterate F π n) ≠ 0 := by
    intro hyNZero
    have hyEvalZero :
        standardLubinTateEndomorphismEvalAt hπ n y hy (π ^ n) = 0 := by
      rw [standardLubinTateEndomorphismEvalAt_uniformizer_pow]
      exact hyNZero
    let z := standardLubinTateEndomorphismValue hπ n (π ^ n)
    let hz : PowerSeries.HasEval z :=
      standardLubinTateEndomorphismValue_hasEval hπ n (π ^ n)
    have huzero :
        standardLubinTateEndomorphismEvalAt hπ n z hz
            (u : F.valuationSubring) = 0 := by
      calc
        standardLubinTateEndomorphismEvalAt hπ n z hz
            (u : F.valuationSubring) =
            standardLubinTateEndomorphismValue hπ n
              ((u : F.valuationSubring) * π ^ n) := by
          simpa [z] using
            (standardLubinTateEndomorphismValue_mul hπ n
              (u : F.valuationSubring) (π ^ n)).symm
        _ =
            standardLubinTateEndomorphismValue hπ n
              (π ^ n * (u : F.valuationSubring)) := by
          rw [mul_comm]
        _ =
            standardLubinTateEndomorphismEvalAt hπ n y hy (π ^ n) := by
          simpa [y, standardLubinTatePrimitivePointIntegerAction] using
            standardLubinTateEndomorphismValue_mul hπ n
              (π ^ n) (u : F.valuationSubring)
        _ = 0 := hyEvalZero
    have hzZero : z = 0 := by
      apply
        standardLubinTateEndomorphismEvalAt_unit_injective
          hπ n u hz PowerSeries.HasEval.zero
      rw [huzero,
        standardLubinTateEndomorphismEvalAt_zero_point]
    have hne :=
      standardLubinTatePrimitivePointInteger_iterate_ne_zero_of_le
        hπ n (show n ≤ n from le_rfl)
    apply hne
    change
      Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n) lambda
          (standardLubinTatePolynomialIterate F π n) = 0
    calc
      _ =
          standardLubinTateEndomorphismEvalAt hπ n lambda hlambda
            (π ^ n) :=
        (standardLubinTateEndomorphismEvalAt_uniformizer_pow
          hπ n lambda hlambda n).symm
      _ = standardLubinTateEndomorphismValue hπ n (π ^ n) := rfl
      _ = 0 := by simpa [z] using hzZero
  have hfactor :=
    congrArg
      (Polynomial.eval₂
        (standardLubinTateLevelCoefficientHom hπ n) y)
      (standardLubinTatePolynomialIterate_succ_factor F π n)
  rw [hySucc, Polynomial.eval₂_mul] at hfactor
  have hprimitive :
      Polynomial.eval₂
          (standardLubinTateLevelCoefficientHom hπ n) y
          (standardLubinTatePrimitivePolynomial F π n) = 0 :=
    (mul_eq_zero.mp hfactor.symm).resolve_left hyN
  have hprimitiveMap :=
    congrArg (standardLubinTateLevelIntegerToSeparableClosure hπ n)
      hprimitive
  rw [map_zero, Polynomial.hom_eval₂,
    standardLubinTateLevelIntegerToSeparableClosure_comp_coefficientHom]
      at hprimitiveMap
  simpa [Polynomial.IsRoot,
    standardLubinTatePrimitivePolynomialOverField,
    standardLubinTatePrimitiveRootAction,
    Polynomial.eval_map, Polynomial.eval₂_map, y] using hprimitiveMap

end AnalyticAction

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_FiniteParameters
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.DiscreteValuationField.fieldNormFiltrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.fieldNormFiltrationPreimageSubgroup_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHom_apply_ofAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_mul_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeries_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_expSeries_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.DiscreteValuationField.coe_fieldNormFiltrationQuotientModuloPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.fieldNormFiltrationQuotientMap_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.fieldNormFiltrationQuotientMap_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.fieldNormFiltrationQuotientModuloPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.fieldNormMapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.mem_fieldNormFiltrationPreimageSubgroup_iff _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite unit parameters for standard Lubin--Tate levels

For a local field `F`, the unit parameters visible at primitive level `n + 1`
are the valuation-ring units modulo the higher principal-unit subgroup
`U^(n + 1)`.  This file records that quotient, chooses representatives, and
computes its cardinality as

`(q - 1) * q ^ n`,

where `q` is the residue-field cardinality.  The final declarations descend
the standard Lubin--Tate action on the chosen primitive point to this finite
parameter quotient.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF

variable {K : Type u} [Field K]

/-- The finite unit parameters visible on the primitive level-`n + 1`
standard Lubin--Tate torsion point. -/
def standardLubinTateUnitParameter
    (F : LocalField.{u, v} K) (n : ℕ) : Type u :=
  F.valuationSubringˣ ⧸
    CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)

/-- The finite unit parameter quotient carries its canonical commutative
group structure. -/
instance standardLubinTateUnitParameter_commGroup
    (F : LocalField.{u, v} K) (n : ℕ) :
    CommGroup (standardLubinTateUnitParameter F n) := by
  change CommGroup
    (F.valuationSubringˣ ⧸
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1))
  infer_instance

/-- The canonical class of a valuation-ring unit at primitive level
`n + 1`. -/
def standardLubinTateUnitParameterClass
    (F : LocalField.{u, v} K) (n : ℕ) :
    F.valuationSubringˣ →* standardLubinTateUnitParameter F n :=
  QuotientGroup.mk'
    (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1))

/-- A chosen valuation-ring unit representing a finite unit parameter. -/
noncomputable def standardLubinTateUnitParameterChosenRepresentative
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : standardLubinTateUnitParameter F n) :
    F.valuationSubringˣ :=
  Classical.choose
    (QuotientGroup.mk'_surjective
      (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) a)

/-- The chosen representative has the prescribed quotient class. -/
@[simp]
theorem standardLubinTateUnitParameterChosenRepresentative_spec
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterClass F n
        (standardLubinTateUnitParameterChosenRepresentative F n a) = a :=
  Classical.choose_spec
    (QuotientGroup.mk'_surjective
      (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) a)

/-- Two valuation-ring units determine the same finite parameter exactly
when their quotient belongs to `U^(n + 1)`. -/
theorem standardLubinTateUnitParameterClass_eq_iff_div_mem
    (F : LocalField.{u, v} K) (n : ℕ)
    (a b : F.valuationSubringˣ) :
    standardLubinTateUnitParameterClass F n a =
        standardLubinTateUnitParameterClass F n b ↔
      a / b ∈
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1) := by
  change
    QuotientGroup.mk'
        (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) a =
      QuotientGroup.mk'
        (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) b ↔
      _
  exact QuotientGroup.eq_iff_div_mem

/-- The finite standard unit parameter set has cardinality
`(q - 1) * q ^ n`. -/
theorem standardLubinTateUnitParameter_natCard
    (F : LocalField.{u, v} K) (n : ℕ) :
    Nat.card (standardLubinTateUnitParameter F n) =
      (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n := by
  let D := F.toCompleteDVF
  let U := CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration D
  let Q :=
    F.valuationSubringˣ ⧸
      CompleteDVF.higherPrincipalUnitGroup D (n + 1)
  let H : Subgroup Q :=
    U.principalUnitSubgroupClassInQuotient 1 (n + 1)
  have hlevel : 1 ≤ n + 1 := by omega
  obtain ⟨π, hπ⟩ := F.exists_uniformizer
  have hquotient :
      Nat.card (Q ⧸ H) = Nat.card F.residueField - 1 := by
    calc
      Nat.card (Q ⧸ H) =
          Nat.card
            (F.valuationSubringˣ ⧸
              CompleteDVF.higherPrincipalUnitGroup D 1) := by
        exact Nat.card_congr
          (U.quotientModuloPrincipalUnitClassEquivQuotientOfLe
            hlevel).toEquiv
      _ = Nat.card F.residueFieldˣ := by
        exact Nat.card_congr
          (higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits D).toEquiv
      _ = Nat.card F.residueField - 1 := Nat.card_units F.residueField
  have hsubquotient :
      Nat.card H = Nat.card F.residueField ^ n := by
    calc
      Nat.card H =
          Nat.card (U.principalUnitSubquotient 1 (n + 1)) := by
        exact
          (Nat.card_congr
            (U.principalUnitSubquotientEquivClassInQuotientOfLe
              hlevel).toEquiv).symm
      _ =
          Nat.card
            (CompleteDVF.higherPrincipalUnitGroup D 1 ⧸
              (CompleteDVF.higherPrincipalUnitGroup D (n + 1)).subgroupOf
                (CompleteDVF.higherPrincipalUnitGroup D 1)) := by
        exact Nat.card_congr
          (U.principalUnitSubquotientConcreteEquiv 1 (n + 1)).toEquiv
      _ = Nat.card F.residueField ^ n := by
        simpa [D] using
          (higherPrincipalUnitGroup.card_principalUnitSubquotient_one_eq_residue_pow_of_uniformizer
            D hπ hlevel)
  change Nat.card Q =
    (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H,
    hquotient, hsubquotient]

/-- The primitive root attached to a finite unit parameter.  A representative
is chosen only to evaluate the primitive action; the theorem below shows that
the value depends only on its quotient class. -/
noncomputable def standardLubinTateUnitParameterRoot
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    SeparableClosure K :=
  standardLubinTatePrimitiveRootAction hπ n
    (standardLubinTateUnitParameterChosenRepresentative F n a)

/-- The parameter root can be evaluated using any representative of its
quotient class. -/
theorem standardLubinTateUnitParameterRoot_eq_action_of_class_eq
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n)
    (u : F.valuationSubringˣ)
    (hu : standardLubinTateUnitParameterClass F n u = a) :
    standardLubinTateUnitParameterRoot F hπ n a =
      standardLubinTatePrimitiveRootAction hπ n u := by
  apply
    standardLubinTatePrimitiveRootAction_eq_of_div_mem_higherPrincipalUnitGroup
      hπ n
  exact
    (standardLubinTateUnitParameterClass_eq_iff_div_mem F n
      (standardLubinTateUnitParameterChosenRepresentative F n a) u).mp
        ((standardLubinTateUnitParameterChosenRepresentative_spec F n a).trans
          hu.symm)

/-- Evaluating at a canonical quotient class recovers the primitive action
of the original valuation-ring unit. -/
@[simp]
theorem standardLubinTateUnitParameterRoot_class
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (u : F.valuationSubringˣ) :
    standardLubinTateUnitParameterRoot F hπ n
        (standardLubinTateUnitParameterClass F n u) =
      standardLubinTatePrimitiveRootAction hπ n u :=
  standardLubinTateUnitParameterRoot_eq_action_of_class_eq
    F hπ n _ u rfl

/-- Every finite unit parameter gives a root of the primitive level
polynomial. -/
theorem standardLubinTateUnitParameterRoot_isRoot
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    ((standardLubinTatePrimitivePolynomialOverField F π n).map
      (algebraMap K (SeparableClosure K))).IsRoot
        (standardLubinTateUnitParameterRoot F hπ n a) := by
  simpa [standardLubinTateUnitParameterRoot] using
    standardLubinTatePrimitiveRootAction_isRoot hπ n
      (standardLubinTateUnitParameterChosenRepresentative F n a)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_LevelAutomorphisms
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instSMulCommClass _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHom_apply_ofAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_mul_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeries_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_expSeries_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_one_ofWithZeroValuation _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Automorphisms of standard Lubin--Tate level fields

The finite unit parameters at primitive level `n + 1` act on the chosen
primitive division point.  Once the resulting roots are regarded as elements
of the simple level field, the canonical power basis lifts them to algebra
automorphisms.  Faithfulness of the finite action and the parameter-cardinality
formula then show that the automorphism group has cardinality equal to the
field degree, hence that every standard level is Galois.
-/

noncomputable section

open scoped Polynomial PowerSeries

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open ValuationTheory.DiscreteValuationField

variable {K : Type u} [Field K]

noncomputable local instance (priority := 50)
    standardLubinTateLevelAutomorphismCoefficientUniformSpace
    (F : LocalField.{u, v} K) :
    UniformSpace F.valuationSubring :=
  ⊥

noncomputable local instance
    standardLubinTateLevelAutomorphismTargetWithIdeal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    WithIdeal
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring where
  i := (standardLubinTateLevelCompleteDVF hπ n).maximalIdeal

noncomputable local instance
    standardLubinTateLevelAutomorphismTargetCompleteSpace
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    CompleteSpace
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

noncomputable local instance
    standardLubinTateLevelAutomorphismTargetT2Space
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    T2Space
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

/-- A finite parameter root, regarded as an element of its standard level
field through the analytically constructed integral action. -/
noncomputable def standardLubinTateUnitParameterLevelRoot
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    standardLubinTateLevelField hπ n :=
  standardLubinTatePrimitiveLevelAction hπ n
    (standardLubinTateUnitParameterChosenRepresentative F n a)

/-- The level-field realization of a parameter root agrees with its ambient
separable-closure realization. -/
@[simp]
theorem standardLubinTateUnitParameterLevelRoot_coe
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    (standardLubinTateUnitParameterLevelRoot F hπ n a :
      SeparableClosure K) =
        standardLubinTateUnitParameterRoot F hπ n a := by
  simp [standardLubinTateUnitParameterLevelRoot,
    standardLubinTateUnitParameterRoot]

/-- Distinct finite unit parameters give distinct roots inside the standard
level field. -/
theorem standardLubinTateUnitParameterLevelRoot_injective
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    Function.Injective
      (standardLubinTateUnitParameterLevelRoot F hπ n) := by
  intro a b hab
  let u :=
    standardLubinTateUnitParameterChosenRepresentative F n a
  let w :=
    standardLubinTateUnitParameterChosenRepresentative F n b
  have hroot :
      standardLubinTatePrimitiveRootAction hπ n u =
        standardLubinTatePrimitiveRootAction hπ n w := by
    have hcoe := congrArg
      (fun z : standardLubinTateLevelField hπ n =>
        (z : SeparableClosure K)) hab
    simpa [standardLubinTateUnitParameterLevelRoot,
      standardLubinTatePrimitiveLevelAction_coe] using hcoe
  have hdiv :
      u / w ∈
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1) :=
    (standardLubinTatePrimitiveRootAction_eq_iff_div_mem_higherPrincipalUnitGroup
      hπ n u w).mp hroot
  calc
    a = standardLubinTateUnitParameterClass F n u := by
      simp [u]
    _ = standardLubinTateUnitParameterClass F n w :=
      (standardLubinTateUnitParameterClass_eq_iff_div_mem
        F n u w).2 hdiv
    _ = b := by
      simp [w]

/-- The identity parameter gives the chosen power-basis generator. -/
@[simp]
theorem standardLubinTateUnitParameterLevelRoot_one
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateUnitParameterLevelRoot F hπ n 1 =
      (standardLubinTateLevelPowerBasis hπ n).gen := by
  apply Subtype.ext
  rw [standardLubinTateUnitParameterLevelRoot_coe]
  have hroot :
      standardLubinTateUnitParameterRoot F hπ n 1 =
        standardLubinTatePrimitiveRootAction hπ n
          (1 : F.valuationSubringˣ) := by
    simpa only [map_one] using
      standardLubinTateUnitParameterRoot_class F hπ n
        (1 : F.valuationSubringˣ)
  rw [hroot, standardLubinTatePrimitiveRootAction_one]
  simpa only [standardLubinTateLevelGenerator] using
    (standardLubinTateLevelGenerator_coe hπ n).symm

/-- A parameter root annihilates the minimal polynomial of the canonical
level-field generator. -/
theorem standardLubinTateUnitParameterLevelRoot_aeval_minpoly
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    Polynomial.aeval (standardLubinTateUnitParameterLevelRoot F hπ n a)
        (minpoly K (standardLubinTateLevelPowerBasis hπ n).gen) = 0 := by
  rw [standardLubinTateLevelPowerBasis_minpoly]
  let ι : standardLubinTateLevelField hπ n →ₐ[K] SeparableClosure K :=
    (standardLubinTateLevelField hπ n).val
  apply ι.injective
  change ι (Polynomial.aeval
    (standardLubinTateUnitParameterLevelRoot F hπ n a)
    (standardLubinTatePrimitivePolynomialOverField F π n)) = ι 0
  rw [← Polynomial.aeval_algHom_apply (f := ι), map_zero]
  change Polynomial.eval₂
    (algebraMap K (SeparableClosure K))
    (standardLubinTateUnitParameterRoot F hπ n a)
    (standardLubinTatePrimitivePolynomialOverField F π n) = 0
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using
    standardLubinTateUnitParameterRoot_isRoot F hπ n a

/-- The algebra endomorphism sending the chosen primitive generator to the
root attached to a finite unit parameter. -/
noncomputable def standardLubinTateUnitParameterAlgHom
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    standardLubinTateLevelField hπ n →ₐ[K]
      standardLubinTateLevelField hπ n :=
  (standardLubinTateLevelPowerBasis hπ n).lift
    (standardLubinTateUnitParameterLevelRoot F hπ n a)
    (standardLubinTateUnitParameterLevelRoot_aeval_minpoly F hπ n a)

/-- The parameter endomorphism sends the power-basis generator to the
corresponding parameter root. -/
@[simp]
theorem standardLubinTateUnitParameterAlgHom_apply_gen
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterAlgHom F hπ n a
        (standardLubinTateLevelPowerBasis hπ n).gen =
      standardLubinTateUnitParameterLevelRoot F hπ n a :=
  (standardLubinTateLevelPowerBasis hπ n).lift_gen _ _

/-- The finite-dimensional parameter endomorphism is an automorphism. -/
noncomputable def standardLubinTateUnitParameterAlgEquiv
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    standardLubinTateLevelField hπ n ≃ₐ[K]
      standardLubinTateLevelField hπ n := by
  letI : FiniteDimensional K (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  exact AlgEquiv.ofBijective
    (standardLubinTateUnitParameterAlgHom F hπ n a)
    (AlgHom.bijective
      (standardLubinTateUnitParameterAlgHom F hπ n a))

/-- The parameter automorphism sends the power-basis generator to the
corresponding parameter root. -/
@[simp]
theorem standardLubinTateUnitParameterAlgEquiv_apply_gen
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterAlgEquiv F hπ n a
        (standardLubinTateLevelPowerBasis hπ n).gen =
      standardLubinTateUnitParameterLevelRoot F hπ n a := by
  rw [standardLubinTateUnitParameterAlgEquiv,
    AlgEquiv.ofBijective_apply,
    standardLubinTateUnitParameterAlgHom_apply_gen]

theorem
    standardLubinTateLevelAlgEquiv_mem_valuationSubring_iff
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
    (σ : Gal((standardLubinTateLevelField hπ n) / K))
    (x : standardLubinTateLevelField hπ n) :
    x ∈ (standardLubinTateLevelCompleteDVF hπ n).valuation.valuationSubring ↔
      σ x ∈
        (standardLubinTateLevelCompleteDVF hπ n).valuation.valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  let : IsScalarTower F.valuationSubring target.valuationSubring
      (standardLubinTateLevelField hπ n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsIntegralClosure target.valuationSubring F.valuationSubring
      (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelCompleteDVF_isIntegralClosure hπ n
  have hforward
      (τ : Gal((standardLubinTateLevelField hπ n) / K))
      {y : standardLubinTateLevelField hπ n}
      (hy : y ∈ target.valuation.valuationSubring) :
      τ y ∈ target.valuation.valuationSubring := by
    have hyIntegral : IsIntegral F.valuationSubring y :=
      (IsIntegralClosure.isIntegral_iff
        (A := target.valuationSubring)
        (R := F.valuationSubring)
        (B := standardLubinTateLevelField hπ n)).2
          ⟨⟨y, hy⟩, rfl⟩
    have hτIntegral : IsIntegral F.valuationSubring (τ y) :=
      IsIntegral.map τ.toAlgHom hyIntegral
    rcases
        (IsIntegralClosure.isIntegral_iff
          (A := target.valuationSubring)
          (R := F.valuationSubring)
          (B := standardLubinTateLevelField hπ n)).1 hτIntegral
      with ⟨z, hz⟩
    exact hz ▸ z.property
  constructor
  · exact hforward σ
  · intro hσx
    have hback := hforward σ.symm hσx
    simpa using hback

noncomputable def
    standardLubinTateLevelAutomorphismIntegerRingEquiv
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
    (σ : Gal((standardLubinTateLevelField hπ n) / K)) :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring ≃+*
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  higherPrincipalUnitGroup.valuationSubringRingEquivOfPreserves
    (standardLubinTateLevelCompleteDVF hπ n)
    σ.toRingEquiv
    (standardLubinTateLevelAlgEquiv_mem_valuationSubring_iff
      hπ n σ)

@[simp]
theorem
    standardLubinTateLevelAutomorphismIntegerRingEquiv_apply
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
    (σ : Gal((standardLubinTateLevelField hπ n) / K))
    (x :
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :
    ((standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ x :
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :
      standardLubinTateLevelField hπ n) =
        σ (x : standardLubinTateLevelField hπ n) :=
  rfl

theorem
    standardLubinTateLevelAutomorphismIntegerRingEquiv_continuous
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
    (σ : Gal((standardLubinTateLevelField hπ n) / K)) :
    Continuous
      (standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ) := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  let r :=
    standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
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
        (standardLubinTateLevelAlgEquiv_mem_valuationSubring_iff
          hπ n σ)
        m x).2 hx

theorem
    standardLubinTateLevelAutomorphismIntegerRingEquiv_comp_coefficientHom
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
    (σ : Gal((standardLubinTateLevelField hπ n) / K)) :
    (standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ :
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring →+*
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring).comp
        (standardLubinTateLevelCoefficientHom hπ n) =
      standardLubinTateLevelCoefficientHom hπ n := by
  ext a : 1
  apply Subtype.ext
  simp only [RingHom.comp_apply,
    standardLubinTateLevelCoefficientHom_apply]
  exact σ.commutes (a : K)

theorem
    standardLubinTateLevelAutomorphismIntegerRingEquiv_primitivePoint_hasEval
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
    (σ : Gal((standardLubinTateLevelField hπ n) / K)) :
    PowerSeries.HasEval
      (standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
        (standardLubinTatePrimitivePointInteger hπ n)) := by
  let r :=
    standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
  let lambda := standardLubinTatePrimitivePointInteger hπ n
  have hlambda :
      Filter.Tendsto (fun m : ℕ => lambda ^ m) Filter.atTop
        (nhds (0 :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)) :=
    standardLubinTatePrimitivePointInteger_hasEval hπ n
  have hr :
      Filter.Tendsto (fun m : ℕ => r (lambda ^ m)) Filter.atTop
        (nhds (r 0)) :=
    Filter.Tendsto.comp
      (standardLubinTateLevelAutomorphismIntegerRingEquiv_continuous
        hπ n σ).continuousAt
      hlambda
  change Filter.Tendsto
    (fun m : ℕ => (r lambda) ^ m) Filter.atTop (nhds 0)
  simpa only [map_pow, map_zero] using hr

theorem
    standardLubinTateLevelAutomorphismIntegerRingEquiv_endomorphismValue
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
    (σ : Gal((standardLubinTateLevelField hπ n) / K))
    (a : F.valuationSubring) :
    standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
        (standardLubinTateEndomorphismValue hπ n a) =
      standardLubinTateEndomorphismEvalAt hπ n
        (standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
          (standardLubinTatePrimitivePointInteger hπ n))
        (standardLubinTateLevelAutomorphismIntegerRingEquiv_primitivePoint_hasEval
          hπ n σ)
        a := by
  let r :=
    standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
  have hcomp :=
    PowerSeries.comp_eval₂
      (φ := standardLubinTateLevelCoefficientHom hπ n)
      continuous_of_discreteTopology
      (standardLubinTatePrimitivePointInteger_hasEval hπ n)
      (ε := (r :
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring →+*
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring))
      (standardLubinTateLevelAutomorphismIntegerRingEquiv_continuous
        hπ n σ)
  have happ := congrArg
    (fun f =>
      f (SameUniformizer.standardLubinTateEndomorphism hπ a))
    hcomp
  rw [
    standardLubinTateLevelAutomorphismIntegerRingEquiv_comp_coefficientHom
      hπ n σ] at happ
  simpa [standardLubinTateEndomorphismValue,
    standardLubinTateEndomorphismEvalAt,
    standardLubinTateLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom, Function.comp_apply, r] using happ

/-- A parameter automorphism transports every parameter root according to
multiplication of finite unit parameters. -/
theorem standardLubinTateUnitParameterAlgEquiv_apply_levelRoot
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a b : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterAlgEquiv F hπ n a
        (standardLubinTateUnitParameterLevelRoot F hπ n b) =
      standardLubinTateUnitParameterLevelRoot F hπ n (a * b) := by
  let u :=
    standardLubinTateUnitParameterChosenRepresentative F n a
  let w :=
    standardLubinTateUnitParameterChosenRepresentative F n b
  let z :=
    standardLubinTateUnitParameterChosenRepresentative F n (a * b)
  let σ := standardLubinTateUnitParameterAlgEquiv F hπ n a
  let r :=
    standardLubinTateLevelAutomorphismIntegerRingEquiv hπ n σ
  have hrgen :
      r (standardLubinTatePrimitivePointInteger hπ n) =
        standardLubinTatePrimitivePointIntegerAction hπ n u := by
    apply Subtype.ext
    rw [standardLubinTateLevelAutomorphismIntegerRingEquiv_apply,
      standardLubinTatePrimitivePointInteger_coe]
    simp [σ, u, standardLubinTateLevelGenerator,
      standardLubinTateUnitParameterLevelRoot,
      standardLubinTatePrimitiveLevelAction]
  have hrw :
      r (standardLubinTatePrimitivePointIntegerAction hπ n w) =
        standardLubinTatePrimitivePointIntegerAction hπ n (w * u) := by
    calc
      r (standardLubinTatePrimitivePointIntegerAction hπ n w) =
          standardLubinTateEndomorphismEvalAt hπ n
            (r (standardLubinTatePrimitivePointInteger hπ n))
            (standardLubinTateLevelAutomorphismIntegerRingEquiv_primitivePoint_hasEval
              hπ n σ)
            (w : F.valuationSubring) := by
              simpa [standardLubinTatePrimitivePointIntegerAction] using
                standardLubinTateLevelAutomorphismIntegerRingEquiv_endomorphismValue
                  hπ n σ (w : F.valuationSubring)
      _ =
          standardLubinTateEndomorphismEvalAt hπ n
            (standardLubinTatePrimitivePointIntegerAction hπ n u)
            (standardLubinTatePrimitivePointIntegerAction_hasEval hπ n u)
            (w : F.valuationSubring) := by
              simp only [hrgen]
      _ = standardLubinTatePrimitivePointIntegerAction hπ n (w * u) :=
        (standardLubinTatePrimitivePointIntegerAction_mul
          hπ n w u).symm
  have hclass :
      standardLubinTateUnitParameterClass F n (w * u) =
        standardLubinTateUnitParameterClass F n z := by
    calc
      standardLubinTateUnitParameterClass F n (w * u) =
          b * a := by
            rw [map_mul]
            simp [u, w]
      _ = a * b := mul_comm b a
      _ = standardLubinTateUnitParameterClass F n z := by
        simp [z]
  have hdiv :
      w * u / z ∈
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1) :=
    (standardLubinTateUnitParameterClass_eq_iff_div_mem
      F n (w * u) z).mp hclass
  have hwuz :
      standardLubinTatePrimitivePointIntegerAction hπ n (w * u) =
        standardLubinTatePrimitivePointIntegerAction hπ n z :=
    (standardLubinTatePrimitivePointIntegerAction_eq_iff_div_mem_higherPrincipalUnitGroup
      hπ n (w * u) z).2 hdiv
  change
    σ
      ((standardLubinTatePrimitivePointIntegerAction hπ n w :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :
        standardLubinTateLevelField hπ n) =
      ((standardLubinTatePrimitivePointIntegerAction hπ n z :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :
        standardLubinTateLevelField hπ n)
  calc
    σ
        ((standardLubinTatePrimitivePointIntegerAction hπ n w :
            (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :
          standardLubinTateLevelField hπ n) =
        (r (standardLubinTatePrimitivePointIntegerAction hπ n w) :
          standardLubinTateLevelField hπ n) := by
            rw [
              standardLubinTateLevelAutomorphismIntegerRingEquiv_apply]
    _ =
        (standardLubinTatePrimitivePointIntegerAction hπ n (w * u) :
          standardLubinTateLevelField hπ n) :=
      congrArg Subtype.val hrw
    _ =
        (standardLubinTatePrimitivePointIntegerAction hπ n z :
          standardLubinTateLevelField hπ n) :=
      congrArg Subtype.val hwuz

/-- The identity parameter gives the identity level-field automorphism. -/
theorem standardLubinTateUnitParameterAlgEquiv_one
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateUnitParameterAlgEquiv F hπ n 1 = 1 := by
  apply MulSemiringAction.toAlgHom_injective K
    (standardLubinTateLevelField hπ n)
  apply (standardLubinTateLevelPowerBasis hπ n).algHom_ext
  simp only [MulSemiringAction.toAlgHom_apply, one_smul,
    AlgEquiv.smul_def]
  rw [standardLubinTateUnitParameterAlgEquiv_apply_gen,
    standardLubinTateUnitParameterLevelRoot_one]

/-- Multiplication of finite parameters is composition of the associated
level-field automorphisms. -/
theorem standardLubinTateUnitParameterAlgEquiv_mul
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a b : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterAlgEquiv F hπ n (a * b) =
      standardLubinTateUnitParameterAlgEquiv F hπ n a *
        standardLubinTateUnitParameterAlgEquiv F hπ n b := by
  apply MulSemiringAction.toAlgHom_injective K
    (standardLubinTateLevelField hπ n)
  apply (standardLubinTateLevelPowerBasis hπ n).algHom_ext
  simp only [MulSemiringAction.toAlgHom_apply, mul_smul,
    AlgEquiv.smul_def]
  rw [standardLubinTateUnitParameterAlgEquiv_apply_gen,
    standardLubinTateUnitParameterAlgEquiv_apply_gen,
    standardLubinTateUnitParameterAlgEquiv_apply_levelRoot]

/-- The explicit map from finite unit parameters to the finite-level Galois
group. -/
noncomputable def standardLubinTateUnitParameterToGal
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateUnitParameter F n →
      Gal((standardLubinTateLevelField hπ n) / K) :=
  standardLubinTateUnitParameterAlgEquiv F hπ n

/-- Faithfulness of the primitive action makes the parameter-to-automorphism
map injective. -/
theorem standardLubinTateUnitParameterToGal_injective
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    Function.Injective
      (standardLubinTateUnitParameterToGal F hπ n) := by
  intro a b hab
  apply standardLubinTateUnitParameterLevelRoot_injective F hπ n
  have hgen := congrArg
    (fun σ : Gal((standardLubinTateLevelField hπ n) / K) =>
      σ (standardLubinTateLevelPowerBasis hπ n).gen) hab
  simpa [standardLubinTateUnitParameterToGal] using hgen

/-- The explicit parameter map preserves the identity element. -/
theorem standardLubinTateUnitParameterToGal_one
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateUnitParameterToGal F hπ n 1 = 1 := by
  simpa [standardLubinTateUnitParameterToGal] using
    standardLubinTateUnitParameterAlgEquiv_one F hπ n

/-- The explicit parameter map preserves multiplication. -/
theorem standardLubinTateUnitParameterToGal_mul
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a b : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterToGal F hπ n (a * b) =
      standardLubinTateUnitParameterToGal F hπ n a *
        standardLubinTateUnitParameterToGal F hπ n b := by
  simpa [standardLubinTateUnitParameterToGal] using
    standardLubinTateUnitParameterAlgEquiv_mul F hπ n a b

/-- The automorphism group of a standard finite level is finite. -/
noncomputable instance standardLubinTateLevelField_galFinite
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Finite (Gal((standardLubinTateLevelField hπ n) / K)) := by
  let : FiniteDimensional K (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : Module.Free K (standardLubinTateLevelField hπ n) :=
    Module.Free.of_divisionRing _ _
  let : Finite
      ((standardLubinTateLevelField hπ n) →ₐ[K]
        (standardLubinTateLevelField hπ n)) :=
    Finite.algHom _ _ _
  exact Finite.algEquiv

/-- The number of base-field automorphisms of a standard level is at most
its field degree. -/
theorem standardLubinTateLevelField_natCard_gal_le_finrank
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Nat.card (Gal((standardLubinTateLevelField hπ n) / K)) ≤
      Module.finrank K (standardLubinTateLevelField hπ n) := by
  let : FiniteDimensional K (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  rw [Nat.card_eq_fintype_card]
  exact AlgEquiv.card_le

/-- The automorphism group of a standard finite level has cardinality equal
to the field degree. -/
theorem standardLubinTateLevelField_natCard_gal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Nat.card (Gal((standardLubinTateLevelField hπ n) / K)) =
      Module.finrank K (standardLubinTateLevelField hπ n) := by
  let : FiniteDimensional K (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  apply Nat.le_antisymm
  · exact standardLubinTateLevelField_natCard_gal_le_finrank hπ n
  · calc
      Module.finrank K (standardLubinTateLevelField hπ n) =
          Nat.card (standardLubinTateUnitParameter F n) := by
        rw [standardLubinTateLevelField_finrank hπ n,
          standardLubinTateUnitParameter_natCard F n]
      _ ≤ Nat.card (Gal((standardLubinTateLevelField hπ n) / K)) :=
        Nat.card_le_card_of_injective
          (standardLubinTateUnitParameterToGal F hπ n)
          (standardLubinTateUnitParameterToGal_injective F hπ n)

/-- The parameter-to-Galois map is bijective. -/
theorem standardLubinTateUnitParameterToGal_bijective
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    Function.Bijective
      (standardLubinTateUnitParameterToGal F hπ n) := by
  apply (Nat.bijective_iff_injective_and_card
    (standardLubinTateUnitParameterToGal F hπ n)).2
  refine
    ⟨standardLubinTateUnitParameterToGal_injective F hπ n, ?_⟩
  rw [standardLubinTateUnitParameter_natCard F n,
    ← standardLubinTateLevelField_finrank hπ n,
    ← standardLubinTateLevelField_natCard_gal hπ n]

/-- Every standard finite Lubin--Tate level field is Galois over its base
field. -/
theorem standardLubinTateLevelField_isGalois
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    IsGalois K (standardLubinTateLevelField hπ n) := by
  let : FiniteDimensional K (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  exact IsGalois.of_card_aut_eq_finrank K
    (standardLubinTateLevelField hπ n)
    (standardLubinTateLevelField_natCard_gal hπ n)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_CompletedIterates
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHom_apply_ofAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_mul_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeries_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_expSeries_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_one_ofWithZeroValuation _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
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

/-- The `i`-fold standard polynomial iterate, evaluated at the primitive
point in the complete level valuation ring. -/
noncomputable def standardLubinTatePrimitivePointIterateInteger
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n i : ℕ) :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  Polynomial.eval₂
    (standardLubinTateLevelCoefficientHom hπ n)
    (standardLubinTatePrimitivePointInteger hπ n)
    (standardLubinTatePolynomialIterate F π i)

/-- The zeroth iterate is the primitive point itself. -/
@[simp]
theorem standardLubinTatePrimitivePointIterateInteger_zero
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTatePrimitivePointIterateInteger hπ n 0 =
      standardLubinTatePrimitivePointInteger hπ n := by
  simp [standardLubinTatePrimitivePointIterateInteger]

/-- One more iterate is evaluation of `y ↦ y ^ q + π y`. -/
theorem standardLubinTatePrimitivePointIterateInteger_succ
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n i : ℕ) :
    standardLubinTatePrimitivePointIterateInteger hπ n (i + 1) =
      standardLubinTatePrimitivePointIterateInteger hπ n i ^
          Nat.card F.residueField +
        standardLubinTateLevelCoefficientHom hπ n π *
          standardLubinTatePrimitivePointIterateInteger hπ n i := by
  rw [standardLubinTatePrimitivePointIterateInteger,
    standardLubinTatePolynomialIterate_succ,
    Polynomial.eval₂_comp,
    standardLubinTatePolynomial_formula,
    Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_mul,
    Polynomial.eval₂_C]
  simp only [Polynomial.eval₂_X, standardLubinTatePrimitivePointIterateInteger]

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_PrimitiveDisplacement
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHom_apply_ofAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_mul_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeries_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_expSeries_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_one_ofWithZeroValuation _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Displacements of primitive Lubin--Tate points

For the primitive point at level `n + 1`, a unit whose first nontrivial
principal-unit layer is `k` displaces that point by an element of normalized
additive valuation `q ^ k`.

The analytic input is proved here rather than assumed.  A unit scalar
endomorphism is `X` times an invertible power series.  Likewise
`F(X, Y) - X` for the standard formal group is `Y` times an invertible
two-variable power series.  Consequently neither operation changes the
valuation of the topologically nilpotent input that it multiplies.
-/

noncomputable section

open scoped Polynomial PowerSeries

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

section FormalFactors

/-- The standard formal-group difference `F(X,Y) - X` is divisible by
`Y`. -/
theorem standardLubinTateFormalGroup_rightDisplacement_dvd
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    (MvPowerSeries.X (1 : Fin 2) :
        MvPowerSeries (Fin 2) F.valuationSubring) ∣
      SameUniformizer.standardFormalGroupPowerSeries hπ -
        MvPowerSeries.X (0 : Fin 2) := by
  rw [MvPowerSeries.X_dvd_iff]
  intro d hd
  let D :=
    SameUniformizer.standardFormalGroupPowerSeries hπ -
      MvPowerSeries.X (0 : Fin 2)
  have hhas :
      MvPowerSeries.HasSubst
        (![(PowerSeries.X : PowerSeries F.valuationSubring), 0] :
          Fin 2 → PowerSeries F.valuationSubring) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i
    · simpa only [Fin.zero_eta, Matrix.cons_val_zero,
        PowerSeries.X_apply] using
        (MvPowerSeries.constantCoeff_X
          (R := F.valuationSubring) ())
    · simp
  have hsubst :
      MvPowerSeries.subst
          ![(PowerSeries.X : PowerSeries F.valuationSubring), 0] D =
        0 := by
    dsimp only [D]
    rw [MvPowerSeries.subst_sub hhas]
    have hformal :
        MvPowerSeries.subst
            ![(PowerSeries.X : PowerSeries F.valuationSubring), 0]
            (SameUniformizer.standardFormalGroupPowerSeries hπ) =
          PowerSeries.X := by
      simpa only [PowerSeries.X_apply] using
        SameUniformizer.standardFormalGroupPowerSeries_subst_X_zero hπ
    rw [hformal, MvPowerSeries.subst_X hhas]
    exact sub_self _
  have hcoeff :=
    congrArg (PowerSeries.coeff (d 0)) hsubst
  rw [coeff_subst_X_zero D d hd] at hcoeff
  simpa [D] using hcoeff

/-- The quotient of `F(X,Y) - X` by `Y`. -/
noncomputable def standardLubinTateFormalGroupRightDisplacementFactor
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    MvPowerSeries (Fin 2) F.valuationSubring :=
  Classical.choose
    (standardLubinTateFormalGroup_rightDisplacement_dvd hπ)

end FormalFactors

section AnalyticValuation

noncomputable local instance
    standardLubinTatePrimitiveDisplacementTargetWithIdeal
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    WithIdeal
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring where
  i := (standardLubinTateLevelCompleteDVF hπ n).maximalIdeal

/-- The analytic value of `[π^k]` is the evaluated standard polynomial
iterate. -/
theorem standardLubinTateEndomorphismValue_uniformizer_pow
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) :
    standardLubinTateEndomorphismValue hπ n (π ^ k) =
      standardLubinTatePrimitivePointIterateInteger hπ n k := by
  exact
    standardLubinTateEndomorphismEvalAt_uniformizer_pow hπ n
      (standardLubinTatePrimitivePointInteger hπ n)
      (standardLubinTatePrimitivePointInteger_hasEval hπ n) k

/-- Every evaluated standard iterate before the annihilating level is
topologically nilpotent. -/
theorem standardLubinTatePrimitivePointIterateInteger_hasEval
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) :
    PowerSeries.HasEval
      (standardLubinTatePrimitivePointIterateInteger hπ n k) := by
  rw [← standardLubinTateEndomorphismValue_uniformizer_pow hπ n k]
  exact standardLubinTateEndomorphismValue_hasEval hπ n (π ^ k)

end AnalyticValuation

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_FieldUnitFactors
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralGroup_discrete _root_.OAI.PrimeDegreePackets.logSubgroup_discrete _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.orderedLogSubgroup_discrete _root_.OAI.PrimeDegreePackets.periodGroup_discrete _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.periodSubmodule_discrete _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.SUnitGroup.instDiscreteTopology_fullLogLattice _root_.SUnitGroup.instDiscreteTopology_reducedLogLattice _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.instDiscreteTopology_extendedFullLogLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite and uniformizer factors of the field-unit group

This file isolates the two factors of the field-unit structure theorem which do not depend on
the structure theorem for first principal units.  The Teichmuller factor is
the cyclic group of order `q - 1`, with its (necessarily discrete) topology.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

variable {K : Type u} [Field K]

/-- The Teichmuller roots form, algebraically and topologically, the cyclic
group of order `q - 1`, where `q` is the residue-field cardinality. -/
noncomputable def residueRootsOfUnityContinuousMulEquivZMod
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F
    Multiplicative (ZMod (Nat.card F.residueField - 1)) ≃ₜ*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F := by
  letI : Valued K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F
  rw [← Nat.card_units F.residueField]
  let e : Multiplicative (ZMod (Nat.card F.residueFieldˣ)) ≃*
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F :=
    (zmodCyclicMulEquiv
      (G := F.residueFieldˣ) (inferInstance : IsCyclic F.residueFieldˣ)).trans
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F).symm
  haveI : Finite (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :=
    Finite.of_equiv F.residueFieldˣ
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F).symm.toEquiv
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_LevelAbelian
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isCompleteDiscrete _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHom_apply_ofAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_mul_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeries_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_expSeries_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_one_ofWithZeroValuation _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Abelian standard Lubin--Tate level fields

The finite unit parameter group

`O_F^* / U_F^(n + 1)`

acts multiplicatively and faithfully on the primitive level-`n + 1`
division point.  The finite-level automorphism calculation identifies this
parameter group bijectively with the full Galois group.  We package that
identification as a multiplicative equivalence and transport commutativity
to the Galois group.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The multiplicative map from finite unit parameters to automorphisms of
the standard Lubin--Tate level field. -/
noncomputable def standardLubinTateUnitParameterToGalHom
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateUnitParameter F n →*
      Gal((standardLubinTateLevelField hπ n) / K) where
  toFun := standardLubinTateUnitParameterToGal F hπ n
  map_one' := standardLubinTateUnitParameterToGal_one F hπ n
  map_mul' := standardLubinTateUnitParameterToGal_mul F hπ n

/-- The homomorphism has the original parameter-to-Galois map as its
underlying function. -/
@[simp]
theorem standardLubinTateUnitParameterToGalHom_apply
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterToGalHom F hπ n a =
      standardLubinTateUnitParameterToGal F hπ n a :=
  rfl

/-- Finite unit parameters are multiplicatively equivalent to the full
Galois group of the standard level field. -/
noncomputable def standardLubinTateUnitParameterEquivGal
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateUnitParameter F n ≃*
      Gal((standardLubinTateLevelField hπ n) / K) :=
  MulEquiv.ofBijective
    (standardLubinTateUnitParameterToGalHom F hπ n)
    (by
      change Function.Bijective
        (standardLubinTateUnitParameterToGal F hπ n)
      exact standardLubinTateUnitParameterToGal_bijective F hπ n)

/-- The multiplicative equivalence evaluates as the original explicit
parameter automorphism. -/
@[simp]
theorem standardLubinTateUnitParameterEquivGal_apply
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : standardLubinTateUnitParameter F n) :
    standardLubinTateUnitParameterEquivGal F hπ n a =
      standardLubinTateUnitParameterToGal F hπ n a :=
  rfl

/-- The inverse of the explicit unit-parameter automorphism acts on the
chosen primitive generator through the inverse Lubin--Tate unit action.

This is the pointwise `[u⁻¹]` target needed for the later comparison with
the actual local Artin map; it does not identify the two maps merely from
their kernels. -/
@[simp]
theorem standardLubinTateUnitParameterEquivGal_inv_class_apply_gen
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (u : F.valuationSubringˣ) :
    (standardLubinTateUnitParameterEquivGal F hπ n
        (standardLubinTateUnitParameterClass F n u))⁻¹
        (standardLubinTateLevelPowerBasis hπ n).gen =
      standardLubinTatePrimitiveLevelAction hπ n u⁻¹ := by
  have hgal :
      (standardLubinTateUnitParameterEquivGal F hπ n
          (standardLubinTateUnitParameterClass F n u))⁻¹ =
        standardLubinTateUnitParameterEquivGal F hπ n
          (standardLubinTateUnitParameterClass F n u)⁻¹ :=
    ((standardLubinTateUnitParameterEquivGal F hπ n).map_inv _).symm
  rw [hgal]
  have hclass :
      (standardLubinTateUnitParameterClass F n u)⁻¹ =
        standardLubinTateUnitParameterClass F n u⁻¹ :=
    ((standardLubinTateUnitParameterClass F n).map_inv u).symm
  rw [hclass, standardLubinTateUnitParameterEquivGal_apply]
  change
    standardLubinTateUnitParameterAlgEquiv F hπ n
        (standardLubinTateUnitParameterClass F n u⁻¹)
        (standardLubinTateLevelPowerBasis hπ n).gen =
      standardLubinTatePrimitiveLevelAction hπ n u⁻¹
  rw [standardLubinTateUnitParameterAlgEquiv_apply_gen]
  apply Subtype.ext
  rw [standardLubinTateUnitParameterLevelRoot_coe,
    standardLubinTatePrimitiveLevelAction_coe,
    standardLubinTateUnitParameterRoot_class]

/-- The full Galois group of a standard finite Lubin--Tate level is
commutative. -/
theorem standardLubinTateLevelField_gal_comm
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ)
    (σ τ : Gal((standardLubinTateLevelField hπ n) / K)) :
    σ * τ = τ * σ := by
  let e := standardLubinTateUnitParameterEquivGal F hπ n
  apply e.symm.injective
  calc
    e.symm (σ * τ) = e.symm σ * e.symm τ := e.symm.map_mul σ τ
    _ = e.symm τ * e.symm σ := mul_comm _ _
    _ = e.symm (τ * σ) := (e.symm.map_mul τ σ).symm

/-- The Galois group of the standard level field is a commutative group. -/
instance standardLubinTateLevelField_isMulCommutative
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    IsMulCommutative
      (Gal((standardLubinTateLevelField hπ n) / K)) :=
  ⟨⟨standardLubinTateLevelField_gal_comm F hπ n⟩⟩

/-- Every standard finite Lubin--Tate level is abelian Galois over its base
local field. -/
instance standardLubinTateLevelField_isAbelianGalois
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    IsAbelianGalois K (standardLubinTateLevelField hπ n) where
  toIsGalois :=
    standardLubinTateLevelField_isGalois (F := F) hπ n
  toIsMulCommutative :=
    standardLubinTateLevelField_isMulCommutative F hπ n

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_r9ad29a_1
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsNonarchimedeanLocalField
/-- The valuation ring of the absolute-value completion at `q`, identified
with the standard p-adic integer ring `ℤ_q`. -/
noncomputable def rationalFinitePlaceCompletionIntegerRingEquivPadicInt
    (q : Nat.Primes) :
    𝒪[(HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion] ≃+*
      ℤ_[q.1] := by
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    RayClass.rationalPrime q
  let vQ := HeightOneSpectrum.adicAbv ℚ v
  let eConcreteIntegers :
      𝒪[vQ.Completion] ≃+*
        v.adicCompletionIntegers ℚ :=
    finitePlaceCompletionIntegerRingEquiv v
  exact
    eConcreteIntegers.trans
      (PadicInt.adicCompletionIntegersEquiv
        (𝓞 ℚ) q).symm.toRingEquiv

/-- The absolute-value completion at the rational prime `q`, identified
with the standard field `ℚ_q`. -/
noncomputable def rationalFinitePlaceCompletionRingEquivPadic
    (q : Nat.Primes) :
    (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion ≃+*
      ℚ_[q.1] :=
  IsFractionRing.ringEquivOfRingEquiv
    (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Padic_UnitDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalFieldTheory.localIntegerValuation_residueFinite _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unit decomposition of the p-adic integers

This file constructs the reusable topological decomposition of
`ℤ_[p]ˣ` into its finite factor and its principal `p`-adic factor.
-/

open scoped Topology

noncomputable section

namespace LocalFieldTheory
namespace Padic

open scoped WithZero
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

local instance padicDVRResidueFinite
    (p : ℕ) [Fact p.Prime] :
    Finite
      (IsLocalRing.ResidueField
        (padicDVRValuation p).valuationSubring) := by
  simpa [padicCompleteDVF] using
    padicCompleteDVF_residueField_finite p

/-- The residue field of the valuation-theoretic presentation of `ℚ_[p]`
is canonically `ZMod p`. -/
noncomputable def padicResidueEquivZMod
    (p : ℕ) [Fact p.Prime] :
    (LocalField.ofWithZeroValuation
      (padicDVRValuation p)).residueField ≃+* ZMod p :=
  (IsLocalRing.ResidueField.mapEquiv
      (padicIntEquivValuationSubring p)).symm.trans
    (padicIntResidueFieldEquivZMod p)

theorem padic_residueCharacteristic_eq
    (p : ℕ) [Fact p.Prime] :
    (LocalField.ofWithZeroValuation
      (padicDVRValuation p)).residueCharacteristic = p := by
  let F :=
    LocalField.ofWithZeroValuation
      (padicDVRValuation p)
  let e : F.residueField ≃+* ZMod p :=
    padicResidueEquivZMod p
  have : CharP F.residueField p := by
    constructor
    intro n
    rw [← e.injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff (ZMod p) p n
  exact ringChar.eq F.residueField p

theorem padic_finrank_eq_one
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v :=
      LocalField.mixedWithZeroValuationContext v
    Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p] = 1 := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  let : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  dsimp only
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  refine ⟨RingHom.injective _, ?_⟩
  let direct : Valued ℚ_[p] (WithZero (Multiplicative ℤ)) :=
    Valued.mk' v
  let restricted : Valued ℚ_[p] F.mrangeValueGroup :=
    CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  have hrestricted :
      @IsUniformInducing
        ℚ_[F.residueCharacteristic] ℚ_[p]
        inferInstance restricted.toUniformSpace
        (algebraMap ℚ_[F.residueCharacteristic] ℚ_[p]) := by
    let : Valued ℚ_[p] F.mrangeValueGroup := restricted
    change IsUniformInducing
      (fun x : ℚ_[F.residueCharacteristic] =>
        ((F.qpadicNumbersEquivQpadicClosureSubfield x :
          F.qpadicClosureSubfield) : ℚ_[p]))
    exact isUniformEmbedding_subtype_val.isUniformInducing.comp
      F.qpadicNumbersToQpadicClosureSubfield_isUniformInducing
  have huniform :
      direct.toUniformSpace = restricted.toUniformSpace := by
    change
      (Valued.mk' v).toUniformSpace =
        (CompleteDVF.mrangeRestrictValued
          (WithZeroValuationTopology.completeDVF v)).toUniformSpace
    exact WithZeroValuationTopology.valuedMk_uniformSpace_eq_mrangeRestrict v
  have hUR :
      (PseudoMetricSpace.toUniformSpace : UniformSpace ℚ_[p]) =
        restricted.toUniformSpace :=
    (padicDVRValued_uniformSpace_eq_standard p).symm.trans huniform
  have hclosed :
      @IsClosed ℚ_[p] restricted.toTopologicalSpace
        (Set.range
          (algebraMap ℚ_[F.residueCharacteristic] ℚ_[p])) := by
    have hembedding :
        @IsUniformEmbedding
          ℚ_[F.residueCharacteristic] ℚ_[p]
          inferInstance restricted.toUniformSpace
          (algebraMap ℚ_[F.residueCharacteristic] ℚ_[p]) :=
      ⟨hrestricted, RingHom.injective _⟩
    exact hembedding.isClosedEmbedding.isClosed_range
  have hratDense :
      @DenseRange ℚ_[p] restricted.toTopologicalSpace
        ℚ ((↑) : ℚ → ℚ_[p]) := by
    have htop :
        (PseudoMetricSpace.toUniformSpace :
          UniformSpace ℚ_[p]).toTopologicalSpace =
            restricted.toTopologicalSpace :=
      congrArg (fun U : UniformSpace ℚ_[p] => U.toTopologicalSpace) hUR
    let P := fun T : TopologicalSpace ℚ_[p] =>
      @DenseRange ℚ_[p] T ℚ ((↑) : ℚ → ℚ_[p])
    exact (congrArg P htop).mp (Padic.denseRange_ratCast p)
  have hdense :
      @DenseRange ℚ_[p] restricted.toTopologicalSpace
        ℚ_[F.residueCharacteristic]
        (algebraMap ℚ_[F.residueCharacteristic] ℚ_[p]) := by
    apply DenseRange.of_comp
      (g := ((↑) : ℚ → ℚ_[F.residueCharacteristic]))
    have hcomp :
        (algebraMap ℚ_[F.residueCharacteristic] ℚ_[p]) ∘
            ((↑) : ℚ → ℚ_[F.residueCharacteristic]) =
          ((↑) : ℚ → ℚ_[p]) := by
      funext q
      simpa only [Function.comp_apply] using
        (map_ratCast
          (algebraMap ℚ_[F.residueCharacteristic] ℚ_[p]) q)
    rw [hcomp]
    exact hratDense
  rw [← Set.range_eq_univ]
  exact hclosed.closure_eq.symm.trans hdense.closure_range

/-- The free additive factor in the mixed-characteristic structure theorem
for `ℚ_[p]` is continuously equivalent to `ℤ_[p]`. -/
noncomputable def padicFreeContinuousAddEquiv
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v :=
      LocalField.mixedWithZeroValuationContext v
    let d := Module.finrank ℚ_[F.residueCharacteristic] ℚ_[p]
    (Fin d → ℤ_[F.residueCharacteristic]) ≃ₜ+ ℤ_[p] := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  letI : LocalField.MixedWithZeroValuationContext v :=
    LocalField.mixedWithZeroValuationContext v
  let q := F.residueCharacteristic
  let d := Module.finrank ℚ_[q] ℚ_[p]
  change (Fin d → ℤ_[q]) ≃ₜ+ ℤ_[p]
  have hq : q = p := by
    simpa [q, F, v] using padic_residueCharacteristic_eq p
  have hd : d = 1 := by
    simpa [d, F, v] using padic_finrank_eq_one p
  exact padicFreeContinuousAddEquivOfEq p q d hq hd

/-- The topology on the first principal-unit group induced directly from
the valuation topology on `ℚ_[p]`. -/
@[implicit_reducible]
noncomputable def padicPrincipalUnitDirectTopology
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    TopologicalSpace
      (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1) := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  letI : Valued ℚ_[p] (WithZero (Multiplicative ℤ)) :=
    Valued.mk' v
  exact inferInstance

/-- The standard topology on the first principal-unit group of `ℚ_[p]`. -/
@[implicit_reducible]
noncomputable def padicPrincipalUnitStandardTopology
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    let F := LocalField.ofWithZeroValuation v
    TopologicalSpace
      (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1) := by
  exact inferInstance

/-- The directly induced valuation topology agrees with the standard topology
on the first principal-unit group of `ℚ_[p]`. -/
theorem padicPrincipalUnitDirectTopology_eq_standard
    (p : ℕ) [Fact p.Prime] :
    padicPrincipalUnitDirectTopology p =
      padicPrincipalUnitStandardTopology p := by
  let v := padicDVRValuation p
  let F := LocalField.ofWithZeroValuation v
  let U := CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1
  let liftTopology := fun T : TopologicalSpace ℚ_[p] => by
    letI : TopologicalSpace ℚ_[p] := T
    exact (inferInstance : TopologicalSpace U)
  unfold padicPrincipalUnitDirectTopology
    padicPrincipalUnitStandardTopology
  change
    liftTopology (Valued.mk' v).toTopologicalSpace =
      liftTopology PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact congrArg liftTopology
    (congrArg (fun U : UniformSpace ℚ_[p] => U.toTopologicalSpace)
      (padicDVRValued_uniformSpace_eq_standard p))

end Padic
end LocalFieldTheory
end
end


