-- Prove2me | Definitions.Def_OAIQ244Duke090
-- name    : OAIQ244Duke090
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T01:47:54.918468+00:00
-- url     : https://prove2.me/theorems/d015c6f2-5194-4e5c-9128-7de2705e5d6a
-- title:
--   Definitions bundle OAIQ244Duke090 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 50 declarations of OpenAI's Lean: 20 definitions, 1 instance and 29 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.compRestrictNormalHomInfiniteGlobalArtinNaturalityDataOfNumberField`, `GlobalClassFieldTheory.Reciprocity.globalArtinFiniteSupport`, `GlobalClassFieldTheory.Reciprocity.globalArtinMonoidHomOfNumberField`, `GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteIntersection`, `GlobalClassFieldTheory.Reciprocity.rationalAbsoluteGaloisRestrictionToCyclotomicZHat`, `GlobalClassFieldTheory.Reciprocity.rationalAbstractExtensionIdeleClassEquiv`, `GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicDegreeData`, `GlobalClassFieldTheory.Reciprocity.rationalExtensionNormComparison`, `GlobalClassFieldTheory.Reciprocity.rationalFixedFieldIdeleClassAdditiveType`, `GlobalClassFieldTheory.Reciprocity.rationalFixedFieldIdeleClassType`, `GlobalClassFieldTheory.Reciprocity.rationalFixedFieldInclusionComparison`, `GlobalClassFieldTheory.Reciprocity.rationalRelativeFixedFieldNormCohomologyComparison`, `GlobalClassFieldTheory.Reciprocity.rationalRelativeFixedFieldNormComparison`, `GlobalClassFieldTheory.Reciprocity.rationalRelativeFixedFieldNormPreimageComparison`, `GlobalClassFieldTheory.Reciprocity.rationalRelativeNormClassNormSource`, `GlobalClassFieldTheory.Reciprocity.rationalRelativeNormClassNormTarget`, `GlobalClassFieldTheory.Reciprocity.rationalRelativeNormComparison`, `GlobalClassFieldTheory.Reciprocity.rationalRelativeNormSource`, `GlobalClassFieldTheory.Reciprocity.rationalRelativeNormTarget`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification`, `GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange`, `GlobalClassFieldTheory_Reciprocity_GlobalArtinFiniteSupportApproximation`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtension`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionAction`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionNorm`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitNormQuotient`, `GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalProduct`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke085` and `OAIQ244Duke086` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke093` and `OAIQ244Duke094`.
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
import Definitions.Def_OAIQ244Duke085
import Definitions.Def_OAIQ244Duke086

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.inertiaImage_normalInstance _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.finiteGaloisExtensionQuotientOfEmbedding_finite _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.finiteUnramifiedNormQuotient _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.infiniteCongruenceSubgroupFiniteIndex _root_.RayClass.approximationCompletionTopologicalSpace _root_.RayClass.congruenceSubgroupFiniteIndex _root_.RayClass.ideleCongruenceSupPrincipalFiniteIndex _root_.RayClass.narrowInfiniteCongruenceSubgroupFiniteIndex _root_.RayClass.ordinaryIdealClassSubgroupFiniteIndex _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding_bundle_finite _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.abstractReciprocityEquiv_apply_of _root_.ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedFrobeniusInM_restriction _root_.ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedLowerGenerator_inclusion_restriction _root_.ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedRestrictionEquiv_lowerGenerator _root_.ClassFormation.DegreeData.abstractReciprocity_normResidueSymbol _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_mul _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusConjugationEquiv_mk _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusConjugationLift_coe _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusConjugationLift_exponent _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerLift_coe _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerLift_exponent _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerMap_mk _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeEquiv_unramifiedFrobenius _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_frobenius _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_mk _root_.ClassFormation.DegreeData.fixedFieldNormalizedDegree_generator _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegree_generator _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusLiftOfTotallyRamified _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusExponent_powerOfDegreeOne _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusFixedFieldQuotientEquiv_mk _root_.ClassFormation.DegreeData.frobeniusFixedFieldToClosure_apply _root_.ClassFormation.DegreeData.frobeniusFixedField_normalizedDegreeEquiv_apply _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusMul_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.frobeniusPowerSum_coe _root_.ClassFormation.DegreeData.frobeniusQuotientAction_mk _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.DegreeData.maximalUnramifiedExtensionRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.DegreeData.maximalUnramifiedRestriction_frobenius _root_.ClassFormation.DegreeData.mem_frobeniusFixedField_iff _root_.ClassFormation.DegreeData.mem_frobeniusFixedSubgroupWithin_iff _root_.ClassFormation.DegreeData.normResidueSymbol_finiteReciprocityHom _root_.ClassFormation.DegreeData.transferNormNaturalityAbelianizedReciprocity_of _root_.ClassFormation.DegreeData.transferNormNaturalityFrobeniusIntermediateEquiv_mk _root_.ClassFormation.DegreeData.transferNormNaturalityIntermediateToFrobeniusSubgroup_apply _root_.ClassFormation.DegreeData.transferNormNaturalityTransferFrobeniusLift_coe _root_.ClassFormation.DegreeData.transferNormNaturalityTransferNormOrbitEquiv_mk _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.unramifiedReciprocityEquiv_apply _root_.ClassFormation.ValuationData.unramifiedReciprocity_equiv_of_generator_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractFixedFieldIdeleClassEquivFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.restrictNormalHom_rationalCyclotomicZHatGlobalArtin _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.baseFixingCosetToAlgHom_mk _root_.LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply _root_.LocalClassFieldTheory.finiteGaloisNormConjugationOfEmbeddings_finiteNormClass_baseUnit _root_.LocalClassFieldTheory.finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.localBaseValuation_baseFieldUnitsEquiv _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.ClassFormation.DegreeData.inertiaConjugationCosetEquiv_mk _root_.infinitePlace_mult_smul
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Base change of the rational cyclotomic `ZHat`-extension

The rational cyclotomic `ZHat`-extension lives inside the fixed separable
closure of `ℚ`.  To form its compositum with an arbitrary number field, we first
embed that number field into the same separable closure.  The
intersection degree below is the normalization integer

`f_K = [K ∩ ℚ̃ : ℚ]`.

All fields in this file are the actual mathlib intermediate fields in
`SeparableClosure ℚ`; no abstract copy of the compositum or of its
Galois group is introduced.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped Topology
open AlgebraicNumberTheory
open ClassFormation
open KummerTheory

/-- The lifted cyclotomic `ZHat`-field is normal with its canonical
`IntermediateField` algebra structure.  This is the normality used by
restriction maps out of the fixed rational separable closure. -/
theorem rationalCyclotomicZHatField_normal :
    @Normal ℚ rationalCyclotomicZHatField _ _
      rationalCyclotomicZHatField.algebra' := by
  exact @IsGalois.to_normal
    ℚ _ rationalCyclotomicZHatField _
      rationalCyclotomicZHatField.algebra'
    (@IsAbelianGalois.of_algHom
      ℚ rationalCyclotomicZHatField rationalCyclotomicTorsionFixedField
      _ _ rationalCyclotomicZHatField.algebra' _ _
      (IntermediateField.liftAlgEquiv
        rationalCyclotomicTorsionFixedField).symm.toAlgHom
      KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois).toIsGalois

/-- Restriction from the actual absolute Galois group of `ℚ` to the
cyclotomic `ZHat`-extension. -/
noncomputable def
    rationalAbsoluteGaloisRestrictionToCyclotomicZHat :
    (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) →ₜ*
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) where
  toMonoidHom :=
    @AlgEquiv.restrictNormalHom
      ℚ _ (SeparableClosure ℚ) _ _
      rationalCyclotomicZHatField _
      rationalCyclotomicZHatField.algebra' _ _
      rationalCyclotomicZHatField_normal
  continuous_toFun := by
    let : @Normal ℚ rationalCyclotomicZHatField _ _
        rationalCyclotomicZHatField.algebra' :=
      rationalCyclotomicZHatField_normal
    exact
      InfiniteGalois.restrictNormalHom_continuous
        rationalCyclotomicZHatField

/-- The actual global degree datum
`d : Gal(ℚ̄/ℚ) → Multiplicative ZHat`, obtained by restriction to the
cyclotomic `ZHat`-extension. -/
noncomputable def rationalCyclotomicDegreeData :
    DegreeData
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  degree :=
    (ContinuousMonoidHom.toContinuousMonoidHom
      rationalCyclotomicZHatFieldGalEquivZHat).comp
        rationalAbsoluteGaloisRestrictionToCyclotomicZHat
  degree_surjective :=
    by
      let : @Normal ℚ rationalCyclotomicZHatField _ _
          rationalCyclotomicZHatField.algebra' :=
        rationalCyclotomicZHatField_normal
      exact
        rationalCyclotomicZHatFieldGalEquivZHat.surjective.comp
          (AlgEquiv.restrictNormalHom_surjective
            (F := ℚ)
            (K₁ := rationalCyclotomicZHatField)
            (E := SeparableClosure ℚ))

/-- The inertia subgroup of the actual cyclotomic degree datum is
literally the subgroup fixing the cyclotomic `ZHat`-extension. -/
theorem rationalCyclotomicDegreeData_inertia :
    rationalCyclotomicDegreeData.inertia =
      RamificationTheory.closedFixingSubgroup ℚ (SeparableClosure ℚ)
        rationalCyclotomicZHatField := by
  let : @Normal ℚ rationalCyclotomicZHatField _ _
      rationalCyclotomicZHatField.algebra' :=
    rationalCyclotomicZHatField_normal
  let r := rationalAbsoluteGaloisRestrictionToCyclotomicZHat
  have hrker : r.toMonoidHom.ker =
      rationalCyclotomicZHatField.fixingSubgroup := by
    change
      (@AlgEquiv.restrictNormalHom
        ℚ _ (SeparableClosure ℚ) _ _
        rationalCyclotomicZHatField _
        rationalCyclotomicZHatField.algebra' _ _
        rationalCyclotomicZHatField_normal).ker =
          rationalCyclotomicZHatField.fixingSubgroup
    exact
      @IntermediateField.restrictNormalHom_ker
        ℚ (SeparableClosure ℚ) _ _ _
        rationalCyclotomicZHatField
        rationalCyclotomicZHatField_normal
  ext σ
  change
    σ ∈ rationalCyclotomicDegreeData.inertia ↔
      σ ∈ RamificationTheory.closedFixingSubgroup ℚ (SeparableClosure ℚ)
        rationalCyclotomicZHatField
  rw [rationalCyclotomicDegreeData.mem_inertia_iff]
  change
    rationalCyclotomicZHatFieldGalEquivZHat
        (r σ) =
        1 ↔
      σ ∈ rationalCyclotomicZHatField.fixingSubgroup
  constructor
  · intro hσ
    have hrestrict :
        r σ =
          1 := by
      apply rationalCyclotomicZHatFieldGalEquivZHat.injective
      simpa using hσ
    have hker :
        σ ∈ r.toMonoidHom.ker :=
      hrestrict
    exact hrker ▸ hker
  · intro hσ
    have hker :
        σ ∈ r.toMonoidHom.ker := by
      rw [hrker]
      exact hσ
    change
      rationalCyclotomicZHatFieldGalEquivZHat
          (r σ) =
        1
    have hzero : r σ = 1 :=
      MonoidHom.mem_ker.mp hker
    rw [hzero, map_one]

/-- For every abstract rational fixed field `F`, the field fixed by
its cyclotomic inertia is the genuine compositum `Fℚ̃` in
`SeparableClosure ℚ`. -/
theorem
    rationalCyclotomicDegreeData_fixedField_fieldInertia
    (H : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicDegreeData.fieldInertia H) =
      LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H ⊔
        rationalCyclotomicZHatField := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H
  have hsubgroup :
      (rationalCyclotomicDegreeData.fieldInertia H).toSubgroup =
        (F ⊔ rationalCyclotomicZHatField).fixingSubgroup := by
    calc
      (rationalCyclotomicDegreeData.fieldInertia H).toSubgroup =
          H.toSubgroup ⊓
            rationalCyclotomicDegreeData.inertia.toSubgroup :=
        rfl
      _ =
          H.toSubgroup ⊓
            rationalCyclotomicZHatField.fixingSubgroup := by
        rw [rationalCyclotomicDegreeData_inertia]
        rfl
      _ =
          F.fixingSubgroup ⊓
            rationalCyclotomicZHatField.fixingSubgroup := by
        rw [InfiniteGalois.fixingSubgroup_fixedField H]
      _ =
          (F ⊔ rationalCyclotomicZHatField).fixingSubgroup :=
        IntermediateField.fixingSubgroup_sup.symm
  change
    IntermediateField.fixedField
        (rationalCyclotomicDegreeData.fieldInertia H).toSubgroup =
      F ⊔ rationalCyclotomicZHatField
  rw [hsubgroup]
  exact
    InfiniteGalois.fixedField_fixingSubgroup
      (F ⊔ rationalCyclotomicZHatField)

/-- Restricting a closed subgroup of the rational absolute Galois group
to the cyclotomic `ZHat`-extension gives exactly the subgroup fixing the
intersection with its concrete fixed field. -/
theorem
    rationalAbsoluteGaloisRestriction_image_eq_intersection_fixingSubgroup
    (H : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    H.toSubgroup.map
        rationalAbsoluteGaloisRestrictionToCyclotomicZHat.toMonoidHom =
      (((LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H) ⊓
        rationalCyclotomicZHatField).restrict
        (show
          LocalClassFieldTheory.abstractFixedField
                ℚ (SeparableClosure ℚ) H ⊓
              rationalCyclotomicZHatField ≤
            rationalCyclotomicZHatField from
          inf_le_right)).fixingSubgroup := by
  let _ : T2Space
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
    krullTopology_t2
  let r := rationalAbsoluteGaloisRestrictionToCyclotomicZHat
  let R : ClosedSubgroup
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
    { toSubgroup := H.toSubgroup.map r
      isClosed' := by
        change IsClosed (r '' H.carrier)
        exact
          (H.isClosed'.isCompact.image
            r.continuous).isClosed }
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H
  let J : IntermediateField ℚ (SeparableClosure ℚ) :=
    F ⊓ rationalCyclotomicZHatField
  let hJT : J ≤ rationalCyclotomicZHatField :=
    inf_le_right
  let E : IntermediateField ℚ rationalCyclotomicZHatField :=
    J.restrict hJT
  have hE :
      E = IntermediateField.fixedField R.toSubgroup := by
    apply
      (IntermediateField.lift_injective
        rationalCyclotomicZHatField)
    calc
      IntermediateField.lift E = J :=
        IntermediateField.lift_restrict hJT
      _ =
          IntermediateField.lift
            (IntermediateField.fixedField R.toSubgroup) := by
        dsimp only [F, J, R, r]
        change
          IntermediateField.fixedField H.toSubgroup ⊓
              rationalCyclotomicZHatField =
            IntermediateField.lift
              (IntermediateField.fixedField
                (Subgroup.map
                  (@AlgEquiv.restrictNormalHom
                    ℚ _ (SeparableClosure ℚ) _ _
                    rationalCyclotomicZHatField _
                    rationalCyclotomicZHatField.algebra' _ _
                    rationalCyclotomicZHatField_normal)
                  H.toSubgroup))
        exact
          @InfiniteGalois.restrict_fixedField
            ℚ (SeparableClosure ℚ) _ _ _ H.toSubgroup
            rationalCyclotomicZHatField
            rationalCyclotomicZHatField_normal
  have hfix :
      E.fixingSubgroup = R.toSubgroup := by
    rw [hE]
    exact InfiniteGalois.fixingSubgroup_fixedField R
  exact hfix.symm

/-- The degree image of a closed subgroup of the rational absolute
Galois group is the subgroup of `ZHat` fixing the intersection of its
concrete fixed field with the actual cyclotomic `ZHat`-extension. -/
theorem
    rationalCyclotomicDegreeData_fieldImage_eq_intersection_fixingSubgroup :
    ∀ H : ClosedSubgroup
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ),
      rationalCyclotomicDegreeData.fieldImage H =
        (((LocalClassFieldTheory.abstractFixedField
              ℚ (SeparableClosure ℚ) H) ⊓
            rationalCyclotomicZHatField).restrict
          (show
            LocalClassFieldTheory.abstractFixedField
                  ℚ (SeparableClosure ℚ) H ⊓
                rationalCyclotomicZHatField ≤
              rationalCyclotomicZHatField from
            inf_le_right)).fixingSubgroup.map
              rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom := by
  intro H
  rw [rationalCyclotomicDegreeData.fieldImage_eq_map]
  change
    H.toSubgroup.map
        (rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom.comp
          rationalAbsoluteGaloisRestrictionToCyclotomicZHat.toMonoidHom) =
      (((LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H) ⊓
          rationalCyclotomicZHatField).restrict
        (show
          LocalClassFieldTheory.abstractFixedField
                ℚ (SeparableClosure ℚ) H ⊓
              rationalCyclotomicZHatField ≤
            rationalCyclotomicZHatField from
          inf_le_right)).fixingSubgroup.map
        rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom
  rw [← Subgroup.map_map,
    rationalAbsoluteGaloisRestriction_image_eq_intersection_fixingSubgroup]

/-- For a finite abstract rational field, the residue degree supplied
by the actual cyclotomic degree datum is the degree of the concrete
intersection with the cyclotomic `ZHat`-extension. -/
theorem
    rationalCyclotomicDegreeData_residueDegree_eq_intersection_finrank
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    (H.residueDegree rationalCyclotomicDegreeData : ℕ) =
      Module.finrank ℚ
        ((LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field ⊓
          rationalCyclotomicZHatField :
            IntermediateField ℚ (SeparableClosure ℚ))) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let J : IntermediateField ℚ (SeparableClosure ℚ) :=
    F ⊓ rationalCyclotomicZHatField
  let hJT : J ≤ rationalCyclotomicZHatField :=
    inf_le_right
  let E : IntermediateField ℚ rationalCyclotomicZHatField :=
    J.restrict hJT
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : FiniteDimensional ℚ J :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion
        (show J ≤ F from inf_le_left)).toLinearMap
      (IntermediateField.inclusion
        (show J ≤ F from inf_le_left)).injective
  let : FiniteDimensional ℚ E :=
    ((IntermediateField.restrictAlgEquiv hJT).toLinearEquiv).finiteDimensional
  let HR :=
    H.toFiniteResidueAbstractField
      rationalCyclotomicDegreeData
  let : Finite
      (rationalCyclotomicDegreeData.residueQuotient
        H.field) :=
    HR.finiteResidueQuotient
  have hindex :
      (rationalCyclotomicDegreeData.fieldImage
        H.field).index =
          Module.finrank ℚ J := by
    rw [
      rationalCyclotomicDegreeData_fieldImage_eq_intersection_fixingSubgroup
        H.field]
    change
      (E.fixingSubgroup.map
        rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom).index =
          Module.finrank ℚ J
    calc
      (E.fixingSubgroup.map
          rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom).index =
          E.fixingSubgroup.index :=
        Subgroup.index_map_equiv E.fixingSubgroup
          rationalCyclotomicZHatFieldGalEquivZHat.toMulEquiv
      _ = Module.finrank ℚ E :=
        (IntermediateField.finrank_eq_fixingSubgroup_index rationalCyclotomicZHatField E).symm
      _ = Module.finrank ℚ J := by
        change Module.finrank ℚ (J.restrict hJT) = Module.finrank ℚ J
        exact
          ((IntermediateField.restrictAlgEquiv hJT).toLinearEquiv).finrank_eq.symm
  let :
      (rationalCyclotomicDegreeData.fieldImage
        HR.field).IsFiniteRelIndex
          (⊤ : Subgroup ZHatMul) :=
    ⟨by
      change
        (rationalCyclotomicDegreeData.fieldImage H.field).relIndex
            (⊤ : Subgroup ZHatMul) ≠ 0
      rw [Subgroup.relIndex_top_right, hindex]
      exact Module.finrank_pos.ne'⟩
  apply Nat.cast_injective (R := Cardinal)
  change
    ((H.residueDegree
      rationalCyclotomicDegreeData : ℕ) : Cardinal) =
        (Module.finrank ℚ J : Cardinal)
  rw [show
      H.residueDegree rationalCyclotomicDegreeData =
        HR.residueDegree from rfl,
    ← HR.residueDegreeCardinal_eq_coe,
    DegreeData.residueDegreeCardinal,
    relativeIndexCardinal_eq_index_of_finite
      (show rationalCyclotomicDegreeData.fieldImage HR.field ≤
        (⊤ : Subgroup ZHatMul) from le_top)]
  norm_cast
  simpa only [HR, FiniteAbstractField.toFiniteResidueAbstractField,
    Subgroup.relIndex_top_right] using hindex

/-- The degree of the intersection with the rational cyclotomic
`ZHat`-extension does not depend on the chosen embedding of an
abstract fixed field into `SeparableClosure ℚ`.

The proof extends the embedding to an automorphism of the separable
closure.  That automorphism preserves the cyclotomic `ZHat`-field
because the latter is normal over `ℚ`, and hence carries the canonical
intersection onto the intersection formed with the chosen image. -/
theorem
    abstractFixedFieldCyclotomicZHatIntersection_finrank_eq_of_embedding
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (ι :
      LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field →ₐ[ℚ]
        SeparableClosure ℚ) :
    Module.finrank ℚ
        ((ι.fieldRange ⊓ rationalCyclotomicZHatField :
          IntermediateField ℚ (SeparableClosure ℚ))) =
      Module.finrank ℚ
        ((LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field ⊓
          rationalCyclotomicZHatField :
            IntermediateField ℚ (SeparableClosure ℚ))) := by
  let K :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let T := rationalCyclotomicZHatField
  let J : IntermediateField ℚ (SeparableClosure ℚ) :=
    K ⊓ T
  let Jι : IntermediateField ℚ (SeparableClosure ℚ) :=
    ι.fieldRange ⊓ T
  let : FiniteDimensional ℚ K :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : FiniteDimensional ℚ J :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion
        (show J ≤ K from inf_le_left)).toLinearMap
      (IntermediateField.inclusion
        (show J ≤ K from inf_le_left)).injective
  let : FiniteDimensional ℚ ι.fieldRange :=
    (ι.equivFieldRange.toLinearEquiv).finiteDimensional
  let : FiniteDimensional ℚ Jι :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion
        (show Jι ≤ ι.fieldRange from inf_le_left)).toLinearMap
      (IntermediateField.inclusion
        (show Jι ≤ ι.fieldRange from inf_le_left)).injective
  let σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ :=
    AlgEquiv.ofBijective
      (ι.liftNormal (SeparableClosure ℚ))
      (AlgHom.normal_bijective
        ℚ (SeparableClosure ℚ) (SeparableClosure ℚ) _)
  have hσK (x : K) :
      σ (x : SeparableClosure ℚ) = ι x := by
    dsimp only [σ]
    rw [AlgEquiv.ofBijective_apply]
    simpa only [IntermediateField.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using
      ι.liftNormal_commutes (SeparableClosure ℚ) x
  have hmapK :
      K.map σ.toAlgHom = ι.fieldRange := by
    ext y
    constructor
    · rw [IntermediateField.mem_map]
      rintro ⟨x, hx, hxy⟩
      rw [AlgHom.mem_fieldRange]
      exact
        ⟨⟨x, hx⟩,
          (hσK ⟨x, hx⟩).symm.trans hxy⟩
    · rw [AlgHom.mem_fieldRange]
      rintro ⟨x, hxy⟩
      rw [IntermediateField.mem_map]
      exact
        ⟨(x : SeparableClosure ℚ), x.property,
          (hσK x).trans hxy⟩
  have hmapT :
      T.map σ.toAlgHom = T :=
    (IntermediateField.normal_iff_forall_map_eq'.1
      (by
        simpa only [T] using rationalCyclotomicZHatField_normal)) σ
  have hmapJ :
      J.map σ.toAlgHom = Jι := by
    dsimp only [J, Jι]
    rw [IntermediateField.map_inf, hmapK, hmapT]
  let e : J ≃ₐ[ℚ] Jι :=
    (IntermediateField.equivMap J σ.toAlgHom).trans
      (IntermediateField.equivOfEq hmapJ)
  exact e.toLinearEquiv.finrank_eq.symm

variable (K : Type*) [Field K] [NumberField K]

/-- The actual intersection `K ∩ E` inside the finite compositum,
transported back to the finite cyclotomic layer `E`. -/
def numberFieldCyclotomicZHatFiniteIntersection
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IntermediateField ℚ E :=
  IntermediateField.comap
    (rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E)
    (numberFieldCyclotomicZHatFiniteCompositumEmbedding K E).fieldRange

/-- An element of the finite-layer intersection is, in the common
separable closure, an element of the full intersection `K ∩ ℚ̃`. -/
theorem
    numberFieldCyclotomicZHatFiniteIntersection_coe_mem_intersection
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (x : E)
    (hx :
      x ∈ numberFieldCyclotomicZHatFiniteIntersection K E) :
    ((((x : E) : rationalCyclotomicZHatField) :
        SeparableClosure ℚ)) ∈
      numberFieldCyclotomicZHatIntersection K := by
  let C :=
    numberFieldCyclotomicZHatFiniteCompositum K E
  let eK : K →ₐ[ℚ] C :=
    numberFieldCyclotomicZHatFiniteCompositumEmbedding K E
  let eE : E →ₐ[ℚ] C :=
    rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E
  change eE x ∈ eK.fieldRange at hx
  rw [AlgHom.mem_fieldRange] at hx
  obtain ⟨k, hk⟩ := hx
  have hkΩ :
      numberFieldSeparableClosureEmbedding K k =
        ((((x : E) : rationalCyclotomicZHatField) :
          SeparableClosure ℚ)) := by
    have h := congrArg (fun y : C => y.1) hk
    change numberFieldSeparableClosureEmbedding K k =
      ((((x : E) : rationalCyclotomicZHatField) :
        SeparableClosure ℚ)) at h
    exact h
  constructor
  · exact ⟨k, hkΩ⟩
  · exact ((x : E) : rationalCyclotomicZHatField).property

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractFixedFieldIdeleClassEquivFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The infinite global Artin homomorphism

This file assembles the finite global Artin homomorphisms in the
`FiniteGaloisIntermediateField` inverse limit supplied by mathlib.  The
first target is the actual `ZHat`-extension of `ℚ` constructed in
`CyclotomicZHatBaseChange`.

The positive archimedean section below is the cyclotomic normalization device:
multiplying an idele by the section of its absolute
norm produces a norm-one idele without changing its Artin symbol.
-/

open scoped Classical IsMulCommutative NNReal NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp

/-- The positive archimedean section has absolute idele norm `r⁻¹`.
This is the normalization dictated by the convention in
`IdeleGroup.absoluteNorm`. -/
theorem rationalPositiveArchimedeanIdele_absoluteNorm
    (r : ℝ≥0ˣ) :
    IdeleGroup.absoluteNorm
        (rationalPositiveArchimedeanIdele r) =
      r⁻¹ := by
  have hcomponent :=
    congrArg Units.val
      (rationalPositiveArchimedeanIdele_infiniteComponent r)
  have hcomponent' :
      InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace
          ((IdeleGroup.infiniteComponent Rat.infinitePlace
            (rationalPositiveArchimedeanIdele r) :
              Rat.infinitePlace.Completionˣ) :
            Rat.infinitePlace.Completion) =
        ((r : ℝ≥0ˣ) : ℝ) := by
    simpa using hcomponent
  have hlocalNorm :
      ‖((IdeleGroup.infiniteComponent Rat.infinitePlace
          (rationalPositiveArchimedeanIdele r) :
            Rat.infinitePlace.Completionˣ) :
          Rat.infinitePlace.Completion)‖₊ =
        (r : ℝ≥0) := by
    apply NNReal.eq
    simp only [coe_nnnorm]
    calc
      ‖((IdeleGroup.infiniteComponent Rat.infinitePlace
          (rationalPositiveArchimedeanIdele r) :
            Rat.infinitePlace.Completionˣ) :
          Rat.infinitePlace.Completion)‖ =
          ‖InfinitePlace.Completion.ringEquivRealOfIsReal
            Rat.isReal_infinitePlace
            ((IdeleGroup.infiniteComponent Rat.infinitePlace
              (rationalPositiveArchimedeanIdele r) :
                Rat.infinitePlace.Completionˣ) :
              Rat.infinitePlace.Completion)‖ :=
        ((InfinitePlace.Completion.isometryEquivRealOfIsReal
          Rat.isReal_infinitePlace).isometry.norm_map_of_map_zero
          (map_zero
            (InfinitePlace.Completion.ringEquivRealOfIsReal
              Rat.isReal_infinitePlace))
          _).symm
      _ = ‖((r : ℝ≥0ˣ) : ℝ)‖ := by
        rw [hcomponent']
      _ = ((r : ℝ≥0ˣ) : ℝ) :=
        Real.norm_of_nonneg (r : ℝ≥0).coe_nonneg
  have hinfinite :
      InfiniteIdeleGroup.archimedeanNorm
          (rationalPositiveArchimedeanIdele r).1 =
        r := by
    rw [InfiniteIdeleGroup.archimedeanNorm_apply,
      Fintype.prod_unique]
    rw [show
      (default : InfinitePlace ℚ) = Rat.infinitePlace by
        exact Subsingleton.elim _ _,
      InfinitePlace.mult_isReal
      ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩,
      pow_one]
    apply Units.ext
    exact hlocalNorm
  rw [IdeleGroup.absoluteNorm_apply]
  change
    FiniteIdeleGroup.absoluteNorm (1 : FiniteIdeleGroup ℚ) *
        (InfiniteIdeleGroup.archimedeanNorm
          (rationalPositiveArchimedeanIdele r).1)⁻¹ =
      r⁻¹
  rw [map_one, hinfinite, one_mul]

/-!
## Assembly in the finite-Galois inverse limit

The following construction is the global analogue of LCFT's
`residueFrobeniusToLimit`: its coordinates are the actual finite global
Artin homomorphisms, and compatibility is restriction in a finite
abelian tower.
-/

/-- Postcomposition of a finite projection of the infinite global Artin map.
Keeping `congrArg` at this generic level prevents large concrete towers from
being normalized merely to infer the endpoints of the mapped equality. -/
theorem map_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    {M : Type} (f : (E ≃ₐ[K] E) → M) :
    letI : NumberField E := hE
    f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)) =
      f (globalArtinMonoidHom
        (K := K) (L := E) a) := by
  let : NumberField E := hE
  exact congrArg f
    (restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE)

/-- The finite global Artin homomorphism with its number-field witness fixed
as an explicit argument.  Concrete intermediate-field towers can share this
opaque hom without repeatedly comparing independently synthesized witnesses. -/
noncomputable def globalArtinMonoidHomOfNumberField
    (K L : Type) [Field K] [NumberField K]
    [Field L] [Algebra K L] [IsAbelianGalois K L]
    (hL : NumberField L) :
    IdeleGroup K →* (L ≃ₐ[K] L) := by
  letI : NumberField L := hL
  exact globalArtinMonoidHom (K := K) (L := L)

/-- Monoid-hom postcomposition of a finite projection, stated at the hom
application level.  This keeps concrete consumers from unfolding
`MonoidHom.comp` merely to join the projection and finite Artin endpoints. -/
theorem comp_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    {M : Type} [Monoid M]
    (f : (E ≃ₐ[K] E) →* M) :
    letI : NumberField E := hE
    f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)) =
      (f.comp (globalArtinMonoidHomOfNumberField K E hE)) a := by
  let : NumberField E := hE
  exact
    (map_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE f).trans rfl

/-- The mapped infinite projection transported through a supplied naturality
square.  The intermediate finite Artin hom is the explicit-witness version,
so the equality is composed once in this generic provider rather than by a
concrete dependent field tower. -/
noncomputable def
    compRestrictNormalHomInfiniteGlobalArtinNaturalityDataOfNumberField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    {M : Type} [Monoid M]
    (f : (E ≃ₐ[K] E) →* M)
    (g : IdeleGroup K →* M)
    (hnat :
      f.comp (globalArtinMonoidHomOfNumberField K E hE) = g) :
    letI : NumberField E := hE
    {x : M // x = g a} := by
  letI : NumberField E := hE
  have hprojection :=
    comp_restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE f
  exact
    ⟨f (AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a)),
      hprojection.trans (DFunLike.congr_fun hnat a)⟩

/-- Restriction of the infinite global Artin map along an abstract finite
abelian scalar tower.  Unlike the intermediate-field projection theorem, this
form allows the finite extension to be supplied through any chosen embedding
into the ambient infinite extension. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_scalarTower
    (K E Ω : Type) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [IsAbelianGalois K E]
    [Field Ω] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) :
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  let j : E →ₐ[K] Ω := IsScalarTower.toAlgHom K E Ω
  let G : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := j.fieldRange
      finiteDimensional :=
        j.equivFieldRange.toLinearEquiv.finiteDimensional
      isGalois := IsGalois.of_algEquiv j.equivFieldRange }
  let _ : FiniteDimensional K G := G.finiteDimensional
  let _ : NumberField G :=
    NumberField.of_module_finite K G
  let _ : IsAbelianGalois K G :=
    IsAbelianGalois.of_algHom G.toIntermediateField.val
  let _ : Algebra E G :=
    j.equivFieldRange.toRingHom.toAlgebra
  let _ : SMul E G := Algebra.toSMul
  let _ : IsScalarTower K E G :=
    IsScalarTower.of_algHom j.equivFieldRange.toAlgHom
  let _ : IsScalarTower K G Ω :=
    IntermediateField.isScalarTower_mid G.toIntermediateField
  let _ : IsScalarTower E G Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hProjection :
      AlgEquiv.restrictNormalHom G
          (infiniteGlobalArtinMonoidHom K Ω a) =
        globalArtinMonoidHom (K := K) (L := G) a :=
    restrictNormalHom_infiniteGlobalArtinMonoidHom K Ω a G
  calc
    AlgEquiv.restrictNormalHom E
          (infiniteGlobalArtinMonoidHom K Ω a) =
        AlgEquiv.restrictNormalHom E
          (AlgEquiv.restrictNormalHom G
            (infiniteGlobalArtinMonoidHom K Ω a)) :=
      IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E G
        (infiniteGlobalArtinMonoidHom K Ω a)
    _ = AlgEquiv.restrictNormalHom E
          (globalArtinMonoidHom (K := K) (L := G) a) :=
      congrArg (AlgEquiv.restrictNormalHom E) hProjection
    _ = globalArtinMonoidHom (K := K) (L := E) a :=
      DFunLike.congr_fun
        (globalArtinMonoidHom_restrict_tower
          (K := K) (L := G) (E := E)) a

/-- Finite global reciprocity at every coordinate makes the infinite
global Artin homomorphism dense in the Krull topology. -/
theorem infiniteGlobalArtinMonoidHom_denseRange
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω] :
    DenseRange (infiniteGlobalArtinMonoidHom K Ω) := by
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨σ, hσU⟩
  let V : Set (Ω ≃ₐ[K] Ω) :=
    (Homeomorph.mulLeft σ) ⁻¹' U
  have hVopen : IsOpen V :=
    hU.preimage (Homeomorph.mulLeft σ).continuous
  have hVone : (1 : Ω ≃ₐ[K] Ω) ∈ V := by
    change σ * 1 ∈ U
    simpa using hσU
  have hVnhds :
      V ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω) :=
    hVopen.mem_nhds hVone
  obtain ⟨E, hEV⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
        (k := K) (K := Ω) V).mp
      hVnhds
  let : NumberField E :=
    NumberField.of_module_finite K E
  obtain ⟨a, ha⟩ :=
    globalArtinMonoidHom_surjective
      (K := K) (L := E)
      (AlgEquiv.restrictNormalHom E σ)
  have hfix :
      σ⁻¹ * infiniteGlobalArtinMonoidHom K Ω a ∈
        E.fixingSubgroup := by
    rw [
      FiniteGaloisIntermediateField.mem_fixingSubgroup_iff,
      map_mul, map_inv,
      restrictNormalHom_infiniteGlobalArtinMonoidHom,
      ha, inv_mul_cancel]
  have hmemV :
      σ⁻¹ * infiniteGlobalArtinMonoidHom K Ω a ∈ V :=
    hEV hfix
  refine
    ⟨infiniteGlobalArtinMonoidHom K Ω a, ?_,
      ⟨a, rfl⟩⟩
  simpa [V, mul_assoc] using hmemV

/-- The rational `ZHat` specialization has dense Artin image. -/
theorem rationalCyclotomicZHatGlobalArtin_denseRange :
    DenseRange rationalCyclotomicZHatGlobalArtin :=
  infiniteGlobalArtinMonoidHom_denseRange
    ℚ rationalCyclotomicZHatField

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The rational cyclotomic principal-idele product formula

The ramified local factor at `p` is the direct `p`-adic unit character.
Every other finite local factor is the inverse Frobenius power prescribed
by the rational prime factorization.  Their product is the image of the
rational sign and therefore has square one.  Prime-power detection in the
torsion-free rational `ZHat`-extension removes this final sign ambiguity
and proves that every rational principal idele has trivial value.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_5
local instance rationalCyclotomicPrincipalProductPrimePowerNumberField
    (p : Nat.Primes) (k : ℕ) :
    NumberField (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

local instance rationalCyclotomicPrincipalProductPrimePowerFiniteDimensional_re7320f_1
    (p : Nat.Primes) (k : ℕ) :
    FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
local instance rationalCyclotomicPrincipalProductPrimePowerIsAbelianGalois
    (p : Nat.Primes) (k : ℕ) :
    IsAbelianGalois ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevelIsAbelianGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The rational cyclotomic complexification

This module realizes the quadratic complexification as the fourth-root
cyclotomic field and proves the rational principal-idele Artin formula.
-/

open scoped BigOperators Classical IsMulCommutative NumberField
open NumberField IsDedekindDomain
open IdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance rationalComplexificationPrimeFact_re7320f_1 :
    Fact rationalComplexificationPrime.1.Prime :=
  ⟨rationalComplexificationPrime.2⟩
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalComplexificationPrimeSquareNeZero
/-- The actual rational cyclotomic field generated by fourth roots of
unity, inside the rational cyclotomic closure. -/
abbrev rationalComplexificationCyclotomicField :
    IntermediateField ℚ KummerTheory.rationalCyclotomicField :=
  KummerTheory.rationalCyclotomicLevel
    rationalComplexificationCyclotomicOrder

noncomputable instance
    rationalComplexificationCyclotomicField_isCyclotomicFour :
    IsCyclotomicExtension {4} ℚ
      rationalComplexificationCyclotomicField := by
  change
    IsCyclotomicExtension
      {(rationalComplexificationCyclotomicOrder : ℕ)} ℚ
      rationalComplexificationCyclotomicField
  exact
    KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
      rationalComplexificationCyclotomicOrder

noncomputable local instance
    rationalComplexificationCyclotomicField_finiteDimensional :
    FiniteDimensional ℚ rationalComplexificationCyclotomicField :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    rationalComplexificationCyclotomicOrder

noncomputable local instance
    rationalComplexificationCyclotomicField_numberField :
    NumberField rationalComplexificationCyclotomicField :=
  KummerTheory.rationalCyclotomicLevel_numberField
    rationalComplexificationCyclotomicOrder

noncomputable local instance
    rationalComplexificationCyclotomicField_isAbelianGalois :
    IsAbelianGalois ℚ rationalComplexificationCyclotomicField :=
  rationalCyclotomicPrincipalPrimeLevelIsAbelianGalois
    rationalComplexificationCyclotomicOrder

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalArtinFiniteSupportApproximation
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalFiniteGaloisIdeleClassMulDistribMulAction _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.rationalAbsoluteGaloisIdeleClass_smul_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractFixedFieldIdeleClassEquivFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.GlobalClassFieldTheory.Reciprocity.rationalPositiveArchimedeanIdele_finiteComponent _root_.GlobalClassFieldTheory.Reciprocity.restrictNormalHom_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField _root_.GlobalClassFieldTheory.Reciprocity.restrictNormalHom_rationalCyclotomicZHatGlobalArtin _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Finite-support reduction for the global Artin map

For a finite abelian extension `L / K`, only finitely many finite local
Artin factors of an idele are nontrivial.  Keeping precisely those finite
components, together with every infinite component, gives an idele with
finite one-place support.  The quotient of the original idele by this
approximation is an actual relative-idele norm: outside the retained
finite set this follows from the local Artin kernel theorem, and at the
retained and infinite places it follows because the quotient component is
one.

Consequently both the preliminary global Artin map and the canonical
idele-class norm quotient may be evaluated on this finite-support
approximation.
-/

open scoped NumberField TensorProduct Classical BigOperators
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance] artinFiniteSupportIdeleClassIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The finite places at which the local Artin factor of `a` is
nontrivial. -/
noncomputable def globalArtinFiniteSupport
    (a : IdeleGroup K) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (finitePlaceArtinFactors_hasFiniteMulSupport
    (K := K) (L := L) a).toFinset

/-- Membership in the finite Artin support is equivalent to nontriviality of
the corresponding chosen local Artin factor. -/
@[simp]
theorem mem_globalArtinFiniteSupport_iff
    (a : IdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ globalArtinFiniteSupport (K := K) (L := L) a ↔
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.finiteComponent v a) ≠ 1 := by
  unfold globalArtinFiniteSupport
  exact
    (finitePlaceArtinFactors_hasFiniteMulSupport
      (K := K) (L := L) a).mem_toFinset

omit [IsAbelianGalois K L] in
/-- The canonical idele-class norm quotient kills every actual
relative-idele norm. -/
@[simp]
theorem globalNormClassFromIdele_relativeIdeleNorm_eq_one
    (z : RelativeIdeleGroup K L) :
    globalNormClassFromIdele K L
        (RelativeIdeleGroup.norm K L z) =
      1 := by
  change
    QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (RelativeIdeleGroup.norm K L z)) =
      1
  apply (QuotientGroup.eq_one_iff _).2
  refine
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z), ?_⟩
  rw [_root_.ideleClassNorm_mk,
    IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtension
private local instance q359TowerIdeleIsMulCommutative3.{w} (A B C : Type w) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite extensions in the rational idele-class representation

The fixed representation of a finite abstract extension is compared with
the relative idele class group of its two actual fixed fields.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

/-- The coefficient representation attached to a finite abstract
extension is the existing relative idele class group of its two actual
fixed fields.  This packages the fixed-part and tower base-change
comparisons into the endpoint used by finite reciprocity. -/
noncomputable def rationalAbstractExtensionIdeleClassEquiv
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K
    let E :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK
    letI := hnormal
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    letI : FiniteDimensional F E :=
      LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    letI : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    (extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal).V ≃+
      Additive (RelativeIdeleGroup.ClassGroup F E) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) K
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  let eFixed :
      Additive (IdeleClassGroup E) ≃+
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation L :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK
  let eRelative :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (IdeleClassGroup E) :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))
  let eTower :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (RelativeIdeleGroup.ClassGroup F E) :=
    MulEquiv.toAdditive
      ((TowerRelativeIdeleGroup.classGroupEquiv
        ℚ F E).symm.trans
          (towerRelativeIdeleClassBaseChangeMulEquiv
            ℚ F E))
  exact
    (((extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal).trans
        eFixed.symm).trans eRelative.symm).trans eTower

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Galois actions on rational fixed-field idele classes

Naturality of the fixed-field comparison for automorphisms and the
finite-extension Galois action.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

/-- The fixed-part idèle-class realization is natural under an
equivalence between two finite rational intermediate fields induced by
an automorphism of the rational separable closure. -/
theorem rationalIdeleClassEquivFixed_ambientAlgEquiv
    {E F : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ F]
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (e : E ≃ₐ[ℚ] F)
    (hσe : ∀ x : E,
      ((e x : F) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (c : IdeleClassGroup E) :
    rationalIdeleClassRepresentation.ρ σ
        (rationalIdeleClassEquivFixed E
          (Additive.ofMul c)).1 =
      (rationalIdeleClassEquivFixed F
        (Additive.ofMul (ideleClassCongr e c))).1 := by
  change
    Additive.ofMul
        (σ • rationalIntermediateIdeleClassToDirectLimit E c) =
      Additive.ofMul
        (rationalIntermediateIdeleClassToDirectLimit F
          (ideleClassCongr e c))
  exact congrArg Additive.ofMul
    (rationalIntermediateIdeleClassToDirectLimit_ambientAlgEquiv
      σ e hσe c)

/-- The relative fixed-field comparison has the same underlying direct-limit
class as the intermediate-field comparison from which it is transported. -/
theorem
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_coe
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)]
    [FiniteDimensional ℚ
      ((abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK).restrictScalars ℚ)]
    [NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)]
    (c : Additive
      (IdeleClassGroup
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK))) :
    (rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
        K L hLK c).1 =
      (rationalIdeleClassEquivFixed
        ((abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hLK).restrictScalars ℚ) c).1 := by
  rfl

theorem
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_baseChange_coe
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)]
    [FiniteDimensional ℚ
      ((abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK).restrictScalars ℚ)]
    [NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)]
    (c : Additive
      (RelativeIdeleGroup.ClassGroup ℚ
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK))) :
    (rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK
      ((MulEquiv.toAdditive
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ)
          (L := abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) hLK))) c)).1 =
      (rationalIdeleClassEquivFixed
        ((abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hLK).restrictScalars ℚ)
        (Additive.ofMul
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ)
            (L := abstractRelativeFixedField
              ℚ (SeparableClosure ℚ) hLK)
            (Additive.toMul c)))).1 := by
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let eFixed :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK
  let eRelative :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))
  calc
    (eFixed (eRelative c)).1 =
        (rationalIdeleClassEquivFixed
          (E.restrictScalars ℚ) (eRelative c)).1 :=
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_coe
        K L hLK (eRelative c)
    _ = (rationalIdeleClassEquivFixed
          (E.restrictScalars ℚ)
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E) (Additive.toMul c)))).1 :=
      congrArg
        (fun d =>
          (rationalIdeleClassEquivFixed
            (E.restrictScalars ℚ) d).1)
        (relativeIdeleClassBaseChangeAddEquiv_apply E c)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms on rational fixed-field idele classes

Compatibility of fixed-field inclusion and relative norm with the actual
idele-class extension attached to the abstract subgroup tower.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

noncomputable def rationalFixedFieldInclusionComparison
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : RelativeIdeleGroup.ClassGroup ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K)) :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  (rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
      ((extensionFixedRepresentationEquiv
        rationalIdeleClassRepresentation K L hLK hnormal).symm
        (fixedFieldInclusion rationalIdeleClassRepresentation
          K L hLK
          (rationalAbstractFixedFieldIdeleClassEquivFixed K
            (Additive.ofMul
              (_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := F) c))))),
    Additive.ofMul
      (RelativeIdeleGroup.classInclusion F E
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c)))

noncomputable def rationalExtensionNormComparison
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (x : (extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal).V) :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K inferInstance
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK inferInstance inferInstance
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let e :=
    rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
  (e (M.norm.hom x),
    includedRelativeIdeleClassNormAdditiveValue F E (e x))

noncomputable def rationalRelativeNormComparison
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let eK := rationalAbstractFixedFieldIdeleClassEquivFixed K
  let e :=
    rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
  (eK.symm
      (relativeNorm rationalIdeleClassRepresentation
        K L hLK a),
    relativeIdeleClassNormAdditiveValue F E
      (e (eAmbient.symm a)))

noncomputable def rationalFixedFieldIdeleClassAdditiveType
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))] : Type :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : NumberField F := NumberField.of_module_finite ℚ F
  Additive (IdeleClassGroup F)

noncomputable def rationalFixedFieldIdeleClassType
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))] : Type :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : NumberField F := NumberField.of_module_finite ℚ F
  IdeleClassGroup F

noncomputable def rationalRelativeNormSource
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    rationalFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) K :=
  (rationalRelativeNormComparison
    (hKfinite := hKfinite) (hfinite := hfinite)
    K L hLK hnormal a).1

noncomputable def rationalRelativeNormTarget
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    rationalFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) K :=
  (rationalRelativeNormComparison
    (hKfinite := hKfinite) (hfinite := hfinite)
    K L hLK hnormal a).2

noncomputable def rationalRelativeNormClassNormSource
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    rationalFixedFieldIdeleClassType
      (hKfinite := hKfinite) K :=
  Additive.toMul
    (rationalRelativeNormTarget
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK hnormal a)

noncomputable def rationalRelativeNormClassNormTarget
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    rationalFixedFieldIdeleClassType
      (hKfinite := hKfinite) K :=
  Additive.toMul
    (rationalRelativeNormSource
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK hnormal a)

/-- The fixed-part inclusion from the lower abstract field to the upper
one becomes the existing relative idele-class inclusion under the
fixed-field realization. -/
theorem
    rationalAbstractExtensionIdeleClassEquiv_fixedFieldInclusion
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : RelativeIdeleGroup.ClassGroup ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K)) :
    let comparison :=
      rationalFixedFieldInclusionComparison K L hLK hnormal c
    comparison.1 = comparison.2 := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let _ := hnormal
  let _ : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let _ : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let _ : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let _ : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let _ : NumberField E := NumberField.of_module_finite ℚ E
  let _ : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  let hFE : F ≤ E.restrictScalars ℚ :=
    abstractFixedField_le ℚ (SeparableClosure ℚ) hLK
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let eFixed :
      Additive (IdeleClassGroup E) ≃+
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation L :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK
  let eRelative :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (IdeleClassGroup E) :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))
  let eTower :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (RelativeIdeleGroup.ClassGroup F E) :=
    MulEquiv.toAdditive
      ((TowerRelativeIdeleGroup.classGroupEquiv
        ℚ F E).symm.trans
        (towerRelativeIdeleClassBaseChangeMulEquiv
          ℚ F E))
  let aK :
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K
      (Additive.ofMul
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c))
  let cE : RelativeIdeleGroup.ClassGroup ℚ E :=
    RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E.restrictScalars ℚ)
      (IntermediateField.inclusion hFE) c
  let z : Additive (RelativeIdeleGroup.ClassGroup ℚ E) :=
    Additive.ofMul cE
  let y :
      (extensionFixedRepresentation rationalIdeleClassRepresentation
        K L hLK hnormal).V :=
    eAmbient.symm
      (fixedFieldInclusion rationalIdeleClassRepresentation
        K L hLK aK)
  have hFixed :
      eFixed (eRelative z) =
        fixedFieldInclusion rationalIdeleClassRepresentation
          K L hLK aK := by
    apply Subtype.ext
    calc
      (eFixed (eRelative z)).1 =
          (rationalIdeleClassEquivFixed
            (E.restrictScalars ℚ)
            (Additive.ofMul
              (_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := E) cE))).1 := by
        rfl
      _ =
          (rationalIdeleClassEquivFixed F
            (Additive.ofMul
              (_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := F) c))).1 := by
        change
          Additive.ofMul
              (rationalIntermediateIdeleClassToDirectLimit
                (E.restrictScalars ℚ)
                (_root_.relativeIdeleClassBaseChangeMulEquiv
                  (K := ℚ) (L := E.restrictScalars ℚ)
                  (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E.restrictScalars ℚ)
                    (IntermediateField.inclusion hFE) c))) =
            Additive.ofMul
              (rationalIntermediateIdeleClassToDirectLimit F
                (_root_.relativeIdeleClassBaseChangeMulEquiv
                  (K := ℚ) (L := F) c))
        exact congrArg Additive.ofMul
          (rationalIntermediateIdeleClassToDirectLimit_extension hFE c)
      _ = aK.1 := by
        simpa only [aK, F] using
          (rationalAbstractFixedFieldIdeleClassEquivFixed_coe K
            (Additive.ofMul
              (_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := F) c))).symm
      _ =
          (fixedFieldInclusion rationalIdeleClassRepresentation
            K L hLK aK).1 := by
        exact
          (fixedFieldInclusion_coe rationalIdeleClassRepresentation
            K L hLK aK).symm
  have hAmbient :
      eAmbient y = eFixed (eRelative z) := by
    calc
      eAmbient y =
          fixedFieldInclusion rationalIdeleClassRepresentation
            K L hLK aK :=
        eAmbient.apply_symm_apply _
      _ = eFixed (eRelative z) := hFixed.symm
  have hTower :
      eTower z =
        Additive.ofMul
          (RelativeIdeleGroup.classInclusion F E
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := F) c)) := by
    apply Additive.toMul.injective
    change
      towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
          ((TowerRelativeIdeleGroup.classGroupEquiv
            ℚ F E).symm cE) =
        RelativeIdeleGroup.classInclusion F E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) c)
    exact
      rationalRelativeIdeleClassEmbedding_towerBaseChange hFE c
  change
    (((eAmbient.trans eFixed.symm).trans eRelative.symm).trans eTower) y =
      Additive.ofMul
        (RelativeIdeleGroup.classInclusion F E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) c))
  exact fourStepAddEquiv_apply_eq
    eAmbient eFixed eRelative eTower hAmbient hTower

theorem rationalRelativeNorm_representation_norm
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation L) :
    let M :=
      extensionFixedRepresentation rationalIdeleClassRepresentation
        K L hLK hnormal
    let eAmbient :=
      extensionFixedRepresentationEquiv
        rationalIdeleClassRepresentation K L hLK hnormal
    M.norm.hom (eAmbient.symm a) =
      eAmbient.symm
        (fixedFieldInclusion rationalIdeleClassRepresentation
          K L hLK
          (relativeNorm rationalIdeleClassRepresentation
            K L hLK a)) := by
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let x := eAmbient.symm a
  let n :=
    relativeNorm rationalIdeleClassRepresentation K L hLK a
  change
    M.norm.hom x =
      eAmbient.symm
        (fixedFieldInclusion rationalIdeleClassRepresentation
          K L hLK n)
  apply Subtype.ext
  change (M.norm.hom x).1 = n.1
  have hNormCoe :=
    extensionFixedRepresentation_norm_coe
      rationalIdeleClassRepresentation
      K L hLK hnormal x
  change
    (M.norm.hom x).1 =
      (relativeNorm rationalIdeleClassRepresentation
        K L hLK (eAmbient x)).1 at hNormCoe
  have hxa : eAmbient x = a :=
    eAmbient.apply_symm_apply a
  rw [hxa] at hNormCoe
  exact hNormCoe

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitNormQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Finite norm quotients for rational fixed fields

The abstract finite norm subgroup and quotient are identified with the
ordinary idele-class norm range and quotient of the actual fixed-field extension.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

local instance
    rationalNormQuotientIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance
    rationalNormQuotientIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative

theorem rationalTowerRelativeClass_baseChange
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra ℚ F] [Algebra F E] [Algebra ℚ E]
    [IsScalarTower ℚ F E]
    [FiniteDimensional ℚ F] [FiniteDimensional F E]
    (c : Additive (IdeleClassGroup E)) :
    _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F) (L := E)
        (towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
          ((TowerRelativeIdeleGroup.classGroupEquiv
            ℚ F E).symm
            ((_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E)).symm (Additive.toMul c)))) =
      Additive.toMul c := by
  let dQ : RelativeIdeleGroup.ClassGroup ℚ E :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := E)).symm (Additive.toMul c)
  have hTower :=
    relativeIdeleClassBaseChangeMulEquiv_tower ℚ F E dQ
  have hBase :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := E)).apply_symm_apply (Additive.toMul c)
  exact Eq.trans hTower hBase

noncomputable def rationalRelativeFixedFieldNormComparison
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : rationalRelativeFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK) :
    (KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation K) ×
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  letI : NumberField F :=
    rationalNormQuotientNumberFieldOfFiniteDimensional F
  letI : NumberField E :=
    rationalNormQuotientNumberFieldOfFiniteDimensional E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  (relativeNorm rationalIdeleClassRepresentation K L hLK
      (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed K L hLK c),
    rationalAbstractFixedFieldIdeleClassEquivFixed K
      (Additive.ofMul
        (_root_.ideleClassNorm F E (Additive.toMul c))))

noncomputable def rationalRelativeFixedFieldNormPreimageComparison
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : rationalRelativeFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK) :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  let dQ : RelativeIdeleGroup.ClassGroup ℚ E :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E)).symm
      (Additive.toMul c)
  let dF : RelativeIdeleGroup.ClassGroup F E := towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
    ((TowerRelativeIdeleGroup.classGroupEquiv ℚ F E).symm dQ)
  (rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
      ((extensionFixedRepresentationEquiv
        rationalIdeleClassRepresentation K L hLK hnormal).symm
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          K L hLK c)),
    Additive.ofMul dF)

noncomputable def rationalRelativeFixedFieldNormCohomologyComparison
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (c : rationalRelativeFixedFieldIdeleClassAdditiveType
      (hKfinite := hKfinite) (hfinite := hfinite)
      K L hLK) :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let eUpper :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed K L hLK
  let comparison :=
    rationalRelativeFixedFieldNormPreimageComparison
      K L hLK hnormal c
  ((rationalAbstractFixedFieldIdeleClassEquivFixed K).symm
      (relativeNorm rationalIdeleClassRepresentation
        K L hLK (eUpper c)),
    Additive.ofMul
      (RelativeIdeleGroup.Cohomology.ideleClassNorm F E
        (Additive.toMul comparison.2)))

end Reciprocity
end GlobalClassFieldTheory
end
end


