-- Prove2me | Definitions.Def_OAIQ244Duke107
-- name    : OAIQ244Duke107
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T04:13:30.385752+00:00
-- url     : https://prove2.me/theorems/cf52b8b1-df12-496f-ab66-3d5acf7ec0ef
-- title:
--   Definitions bundle OAIQ244Duke107 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 42 definitions, 11 instances and 46 theorems. The definitions and types are `GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin`, `GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField`, `GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBase`, `GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseEmbedding`, `GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseEquiv`, `GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseSubgroup`, `GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldMaximalIdeleClassEquiv`, `GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormAmbient`, `GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassField`, `GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBase`, `GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseEmbedding`, `GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseEquiv`, `GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseSubgroup`, `GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtension`, `GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldSubextension`, `GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassField`, `GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBase`, `GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseEquiv`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldIdeleClassGroupGroup`, `GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom`, `GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom`, `GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv`, `GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom`, `GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv`, `GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMonoidHom`, `GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMulEquiv`, `GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationEquiv`, `GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom`, `GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom`, `GlobalClassFieldTheory.Reciprocity.globalReciprocityAbelianizationContinuousMulEquiv`, `GlobalClassFieldTheory.Reciprocity.ideleClassNormAbelianizationQuotientContinuousMonoidHom`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryBaseEmbedding`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryCompositumSubextension`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryTopEmbedding`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicCoordinate`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicCyclicFixedField`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicCyclicFixedSubgroup`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicCyclicPreimage`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicImage` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_GlobalClassFields_ArithmeticUnramifiedPrimeArtin`, `GlobalClassFieldTheory_GlobalClassFields_BigHilbertClassFieldOverOriginalBase`, `GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldConstruction`, `GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldOriginalField`, `GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldReciprocity_Algebraic_Construction`, `GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldReciprocity_GlobalNormResidue`, `GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldReciprocity_Topological_Construction`, `GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldReciprocity_Topological_EvaluationCore`, `GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldReciprocity_Topological_EvaluationValue`, `GlobalClassFieldTheory_GlobalClassFields_FiniteAbelianClassFieldContainment`, `GlobalClassFieldTheory_GlobalClassFields_HilbertClassFieldMaximalSubextension`, `GlobalClassFieldTheory_GlobalClassFields_HilbertClassFieldRealization`, `GlobalClassFieldTheory_GlobalClassFields_OrdinaryNormClassField`, `GlobalClassFieldTheory_GlobalClassFields_SmallHilbertClassFieldOverOriginalBase`, `GlobalClassFieldTheory_Reciprocity_ArithmeticNormalization`, `GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedLocalGlobalCompatibility`, `GlobalClassFieldTheory_Reciprocity_GlobalNormResidueAbelianization`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicAuxiliaryField`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData`, `GlobalClassFieldTheory_Reciprocity_TopologicalGlobalNormResidueAbelianization`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke104`, `OAIQ244Duke105` and `OAIQ244Duke106` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke110` and `OAIQ244Duke111`; the statement `ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt`.
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
import Definitions.Def_OAIQ244Duke106

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedLocalGlobalCompatibility
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Cyclotomic unramified local--global compatibility

For an unramified finite abelian subextension of an abstract rational
fixed field, the actual global norm-residue homomorphism agrees on every
finite one-place idele class with the chosen local Artin homomorphism.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

attribute [local instance]
  rationalSeparableClosureAlgebra
  naturalityAbstractFixedFieldBaseQuotientFinite
  naturalityAbstractFixedFieldRelativeQuotientFinite
  naturalityAbstractFixedFieldFiniteDimensional
  naturalityAbstractRelativeFixedFieldFiniteDimensional
  naturalityAbstractFixedFieldRelativeScalarTower
  naturalityAbstractRelativeFixedFieldAbsoluteFiniteDimensional
  naturalityAbstractFixedFieldNumberField
  naturalityAbstractRelativeFixedFieldNumberField
  naturalityAbstractRelativeFixedFieldIsAbelianGalois

attribute [local instance] GlobalClassFieldTheory.Reciprocity.abstractFixedFieldFiniteIdeleGroupGroup
attribute [local instance] GlobalClassFieldTheory.Reciprocity.abstractFixedFieldIdeleGroupGroup
@[reducible]
noncomputable local instance
    abstractFixedFieldIdeleClassGroupGroup
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Group
      (IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :=
  QuotientGroup.Quotient.group
    (IdeleGroup.principalSubgroup
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field))

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.completedMaximalOrderCompactSpace _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space
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
# Finite p-adic cyclic data for local-global Artin compatibility

This module packages the simultaneous finite-quotient and cyclotomic
coordinates and the corresponding abstract auxiliary subextension.
-/

open scoped IsMulCommutative NumberField
open NumberField
open IdeleGroup RelativeIdeleGroup
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology
open KummerTheory ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_7
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionNormal
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePadicTowerExtensionQuotientFinite
noncomputable local instance numberFieldTowerExtensionQuotientIsMulCommutative :
    IsMulCommutative
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) := by
  let e :
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
          extensionSubgroup
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) ≃*
        Gal(L / K) :=
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
  exact
    { is_comm :=
        ⟨fun x y => by
          apply e.injective
          rw [map_mul, map_mul]
          exact
            (inferInstance :
              IsMulCommutative (Gal(L / K))).is_comm.comm
                (e x) (e y)⟩ }

attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupCompactSpace
/-- The finite quotient coordinate on the compatible embedded copy of
the absolute Galois group of `K`. -/
noncomputable def numberFieldTowerFiniteQuotientCoordinate :
    (numberFieldTowerBaseSubgroup K L).toSubgroup →ₜ*
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) := by
  let N :=
    extensionSubgroup
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  exact
    { toMonoidHom := QuotientGroup.mk' N
      continuous_toFun := QuotientGroup.continuous_mk }

/-- The simultaneous finite-extension and cyclotomic `p`-adic
coordinate on the compatible absolute Galois group of `K`. -/
noncomputable def numberFieldTowerFinitePadicCoordinate
    (p : Nat.Primes) :
    (numberFieldTowerBaseSubgroup K L).toSubgroup →ₜ*
      (((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
          extensionSubgroup
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) ×
        Multiplicative ℤ_[p.1]) := by
  let finiteCoordinate :=
    numberFieldTowerFiniteQuotientCoordinate
      (K := K) (L := L)
  let padicDegree :=
    numberFieldTowerBaseSubgroupPadicCyclotomicDegree
      (K := K) (L := L) p
  exact
    { toFun := fun τ =>
        (finiteCoordinate τ, padicDegree τ)
      map_one' := by
        simp only [map_one]
        rfl
      map_mul' := by
        intro σ τ
        simp only [map_mul, Prod.mul_def]
      continuous_toFun :=
        finiteCoordinate.continuous_toFun.prodMk
          padicDegree.continuous_toFun }

/-- The actual image of the simultaneous finite and `p`-adic
cyclotomic coordinate, as a closed subgroup of the product. -/
noncomputable def numberFieldTowerFinitePadicImage
    (p : Nat.Primes) :
    ClosedSubgroup
      (((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
          extensionSubgroup
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) ×
        Multiplicative ℤ_[p.1]) := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let N :=
    extensionSubgroup
      H
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  letI extensionSubgroupClosed : IsClosed (N : Set H.toSubgroup) :=
    extensionSubgroup_isClosed
      H
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  let coordinate :=
    numberFieldTowerFinitePadicCoordinate
      (K := K) (L := L) p
  refine
    { toSubgroup := coordinate.toMonoidHom.range
      isClosed' := ?_ }
  change IsClosed (Set.range coordinate)
  exact
    (isCompact_range coordinate.continuous_toFun).isClosed

/-- The simultaneous coordinate with codomain restricted to its actual
closed image. -/
noncomputable def numberFieldTowerFinitePadicRangeRestriction
    (p : Nat.Primes) :
    (numberFieldTowerBaseSubgroup K L).toSubgroup →ₜ*
      (numberFieldTowerFinitePadicImage
        (K := K) (L := L) p).toSubgroup := by
  let coordinate :=
    numberFieldTowerFinitePadicCoordinate
      (K := K) (L := L) p
  exact
    { toMonoidHom := coordinate.toMonoidHom.rangeRestrict
      continuous_toFun :=
        coordinate.continuous_toFun.subtype_mk
          (fun τ => ⟨τ, rfl⟩) }

/-- The inverse image in the compatible absolute Galois group of the
closed cyclic subgroup generated by one simultaneous finite/`p`-adic
coordinate. -/
noncomputable def numberFieldTowerFinitePadicCyclicPreimage
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    ClosedSubgroup
      (numberFieldTowerBaseSubgroup K L).toSubgroup := by
  let rangeRestriction :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p
  let γ :=
    rangeRestriction τ
  let Γ :=
    ClassFormation.padicCyclicClosure γ
  exact
    { toSubgroup :=
        Γ.toSubgroup.comap
          rangeRestriction.toMonoidHom
      isClosed' :=
        Γ.isClosed'.preimage
          rangeRestriction.continuous_toFun }

/-- The cyclic preimage, embedded back into the rational absolute
Galois group.  Its fixed field is the concrete auxiliary number field
used in the finite-place reduction. -/
noncomputable def numberFieldTowerFinitePadicCyclicFixedSubgroup
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    ClosedSubgroup (Gal(SeparableClosure ℚ / ℚ)) := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  exact
    { toSubgroup :=
        U.toSubgroup.map H.toSubgroup.subtype
      isClosed' := by
        change
          IsClosed
            (Subtype.val ''
              (U : Set H.toSubgroup))
        exact
          H.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap
            (U : Set H.toSubgroup) U.isClosed' }

/-- The auxiliary cyclic fixed subgroup lies in the subgroup fixing
the compatible embedded copy of `K`. -/
theorem numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ).toSubgroup ≤
      (numberFieldTowerBaseSubgroup K L).toSubgroup := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  rintro _ ⟨u, _, rfl⟩
  exact u.2

/-- Base change of `L / K` to the auxiliary cyclic fixed field.  Its
top subgroup is the intersection of the auxiliary fixing subgroup
with the subgroup fixing `L`, hence its concrete top field is the
auxiliary compositum with `L`. -/
noncomputable def
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    FiniteAbelianSubextension
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ) :=
  (numberFieldTowerFiniteAbelianSubextension K L).baseChange
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ)
    (numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
      (K := K) (L := L) p τ)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicAuxiliaryField
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
# The finite p-adic auxiliary field

This module realizes the simultaneous finite/cyclotomic lift as an actual
number field and proves the subgroup and intermediate-field identities
needed by the auxiliary-field argument.
-/

open scoped IsMulCommutative NumberField
open AlgebraicNumberTheory IsDedekindDomain NumberField
open IdeleGroup RelativeIdeleGroup
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology
open KummerTheory ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open GlobalClassFields

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance]
  rationalSeparableClosureAlgebra

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_8
local instance finitePadicAuxiliaryExtensionNormal :
    (extensionSubgroup
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).Normal :=
  numberFieldTowerExtensionSubgroup_normal K L

local instance finitePadicAuxiliaryExtensionQuotientFinite_red7440_1 :
    Finite
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  numberFieldTowerExtensionQuotient_finite K L
noncomputable local instance finitePadicAuxiliaryExtensionQuotientIsMulCommutative :
    IsMulCommutative
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) := by
  let e :
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
          extensionSubgroup
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) ≃*
        Gal(L / K) :=
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
  exact
    { is_comm :=
        ⟨fun x y => by
          apply e.injective
          rw [map_mul, map_mul]
          exact
            (inferInstance :
              IsMulCommutative (Gal(L / K))).is_comm.comm
                (e x) (e y)⟩ }

/-- The concrete auxiliary fixed field attached to a simultaneous
finite/cyclotomic lift. -/
noncomputable def numberFieldTowerFinitePadicCyclicFixedField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IntermediateField ℚ (SeparableClosure ℚ) := by
  exact
    IntermediateField.fixedField
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ).toSubgroup

/-- The compatible embedded copy of `K` lies in every auxiliary
cyclic fixed field. -/
theorem numberFieldTowerBaseField_le_finitePadicCyclicFixedField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    numberFieldTowerBaseField K L ≤
      numberFieldTowerFinitePadicCyclicFixedField
        (K := K) (L := L) p τ := by
  intro x hx
  change x ∈ IntermediateField.fixedField
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ).toSubgroup
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  change
    σ ∈
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ).toSubgroup at hσ
  obtain ⟨u, hu, rfl⟩ := hσ
  exact
    (IntermediateField.mem_fixingSubgroup_iff
      (numberFieldTowerBaseField K L) u.1).1 u.2 x hx

/-- The compatible embedding of the original base field into the
genuine auxiliary fixed field. -/
noncomputable def numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    K →ₐ[ℚ]
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ)
  exact
    (numberFieldTowerLowerEmbedding K L).codRestrict F.toSubalgebra
      (fun x =>
        numberFieldTowerBaseField_le_finitePadicCyclicFixedField
          (K := K) (L := L) p τ ⟨x, rfl⟩)

/-- Coercing the auxiliary base embedding recovers the fixed lower embedding
into the rational separable closure. -/
@[simp]
theorem numberFieldTowerFinitePadicAuxiliaryBaseEmbedding_coe
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (x : K) :
    ((numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
        (K := K) (L := L) p τ x :
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) :
      SeparableClosure ℚ) =
        numberFieldTowerLowerEmbedding K L x := by
  rfl

/-- The compatible copy of the original top field lies in the
auxiliary compositum fixed field. -/
theorem numberFieldTowerTopField_mem_finitePadicAuxiliaryTopField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    {x : SeparableClosure ℚ}
    (hx : x ∈ numberFieldInRationalSeparableClosure L) :
    x ∈
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below := by
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let T :=
    numberFieldTowerTopSubgroup L
  change x ∈ IntermediateField.fixedField
    (S.toSubgroup ⊓ T.toSubgroup)
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hσT : σ ∈ T.toSubgroup :=
    hσ.2
  change
    σ ∈
      (numberFieldInRationalSeparableClosure L).fixingSubgroup
        at hσT
  exact
    (IntermediateField.mem_fixingSubgroup_iff
      (numberFieldInRationalSeparableClosure L) σ).1
      hσT x hx

/-- The compatible embedding of the original top field into the
auxiliary compositum fixed field. -/
noncomputable def numberFieldTowerFinitePadicAuxiliaryTopEmbedding
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    L →ₐ[ℚ]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below := by
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ).below
  exact
    (numberFieldSeparableClosureEmbedding L).codRestrict
      (E.restrictScalars ℚ).toSubalgebra
      (fun x =>
        numberFieldTowerTopField_mem_finitePadicAuxiliaryTopField
          (K := K) (L := L) p τ ⟨x, rfl⟩)

/-- Coercing the auxiliary top embedding recovers the chosen top-field
embedding into the rational separable closure. -/
@[simp]
theorem numberFieldTowerFinitePadicAuxiliaryTopEmbedding_coe
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (x : L) :
    ((numberFieldTowerFinitePadicAuxiliaryTopEmbedding
        (K := K) (L := L) p τ x :
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) :
      SeparableClosure ℚ) =
        numberFieldSeparableClosureEmbedding L x := by
  rfl

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalNormResidueAbelianization
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.idealArtinMap_primeToIdealMap _root_.GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.primeToIdealMap_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdeleQuotient_mk_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHomOfEmbedding_apply _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_ideleClassNorm _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The global norm-residue symbol for finite Galois extensions

For an arbitrary finite Galois extension of number fields, the global
norm-residue quotient is the abelianization of the genuine Galois group:

`C_K / N_{L/K} C_L ≃ Gal(L / K)ᵃᵇ`.

The abelian specialization in `GlobalNormResidue` identifies this target
further with `Gal(L / K)`.  This file retains the abelianization and therefore
states global reciprocity at its full finite-Galois generality.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianization_ideleClassGroupIsMulCommutative
/-- The abstract norm-residue symbol followed by the concrete Galois
comparison.  This declaration boundary keeps the dependent quotient indices
and their instance packages from being reconstructed at each evaluation. -/
noncomputable def
    numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv :
    FiniteNormQuotient rationalIdeleClassRepresentation
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L) ≃+
      Additive (Abelianization (Gal(L / K))) := by
  let _ : Finite _ :=
    (numberFieldTowerReciprocityFiniteAbstractField K L).finite
  let _ :
      (CyclicCohomology.extensionSubgroup
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).Normal :=
    numberFieldTowerExtensionSubgroup_normal K L
  let _ : Finite _ :=
    (numberFieldTowerFiniteGaloisSubextension K L).finite
  letI : AddCommGroup
      (FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
    finiteNormQuotientAddCommGroup rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  exact
    @AddEquiv.trans
      (FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
      (Additive
        (Abelianization
          (ClassFormation.FiniteGaloisSubextension.extensionQuotient
            (numberFieldTowerFiniteGaloisSubextension K L))))
      (Additive (Abelianization (Gal(L / K))))
      inferInstance inferInstance inferInstance
      (rationalCyclotomicDegreeData.normResidueSymbol
        rationalIdeleClassRepresentation
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        (numberFieldTowerReciprocityFiniteAbstractField K L)
        (numberFieldTowerFiniteGaloisSubextension K L))
      (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
        K L)

/-- The actual global norm-residue equivalence for a finite Galois
number-field extension:

`C_K / N_{L/K} C_L ≃ Gal(L / K)ᵃᵇ`. -/
noncomputable def globalNormResidueAbelianizationEquiv :
    Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃+
      Additive (Abelianization (Gal(L / K))) := by
  exact
    (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
        K L).symm.trans
      (numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv K L)

/-- The genuine global norm-residue homomorphism with target the
abelianization of the actual Galois group. -/
noncomputable def globalNormResidueAbelianizationMonoidHom :
    IdeleClassGroup K →*
      Abelianization (Gal(L / K)) := by
  let e :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃*
        Abelianization (Gal(L / K)) :=
    AddEquiv.toMultiplicative
      (globalNormResidueAbelianizationEquiv K L)
  exact
    e.toMonoidHom.comp
      (QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range)

/-- Evaluation of the finite-Galois global norm-residue homomorphism is the
global equivalence applied to the genuine norm quotient class. -/
@[simp]
theorem globalNormResidueAbelianizationMonoidHom_apply
    (c : IdeleClassGroup K) :
    globalNormResidueAbelianizationMonoidHom K L c =
      Additive.toMul
        (globalNormResidueAbelianizationEquiv K L
          (Additive.ofMul
            (QuotientGroup.mk'
              (_root_.ideleClassNorm K L).range c))) :=
  rfl

/-- An idele class has trivial finite-Galois norm-residue symbol exactly when
it is an actual idele-class norm from `L`. -/
@[simp]
theorem globalNormResidueAbelianizationMonoidHom_eq_one_iff
    (c : IdeleClassGroup K) :
    globalNormResidueAbelianizationMonoidHom K L c = 1 ↔
      c ∈ (_root_.ideleClassNorm K L).range := by
  let e :=
    AddEquiv.toMultiplicative
      (globalNormResidueAbelianizationEquiv K L)
  change
    e (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range c) =
        1 ↔
      c ∈ (_root_.ideleClassNorm K L).range
  constructor
  · intro h
    have hq :
        QuotientGroup.mk'
            (_root_.ideleClassNorm K L).range c =
          1 := by
      apply
        e.injective
      exact h.trans (map_one e).symm
    exact (QuotientGroup.eq_one_iff c).1 hq
  · intro hc
    have hq :
        QuotientGroup.mk'
            (_root_.ideleClassNorm K L).range c =
          1 :=
      (QuotientGroup.eq_one_iff c).2 hc
    exact
      (congrArg e hq).trans
        (map_one e)

/-- The finite-Galois global norm-residue symbol viewed on the idele group.

This is the genuine idele-class symbol pulled back along
`I_K → C_K`; in particular it is not a separately chosen map. -/
noncomputable def globalNormResidueAbelianizationIdeleMonoidHom :
    IdeleGroup K →*
      Abelianization (Gal(L / K)) :=
  (globalNormResidueAbelianizationMonoidHom K L).comp
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K))

/-- Evaluation of the finite-Galois norm-residue symbol on an idele is
evaluation of the class symbol on its genuine idele class. -/
@[simp]
theorem globalNormResidueAbelianizationIdeleMonoidHom_apply
    (a : IdeleGroup K) :
    globalNormResidueAbelianizationIdeleMonoidHom K L a =
      globalNormResidueAbelianizationMonoidHom K L
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) :=
  rfl

/-- The finite-Galois norm-residue symbol on ideles is trivial on every
principal idele. -/
@[simp]
theorem globalNormResidueAbelianizationIdeleMonoidHom_principalIdele
    (x : Kˣ) :
    globalNormResidueAbelianizationIdeleMonoidHom K L
        (IdeleGroup.principalIdele K x) =
      1 := by
  have hclass :
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (IdeleGroup.principalIdele K x) =
        1 :=
    (QuotientGroup.eq_one_iff
      (IdeleGroup.principalIdele K x)).2
      ⟨x, rfl⟩
  calc
    globalNormResidueAbelianizationIdeleMonoidHom K L
          (IdeleGroup.principalIdele K x) =
        globalNormResidueAbelianizationMonoidHom K L
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)
            (IdeleGroup.principalIdele K x)) :=
      globalNormResidueAbelianizationIdeleMonoidHom_apply K L _
    _ = globalNormResidueAbelianizationMonoidHom K L 1 :=
      congrArg
        (globalNormResidueAbelianizationMonoidHom K L)
        hclass
    _ = 1 := map_one _

/-- An idele has trivial finite-Galois norm-residue symbol exactly when
its idele class is an actual norm from `L`. -/
@[simp]
theorem globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff
    (a : IdeleGroup K) :
    globalNormResidueAbelianizationIdeleMonoidHom K L a = 1 ↔
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a ∈
        (_root_.ideleClassNorm K L).range := by
  simpa only [
    globalNormResidueAbelianizationIdeleMonoidHom_apply] using
      globalNormResidueAbelianizationMonoidHom_eq_one_iff K L
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a)

/-- The kernel of the idele-level finite-Galois norm-residue symbol is the
full inverse image of the genuine idele-class norm range. -/
@[simp]
theorem globalNormResidueAbelianizationIdeleMonoidHom_ker :
    (globalNormResidueAbelianizationIdeleMonoidHom K L).ker =
      (_root_.ideleClassNorm K L).range.comap
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)) := by
  ext a
  change
    globalNormResidueAbelianizationIdeleMonoidHom K L a = 1 ↔
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a ∈
        (_root_.ideleClassNorm K L).range
  exact
    globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff
      K L a

/-- The kernel of the finite-Galois norm-residue homomorphism is exactly the
range of the ordinary idele-class norm. -/
@[simp]
theorem globalNormResidueAbelianizationMonoidHom_ker :
    (globalNormResidueAbelianizationMonoidHom K L).ker =
      (_root_.ideleClassNorm K L).range := by
  ext c
  change
    globalNormResidueAbelianizationMonoidHom K L c = 1 ↔
      c ∈ (_root_.ideleClassNorm K L).range
  exact
    globalNormResidueAbelianizationMonoidHom_eq_one_iff
      K L c

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_TopologicalGlobalNormResidueAbelianization
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.idealArtinMap_primeToIdealMap _root_.GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.primeToIdealMap_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdeleQuotient_mk_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHomOfEmbedding_apply _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_ideleClassNorm _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Topological global reciprocity for finite Galois extensions

For a finite Galois extension `L / K`, global norm-residue reciprocity
identifies the native idele-class norm quotient with the abelianization
of the finite Krull Galois group.  This file records the identification
as a `ContinuousMulEquiv` in both mathematical directions:

* norm-residue: `C_K / N_{L/K}(C_L) ≃ₜ* Gal(L / K)ᵃᵇ`;
* reciprocity: `Gal(L / K)ᵃᵇ ≃ₜ* C_K / N_{L/K}(C_L)`.

The evaluation lemmas below ensure that these are the already
constructed actual global symbols, rather than unrelated abstract
isomorphisms between finite groups.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Keep quotient normality out of every exported declaration type. -/
local instance
    topologicalGlobalNormResidueAbelianization_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The native topology on the actual idele-class norm quotient is
discrete.  The openness used here is the genuine ordinary norm-range
theorem for the given finite Galois extension. -/
theorem ideleClassNormAbelianizationQuotient_discreteTopology :
    DiscreteTopology
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) := by
  apply QuotientGroup.discreteTopology
  exact
    GlobalClassFields.ideleClassNorm_range_isOpen
      (K := K) (L := L)

local instance
    topologicalGlobalNormResidueAbelianization_normQuotientDiscreteTopology :
    DiscreteTopology
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  ideleClassNormAbelianizationQuotient_discreteTopology K L

attribute [local instance] GlobalClassFieldTheory.Reciprocity.topologicalGlobalNormResidueAbelianization_galoisAbelianizationTopology
attribute [local instance] GlobalClassFieldTheory.Reciprocity.topologicalGlobalNormResidueAbelianization_galoisAbelianizationDiscreteTopology
/-- The full finite-Galois norm-residue isomorphism with its native
topologies:

`C_K / N_{L/K}(C_L) ≃ₜ* Gal(L / K)ᵃᵇ`. -/
noncomputable def globalNormResidueAbelianizationContinuousMulEquiv :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃ₜ*
      Abelianization (Gal(L / K)) := by
  let e :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃*
        Abelianization (Gal(L / K)) :=
    AddEquiv.toMultiplicative
      (globalNormResidueAbelianizationEquiv K L)
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- Evaluation of the topological finite-Galois norm-residue
equivalence is the previously constructed actual norm-residue
equivalence. -/
@[simp]
theorem globalNormResidueAbelianizationContinuousMulEquiv_apply
    (c :
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :
    globalNormResidueAbelianizationContinuousMulEquiv K L c =
      Additive.toMul
        (globalNormResidueAbelianizationEquiv K L
          (Additive.ofMul c)) := by
  rfl

/-- Global reciprocity for a finite Galois extension in the direction
used by the class-field correspondence:

`Gal(L / K)ᵃᵇ ≃ₜ* C_K / N_{L/K}(C_L)`. -/
noncomputable def globalReciprocityAbelianizationContinuousMulEquiv :
    Abelianization (Gal(L / K)) ≃ₜ*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  (globalNormResidueAbelianizationContinuousMulEquiv K L).symm

/-- Evaluation in the reciprocity direction is exactly the inverse
actual finite-Galois norm-residue map. -/
@[simp]
theorem globalReciprocityAbelianizationContinuousMulEquiv_apply
    (σ : Abelianization (Gal(L / K))) :
    globalReciprocityAbelianizationContinuousMulEquiv K L σ =
      Additive.toMul
        ((globalNormResidueAbelianizationEquiv K L).symm
          (Additive.ofMul σ)) := by
  rfl

/-- The native quotient projection
`C_K → C_K / N_{L/K}(C_L)` as a continuous homomorphism. -/
noncomputable def
    ideleClassNormAbelianizationQuotientContinuousMonoidHom :
    IdeleClassGroup K →ₜ*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  { QuotientGroup.mk'
      (_root_.ideleClassNorm K L).range with
    continuous_toFun := QuotientGroup.continuous_mk }

/-- The global norm-residue symbol
`C_K → Gal(L / K)ᵃᵇ` as a continuous homomorphism in the natural
idele-class and finite Krull quotient topologies. -/
noncomputable def
    globalNormResidueAbelianizationContinuousMonoidHom :
    IdeleClassGroup K →ₜ*
      Abelianization (Gal(L / K)) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
      (globalNormResidueAbelianizationContinuousMulEquiv K L)).comp
    (ideleClassNormAbelianizationQuotientContinuousMonoidHom K L)

/-- Forgetting continuity from the topological finite-Galois
norm-residue map recovers the previously constructed actual symbol. -/
@[simp]
theorem globalNormResidueAbelianizationContinuousMonoidHom_apply
    (c : IdeleClassGroup K) :
    globalNormResidueAbelianizationContinuousMonoidHom K L c =
      globalNormResidueAbelianizationMonoidHom K L c := by
  rfl

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ArithmeticNormalization
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
attribute [-simp] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.idealArtinMap_primeToIdealMap _root_.GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.primeToIdealMap_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdeleQuotient_mk_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
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

theorem arithmeticNormIdeleClassIsMulCommutative
    (K : Type) [Field K] [NumberField K] :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] arithmeticNormIdeleClassIsMulCommutative

section FiniteGalois

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Reuse the quotient topology chosen by topological global reciprocity. -/
local instance
    arithmeticGlobalNormResidueAbelianization_galoisAbelianizationTopology_red7440_1 :
    TopologicalSpace (Abelianization (Gal(L / K))) :=
  topologicalGlobalNormResidueAbelianization_galoisAbelianizationTopology
    K L
/-- The quotient topology above carries the quotient topological-group
structure. -/
local instance
    arithmeticGlobalNormResidueAbelianization_galoisAbelianizationIsTopologicalGroup_red7440_1 :
    IsTopologicalGroup (Abelianization (Gal(L / K))) := by
  change
    IsTopologicalGroup
      (Gal(L / K) ⧸ commutator (Gal(L / K)))
  infer_instance
/-- The global norm-residue homomorphism with arithmetic
Frobenius normalization, for an arbitrary finite Galois extension. -/
noncomputable def arithmeticGlobalNormResidueAbelianizationMonoidHom :
    IdeleClassGroup K →*
      Abelianization (Gal(L / K)) :=
  (MulEquiv.inv
      (Abelianization (Gal(L / K)))).toMonoidHom.comp
    (globalNormResidueAbelianizationMonoidHom K L)

/-- Arithmetic normalization evaluates by inverting the geometric
norm-residue symbol. -/
@[simp]
theorem arithmeticGlobalNormResidueAbelianizationMonoidHom_apply
    (c : IdeleClassGroup K) :
    arithmeticGlobalNormResidueAbelianizationMonoidHom K L c =
      (globalNormResidueAbelianizationMonoidHom K L c)⁻¹ := by
  rfl

/-- Arithmetic normalization does not change the genuine norm kernel. -/
@[simp]
theorem arithmeticGlobalNormResidueAbelianizationMonoidHom_ker :
    (arithmeticGlobalNormResidueAbelianizationMonoidHom K L).ker =
      (_root_.ideleClassNorm K L).range := by
  ext c
  simp only [MonoidHom.mem_ker,
    arithmeticGlobalNormResidueAbelianizationMonoidHom_apply,
    inv_eq_one]
  exact globalNormResidueAbelianizationMonoidHom_eq_one_iff K L c

end FiniteGalois

section FiniteAbelian

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The global norm-residue homomorphism in arithmetic Frobenius
normalization for a finite abelian extension. -/
noncomputable def arithmeticGlobalNormResidueMonoidHom :
    IdeleClassGroup K →* Gal(L / K) :=
  (MulEquiv.inv (Gal(L / K))).toMonoidHom.comp
    (globalNormResidueMonoidHom K L)

/-- Arithmetic normalization evaluates by inverting the geometric global
norm-residue symbol. -/
@[simp]
theorem arithmeticGlobalNormResidueMonoidHom_apply
    (c : IdeleClassGroup K) :
    arithmeticGlobalNormResidueMonoidHom K L c =
      (globalNormResidueMonoidHom K L c)⁻¹ := by
  rfl

/-- Arithmetic normalization leaves the global norm kernel unchanged. -/
@[simp]
theorem arithmeticGlobalNormResidueMonoidHom_ker :
    (arithmeticGlobalNormResidueMonoidHom K L).ker =
      (_root_.ideleClassNorm K L).range := by
  ext c
  simp only [MonoidHom.mem_ker,
    arithmeticGlobalNormResidueMonoidHom_apply, inv_eq_one]
  exact globalNormResidueMonoidHom_eq_one_iff K L c

/-- Arithmetic global norm-residue as a homeomorphic multiplicative
equivalence of the native norm quotient with the finite Krull Galois
group. -/
noncomputable def arithmeticGlobalNormResidueContinuousMulEquiv :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃ₜ*
      Gal(L / K) :=
  (globalNormResidueContinuousMulEquiv K L).trans
    (commutativeGroupInversionContinuousMulEquiv
      (Gal(L / K)))

/-- The arithmetic norm-residue equivalence is pointwise the inverse of the
geometric equivalence. -/
@[simp]
theorem arithmeticGlobalNormResidueContinuousMulEquiv_apply
    (q :
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :
    arithmeticGlobalNormResidueContinuousMulEquiv K L q =
      (globalNormResidueContinuousMulEquiv K L q)⁻¹ := by
  rfl

/-- The canonical arithmetic reciprocity isomorphism in the direction
`Gal(L/K) ≃ₜ* C_K / N_{L/K}(C_L)`. -/
noncomputable def arithmeticGlobalReciprocityContinuousMulEquiv :
    Gal(L / K) ≃ₜ*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  (arithmeticGlobalNormResidueContinuousMulEquiv K L).symm

/-- Applying inverse arithmetic reciprocity to a quotient representative
recovers the arithmetic norm-residue symbol. -/
@[simp]
theorem arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk
    (c : IdeleClassGroup K) :
    (arithmeticGlobalReciprocityContinuousMulEquiv K L).symm
      (QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range c) =
      arithmeticGlobalNormResidueMonoidHom K L c := by
  rfl

/-- Arithmetic reciprocity sends the arithmetic norm-residue symbol of an
idèle class to its literal representative in the norm quotient. -/
@[simp]
theorem arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue
    (c : IdeleClassGroup K) :
    arithmeticGlobalReciprocityContinuousMulEquiv K L
        (arithmeticGlobalNormResidueMonoidHom K L c) =
      QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range c := by
  let e := arithmeticGlobalReciprocityContinuousMulEquiv K L
  calc
    e (arithmeticGlobalNormResidueMonoidHom K L c) =
        e
          (e.symm
            (QuotientGroup.mk'
              (_root_.ideleClassNorm K L).range c)) :=
      congrArg e
        (arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk
          K L c).symm
    _ = QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range c :=
      e.apply_symm_apply _

omit [NumberField L] in
/-- Arithmetic finite-place Artin symbols are inverses of the geometric
chosen local symbols. -/
@[simp]
theorem arithmeticChosenFinitePlaceArtinMonoidHom_apply
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    arithmeticChosenFinitePlaceArtinMonoidHom K L v x =
      (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x)⁻¹ := by
  rfl

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- Arithmetic infinite-place Artin symbols are inverses of the geometric
chosen local symbols. -/
@[simp]
theorem arithmeticChosenInfinitePlaceArtinMonoidHom_apply
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    arithmeticChosenInfinitePlaceArtinMonoidHom K L v x =
      (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v x)⁻¹ := by
  rfl

/-- The idèle-level global Artin product in arithmetic normalization. -/
noncomputable def arithmeticGlobalArtinMonoidHom :
    IdeleGroup K →* Gal(L / K) :=
  (MulEquiv.inv (Gal(L / K))).toMonoidHom.comp
    (globalArtinMonoidHom (K := K) (L := L))

omit [FiniteDimensional K L] in
/-- The arithmetic global Artin symbol is the inverse of the geometric global
Artin symbol. -/
@[simp]
theorem arithmeticGlobalArtinMonoidHom_apply
    (a : IdeleGroup K) :
    arithmeticGlobalArtinMonoidHom K L a =
      (globalArtinMonoidHom (K := K) (L := L) a)⁻¹ := by
  rfl

/-- The arithmetic global Artin symbol of a finite one-place idèle is
literally the arithmetic chosen local Artin symbol. -/
@[simp]
theorem arithmeticGlobalArtinMonoidHom_finitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    arithmeticGlobalArtinMonoidHom K L
        (finitePlaceIdele v x) =
      arithmeticChosenFinitePlaceArtinMonoidHom K L v x := by
  rw [arithmeticGlobalArtinMonoidHom_apply,
    globalArtinMonoidHom_finitePlaceIdele,
    arithmeticChosenFinitePlaceArtinMonoidHom_apply]

omit [FiniteDimensional K L] in
/-- The arithmetic global Artin symbol of an infinite one-place idèle
is literally the arithmetic chosen local Artin symbol. -/
@[simp]
theorem arithmeticGlobalArtinMonoidHom_infinitePlaceIdele
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    arithmeticGlobalArtinMonoidHom K L
        (infinitePlaceIdele v x) =
      arithmeticChosenInfinitePlaceArtinMonoidHom K L v x := by
  rw [arithmeticGlobalArtinMonoidHom_apply,
    globalArtinMonoidHom_infinitePlaceIdele,
    arithmeticChosenInfinitePlaceArtinMonoidHom_apply]

end FiniteAbelian

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ArithmeticUnramifiedPrimeArtin
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
attribute [-simp] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.idealArtinMap_primeToIdealMap _root_.GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.primeToIdealMap_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdeleQuotient_mk_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.IdeleGroup.count_fractionalIdeal _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Arithmetic Frobenius at an unramified finite place

The pre-existing local class-formation coordinate has geometric
Frobenius normalization.  This file supplies the canonical prime Artin
element used in the ideal-theoretic formulation: the ordinary normalized
prime idèle maps to arithmetic Frobenius.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The arithmetic global Artin element of the ordinary normalized
one-place prime idèle. -/
noncomputable def arithmeticFinitePlacePrimeArtin
    (v : HeightOneSpectrum (𝓞 K)) :
    L ≃ₐ[K] L :=
  Reciprocity.arithmeticGlobalArtinMonoidHom K L
    (finitePrimeIdele v)

/-- The arithmetic prime Artin element is the arithmetic chosen local
Artin value of the normalized order-one element. -/
@[simp]
theorem arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin
    (v : HeightOneSpectrum (𝓞 K)) :
    arithmeticFinitePlacePrimeArtin (K := K) (L := L) v =
      Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
        K L v (FiniteIdeleGroup.chosenLocalOrderSection v 1) := by
  rw [arithmeticFinitePlacePrimeArtin, finitePrimeIdele,
    Reciprocity.arithmeticGlobalArtinMonoidHom_finitePlaceIdele]

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_OrdinaryNormClassField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Class fields from ordinary idele-class norm neighbourhoods

An actual finite Galois norm subgroup contained in an ordinary
idele-class subgroup makes the transported subgroup norm-open in the
rational absolute class formation.  Finite abelian classification then
constructs its class field.  The final theorem below transports the
result back to the ordinary idele class group of the actual fixed field,
so its conclusion is an equality of genuine determinant-norm ranges.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open Reciprocity

attribute [local instance] ordinaryNormClassFieldIdeleClassCommGroup

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/- The fixed-field typeclass data used by the topology comparison are kept
behind named constants.  This prevents every consumer from rebuilding the
same finite-dimensional and number-field proof terms while reducing the
dependent fixed-field type. -/

theorem ordinaryNormOpenSubgroup_val
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    (ordinaryNormOpenSubgroup K L H hLH).1 =
      H.toAddSubgroup.map
        (numberFieldTowerIdeleClassEquivAmbientFixed K L).toAddMonoidHom :=
  rfl

/-- A finite Galois norm neighbourhood inside an ordinary idele-class
subgroup produces a finite abelian subextension whose abstract norm
subgroup is exactly the transported ordinary subgroup. -/
theorem exists_finiteAbelianSubextension_normSubgroup_eq_of_normRange_le
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    ∃ M : FiniteAbelianSubextension
        (numberFieldTowerBaseSubgroup K L),
      M.normSubgroup rationalIdeleClassRepresentation =
        (H.toAddSubgroup).map
          (numberFieldTowerIdeleClassEquivAmbientFixed
            K L).toAddMonoidHom := by
  let :=
    numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L
  let B : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    { field := numberFieldTowerBaseSubgroup K L
      finite := numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L }
  let N := ordinaryNormOpenSubgroup K L H hLH
  obtain ⟨M, hM⟩ :
      ∃ M : FiniteAbelianSubextension
          (numberFieldTowerBaseSubgroup K L),
        FiniteAbelianSubextension.normSubgroupMap
            rationalIdeleClassRepresentation M = N :=
    FiniteAbelianSubextension.normSubgroupMap_surjective
      Reciprocity.rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom B N
  refine ⟨M, ?_⟩
  rw [← FiniteAbelianSubextension.normSubgroupMap_val]
  rw [congrArg Subtype.val hM]
  exact ordinaryNormOpenSubgroup_val K L H hLH

/-- The finite abelian subextension selected from an ordinary norm
neighbourhood.  This is the unique choice point for the realization API
below. -/
noncomputable def ordinaryNormClassFieldSubextension
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    FiniteAbelianSubextension (numberFieldTowerBaseSubgroup K L) :=
  Classical.choose
    (exists_finiteAbelianSubextension_normSubgroup_eq_of_normRange_le
      K L H hLH)

/-- The actual relative fixed field of the selected ordinary class-field
subextension. -/
noncomputable abbrev ordinaryNormClassFieldExtension
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) : Type :=
  abstractRelativeFixedField ℚ (SeparableClosure ℚ)
    (ordinaryNormClassFieldSubextension K L H hLH).below

noncomputable instance ordinaryNormClassFieldExtensionIsGalois
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsGalois (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (ordinaryNormClassFieldSubextension K L H hLH).field
    (ordinaryNormClassFieldSubextension K L H hLH).below
    (ordinaryNormClassFieldSubextension K L H hLH).normal

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldConstruction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Construction of a closed finite-index class field

This leaf fixes the finite Galois norm neighbourhood, abstract subextension,
and canonical fixed-field presentation attached to a closed finite-index
idèle-class subgroup. Norm-range and reciprocity statements live in later
leaves so their elaboration environments do not remain resident here.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- The compatible abstract base subgroup used by the selected class
field of `H`. -/
noncomputable abbrev closedFiniteIndexClassFieldBaseSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :=
  numberFieldTowerBaseSubgroup K
    (closedFiniteIndexClassFieldNormAmbient
      (K := K) H hclosed)

/-- The canonical fixed-field copy of the original number field used
by the selected class field of `H`. -/
noncomputable abbrev closedFiniteIndexClassFieldBase
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] : Type :=
  ordinaryNormClassFieldBase K
    (closedFiniteIndexClassFieldNormAmbient
      (K := K) H hclosed)

/-- The actual finite abelian class field selected by `H`. -/
noncomputable abbrev closedFiniteIndexClassField
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] : Type :=
  ordinaryNormClassFieldExtension K
    (closedFiniteIndexClassFieldNormAmbient
      (K := K) H hclosed) H
    (closedFiniteIndexClassFieldNormAmbient_normRange_le
      (K := K) H hclosed)

/-- The canonical equivalence from the original number field to the
fixed-field base of its selected class field. -/
noncomputable abbrev closedFiniteIndexClassFieldBaseEquiv
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    K ≃ₐ[ℚ]
      closedFiniteIndexClassFieldBase
        (K := K) H hclosed :=
  ordinaryNormClassFieldBaseEquiv K
    (closedFiniteIndexClassFieldNormAmbient
      (K := K) H hclosed)
end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldOriginalField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.idealArtinMap_primeToIdealMap _root_.GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.primeToIdealMap_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdeleQuotient_mk_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup_of _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicGalEquivZHat_extensionClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicGalEquivZHat_quotientClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_extensionClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHomOfEmbedding_apply _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractFieldEquiv_algebraMap _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryBaseEmbedding_coe _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryTopEmbedding_coe _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_ideleClassNorm _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Transport to the original number field

This leaf installs the original-field algebra tower and transports the
canonical norm-range computation back to the original idèle class group.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- The canonical fixed-field copy, regarded as an algebra over the
original number field. -/
noncomputable instance closedFiniteIndexClassFieldBaseAlgebraOverOriginal
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Algebra K
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed) :=
  (closedFiniteIndexClassFieldBaseEquiv
    (K := K) H hclosed).toRingHom.toAlgebra

/-- The selected class field, regarded as an algebra over the original
number field through its canonical fixed-field copy. -/
noncomputable instance closedFiniteIndexClassFieldAlgebraOverOriginal
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    Algebra K
      (closedFiniteIndexClassField
        (K := K) H hclosed) :=
  ((algebraMap
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed)
      (closedFiniteIndexClassField
        (K := K) H hclosed)).comp
    (algebraMap K
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed))).toAlgebra

/-- The scalar map into the selected class field is the canonical base
equivalence followed by fixed-field inclusion. -/
@[simp]
theorem closedFiniteIndexClassField_algebraMap_original
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]
    (x : K) :
    algebraMap K
        (closedFiniteIndexClassField
          (K := K) H hclosed) x =
      algebraMap
        (closedFiniteIndexClassFieldBase
          (K := K) H hclosed)
        (closedFiniteIndexClassField
          (K := K) H hclosed)
        (closedFiniteIndexClassFieldBaseEquiv
          (K := K) H hclosed x) :=
  rfl

noncomputable instance closedFiniteIndexClassFieldScalarTowerOverOriginal
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    IsScalarTower K
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed)
      (closedFiniteIndexClassField
        (K := K) H hclosed) :=
  IsScalarTower.of_algebraMap_eq' rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldReciprocity_Topological_Construction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Continuous closed finite-index class-field reciprocity

The final equivalence composes finite global reciprocity with the generic
continuous transport induced by the exact norm-range equality.  Equality
elimination preserves the native quotient topology, so no discrete topology
instances are reconstructed here.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

/-- Canonical class-group commutativity supplies normality for the two quotients. -/
theorem closedFiniteIndexTopologicalClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] closedFiniteIndexTopologicalClassGroupIsMulCommutative

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldReciprocity_Topological_EvaluationValue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Named value of closed finite-index reciprocity

The expanded inverse norm-residue expression is kept behind one reducible
value provider.  Public evaluation statements can therefore mention the
selected class-field instance tower once while remaining definitionally
equivalent to the historical formula.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

/-- Canonical class-group commutativity supplies normality for norm-range transport. -/
theorem closedFiniteIndexEvaluationValueClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] closedFiniteIndexEvaluationValueClassGroupIsMulCommutative

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldReciprocity_Topological_EvaluationCore
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Generic evaluation core for transported reciprocity

This theorem works for an arbitrary finite abelian extension and subgroup
equality.  It proves the composition formula once without unfolding a
domain-specific selected-field construction.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

/-- Canonical class-group commutativity supplies normality in the transport formula. -/
theorem closedFiniteIndexEvaluationCoreClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] closedFiniteIndexEvaluationCoreClassGroupIsMulCommutative

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldReciprocity_Algebraic_Construction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Underlying algebraic closed finite-index reciprocity

The algebraic equivalence is obtained by forgetting topology from the named
continuous provider.  This avoids a second specialization of the full finite
global reciprocity instance tower.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

/-- Canonical class-group commutativity supplies normality of the defining subgroup. -/
theorem closedFiniteIndexAlgebraicClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] closedFiniteIndexAlgebraicClassGroupIsMulCommutative

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ClosedFiniteIndexClassFieldReciprocity_GlobalNormResidue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Norm-residue evaluation for a closed finite-index class field

This leaf proves that the selected class-field reciprocity equivalence sends
the global norm-residue symbol to the corresponding quotient class.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

/-- Canonical class-group commutativity supplies normality for quotient evaluation. -/
theorem closedFiniteIndexNormResidueClassGroupIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] closedFiniteIndexNormResidueClassGroupIsMulCommutative

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_HilbertClassFieldRealization
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Actual realizations of the Hilbert class fields

The big and small Hilbert norm subgroups are closed and have finite
index.  The finite-index class-field construction therefore supplies
genuine finite abelian subextensions of the rational separable closure.
This file fixes those subextensions once and for all, names their actual
relative fixed fields, and identifies their determinant-norm ranges.

The resulting degrees are the orders of the corresponding reciprocity
quotients: the narrow class number for the big Hilbert class field and
the ordinary class number for the small Hilbert class field.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open NumberField
open Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- The big-Hilbert congruence subgroup has finite index, registered at
the realization layer where the closed finite-index construction uses it. -/
instance bigHilbertClassFieldNormSubgroupFiniteIndex :
    (bigHilbertClassFieldNormSubgroup (K := K)).FiniteIndex := by
  unfold bigHilbertClassFieldNormSubgroup
  infer_instance

/-- The concrete finite Galois norm neighbourhood used to realize the
big Hilbert class field. -/
noncomputable abbrev bigHilbertClassFieldNormAmbient (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassFieldNormAmbient
    (K := K)
    (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The compatible abstract base subgroup for the actual big Hilbert
class-field realization. -/
noncomputable abbrev bigHilbertClassFieldBaseSubgroup (K : Type)
    [Field K] [NumberField K] :=
  closedFiniteIndexClassFieldBaseSubgroup
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The compatible actual copy of the original number field occurring
as the base fixed field in the big-Hilbert realization. -/
noncomputable abbrev bigHilbertClassFieldBase (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassFieldBase
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The actual big Hilbert class field selected inside the rational
separable closure. -/
noncomputable abbrev bigHilbertClassField (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassField
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The canonical equivalence from `K` to the actual base fixed field
used by the selected big Hilbert class field. -/
noncomputable abbrev bigHilbertClassFieldBaseEquiv :
    K ≃ₐ[ℚ] bigHilbertClassFieldBase K :=
  closedFiniteIndexClassFieldBaseEquiv
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The compatible actual copy of the original number field occurring
as the base fixed field in the small-Hilbert realization. -/
noncomputable abbrev smallHilbertClassFieldBase (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassFieldBase
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The actual small Hilbert class field selected inside the rational
separable closure. -/
noncomputable abbrev smallHilbertClassField (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassField
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The canonical equivalence from `K` to the actual base fixed field
used by the selected small Hilbert class field. -/
noncomputable abbrev smallHilbertClassFieldBaseEquiv :
    K ≃ₐ[ℚ] smallHilbertClassFieldBase K :=
  closedFiniteIndexClassFieldBaseEquiv
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_BigHilbertClassFieldOverOriginalBase
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.idealArtinMap_primeToIdealMap _root_.GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.primeToIdealMap_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdeleQuotient_mk_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup_of _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicGalEquivZHat_extensionClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicGalEquivZHat_quotientClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_extensionClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHomOfEmbedding_apply _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractFieldEquiv_algebraMap _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryBaseEmbedding_coe _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryTopEmbedding_coe _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_ideleClassNorm _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The big Hilbert class field over the original number field

The selected big Hilbert class field is constructed over a canonical
fixed-field copy of the input number field.  The canonical equivalence
with the original field supplies the actual scalar map used here.  Thus
the selected field is a finite abelian Galois extension of the original
number field, with degree equal to the narrow class number.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

variable (K : Type) [Field K] [NumberField K]

/-- The canonical base fixed field of the big Hilbert realization,
regarded as an algebra over the original number field. -/
noncomputable instance bigHilbertClassFieldBaseAlgebraOverOriginal :
    Algebra K (bigHilbertClassFieldBase K) :=
  (bigHilbertClassFieldBaseEquiv (K := K)).toRingHom.toAlgebra

/-- The selected big Hilbert class field as an algebra over the
original number field. -/
noncomputable instance bigHilbertClassFieldAlgebraOverOriginal :
    Algebra K (bigHilbertClassField K) :=
  ((algebraMap
      (bigHilbertClassFieldBase K)
      (bigHilbertClassField K)).comp
    (algebraMap K
      (bigHilbertClassFieldBase K))).toAlgebra

/-- The scalar map into the selected big Hilbert class field is the
canonical base equivalence followed by fixed-field inclusion. -/
@[simp]
theorem bigHilbertClassField_algebraMap_original
    (x : K) :
    algebraMap K (bigHilbertClassField K) x =
      algebraMap
        (bigHilbertClassFieldBase K)
        (bigHilbertClassField K)
        (bigHilbertClassFieldBaseEquiv (K := K) x) :=
  rfl

/-- The original field, its fixed-field copy, and the selected big
Hilbert class field form the literal scalar tower. -/
noncomputable instance bigHilbertClassFieldScalarTowerOverOriginal :
    IsScalarTower K
      (bigHilbertClassFieldBase K)
      (bigHilbertClassField K) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The selected big Hilbert class field is Galois over the original
number field. -/
noncomputable instance bigHilbertClassFieldIsGaloisOverOriginal :
    IsGalois K (bigHilbertClassField K) := by
  let e :=
    bigHilbertClassFieldBaseEquiv (K := K)
  apply IsGalois.of_equiv_equiv
    (F := bigHilbertClassFieldBase K)
    (E := bigHilbertClassField K)
    (f := e.symm.toRingEquiv)
    (g := RingEquiv.refl (bigHilbertClassField K))
  apply RingHom.ext
  intro x
  calc
    ((algebraMap K (bigHilbertClassField K)).comp
        e.symm.toRingEquiv) x =
        algebraMap K (bigHilbertClassField K) (e.symm x) := rfl
    _ = algebraMap
          (bigHilbertClassFieldBase K)
          (bigHilbertClassField K)
          (bigHilbertClassFieldBaseEquiv (K := K) (e.symm x)) :=
      bigHilbertClassField_algebraMap_original
        (K := K) (e.symm x)
    _ = algebraMap
          (bigHilbertClassFieldBase K)
          (bigHilbertClassField K) x := by
      simpa only [e] using
        congrArg
          (algebraMap
            (bigHilbertClassFieldBase K)
            (bigHilbertClassField K))
          ((bigHilbertClassFieldBaseEquiv
            (K := K)).apply_symm_apply x)
    _ = ((RingEquiv.refl
            (bigHilbertClassField K)).toRingHom.comp
          (algebraMap
            (bigHilbertClassFieldBase K)
            (bigHilbertClassField K))) x := rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_FiniteAbelianClassFieldContainment
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Containment of finite abelian class fields

For actual finite abelian extensions of a number field, containment is
exactly reverse containment of their genuine idèle-class norm ranges.

The proof first realizes an arbitrary extension in the same rational
separable closure as the class field selected by a closed finite-index
subgroup.  The abstract finite-abelian classification then gives a
literal inclusion of fixing subgroups, which restricts the chosen
ambient embedding to an actual algebra embedding into the selected
class field.  Applying this construction to the norm range of a second
extension yields the intrinsic containment criterion over the original
number field.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open NumberField
open RamificationTheory
open Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- The distinguished embedding of the original number field into the
rational separable closure underlying the class field selected by
`H`. -/
noncomputable def closedFiniteIndexClassFieldBaseEmbedding
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    K →ₐ[ℚ] SeparableClosure ℚ :=
  numberFieldTowerLowerEmbedding K
    (closedFiniteIndexClassFieldNormAmbient
      (K := K) H hclosed)

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SmallHilbertClassFieldOverOriginalBase
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassField_algebraMap_original _root_.GlobalClassFieldTheory.GlobalClassFields.idealArtinMap_primeToIdealMap _root_.GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.primeToIdealMap_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdeleQuotient_mk_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup_of _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicGalEquivZHat_extensionClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicGalEquivZHat_quotientClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_extensionClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHomOfEmbedding_apply _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractFieldEquiv_algebraMap _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryBaseEmbedding_coe _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryTopEmbedding_coe _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_ideleClassNorm _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The small Hilbert class field over the original number field

The finite class-field construction realizes the small Hilbert class
field over a canonical fixed-field copy of the input number field.
The fixed-field copy is canonically `ℚ`-algebra equivalent to the
original field.  This file uses that equivalence as the actual scalar
map, so the selected Hilbert class field becomes a finite abelian
Galois extension of the original field itself.

This is the scalar structure used by the final extension-of-ideals map
in the principal ideal theorem.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

variable (K : Type) [Field K] [NumberField K]

/-- The canonical fixed-field copy underlying the selected small
Hilbert class field, regarded as an algebra over the original number
field. -/
noncomputable instance smallHilbertClassFieldBaseAlgebraOverOriginal :
    Algebra K (smallHilbertClassFieldBase K) :=
  (smallHilbertClassFieldBaseEquiv (K := K)).toRingHom.toAlgebra

/-- The selected small Hilbert class field, regarded as an algebra over
the original number field through the canonical fixed-field copy. -/
noncomputable instance smallHilbertClassFieldAlgebraOverOriginal :
    Algebra K (smallHilbertClassField K) :=
  ((algebraMap
      (smallHilbertClassFieldBase K)
      (smallHilbertClassField K)).comp
    (algebraMap K
      (smallHilbertClassFieldBase K))).toAlgebra

/-- The scalar map from the original number field into the selected
small Hilbert class field is literally the canonical base equivalence
followed by the fixed-field inclusion. -/
@[simp]
theorem smallHilbertClassField_algebraMap_original
    (x : K) :
    algebraMap K (smallHilbertClassField K) x =
      algebraMap
        (smallHilbertClassFieldBase K)
        (smallHilbertClassField K)
        (smallHilbertClassFieldBaseEquiv (K := K) x) :=
  rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_HilbertClassFieldMaximalSubextension
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.idealArtinMap_primeToIdealMap _root_.GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_rayPrimeClass _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.primeToIdealMap_finitePrimeIdele _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo _root_.GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdeleQuotient_mk_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_apply _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealArtinGaloisMap_ker _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivGaloisGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.idealClassQuotientEquivNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.rayClassToNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalArtinMonoidHom_infinitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue _root_.GlobalClassFieldTheory.Reciprocity.arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationIdeleMonoidHom_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_apply _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_eq_one_iff _root_.GlobalClassFieldTheory.Reciprocity.globalNormResidueAbelianizationMonoidHom_ker _root_.GlobalClassFieldTheory.Reciprocity.globalReciprocityAbelianizationContinuousMulEquiv_apply _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The maximal finite-unramified abelian subextension

The selected big Hilbert class field is characterized here in actual
field order.  Its abstract norm subgroup in the rational absolute
idele-class formation is identified exactly with the intrinsic
big-Hilbert subgroup of its fixed-field base.  Every finite abelian
subextension whose actual fixed-field extension is unramified at all
finite places has a larger norm subgroup, hence lies below the selected
big Hilbert class field by the order-reversing finite classification.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation KummerTheory
open LocalClassFieldTheory NumberField Reciprocity

/-- The fixed-field idele-class equivalence at the selected big-Hilbert
base, named once so later subgroup comparisons do not reconstruct it. -/
noncomputable def bigHilbertClassFieldMaximalIdeleClassEquiv
    (K : Type) [Field K] [NumberField K] :
    Additive (IdeleClassGroup (bigHilbertClassFieldBase K)) ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (bigHilbertClassFieldBaseSubgroup K) :=
  rationalAbstractFixedFieldIdeleClassEquivFixed
    (bigHilbertClassFieldBaseSubgroup K)

/-!
## Maximality over the original number field

The preceding order statement lives over the fixed-field copy of the
base used by the rational absolute class formation.  We now embed an
arbitrary actual finite abelian extension `E / K` compatibly with that
copy, apply the fixed-field maximality theorem there, and restrict its
ambient embedding to the selected big Hilbert class field.
-/

/-- The distinguished embedding of the original number field into the
rational separable closure underlying the selected big Hilbert class
field. -/
noncomputable def bigHilbertClassFieldBaseEmbedding
    (K : Type) [Field K] [NumberField K] :
    K →ₐ[ℚ] SeparableClosure ℚ :=
  numberFieldTowerLowerEmbedding K
    (bigHilbertClassFieldNormAmbient K)

/-- The canonical fixed-field equivalence has the distinguished base
embedding as its underlying map into the rational separable closure. -/
@[simp]
theorem bigHilbertClassFieldBaseEquiv_coe
    (K : Type) [Field K] [NumberField K]
    (x : K) :
    ((bigHilbertClassFieldBaseEquiv (K := K) x :
        bigHilbertClassFieldBase K) :
      SeparableClosure ℚ) =
      bigHilbertClassFieldBaseEmbedding K x := by
  rfl

end GlobalClassFields
end GlobalClassFieldTheory
end
end


