-- Prove2me | Definitions.Def_OAIQ244Duke009
-- name    : OAIQ244Duke009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:11:29.462192+00:00
-- url     : https://prove2.me/theorems/48af8f27-3e7d-4b29-ab2e-40a076c82c01
-- title:
--   Definitions bundle OAIQ244Duke009 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 145 declarations of OpenAI's Lean: 47 definitions, 18 instances and 80 theorems. The definitions and types are `GlobalClassFieldTheory.ClassFieldAxiom.globalFieldNormSubgroup`, `GlobalClassFieldTheory.Reciprocity.cyclotomicAbstractFixedFieldArtin_separableClosureAlgebra`, `GlobalClassFieldTheory.Reciprocity.padicIntUnitOfRat`, `GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceConjugation`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicAdicAbsoluteValue`, `GlobalClassFieldTheory.Reciprocity.rationalPositiveArchimedeanLocalComponent`, `GlobalClassFieldTheory.Reciprocity.rationalSignPadicUnit`, `IdeleGroup.finitePlaceValue`, `IdeleGroup.infinitePlaceValue`, `KummerTheory.continuousMulEquivPiCongr`, `KummerTheory.continuousPiMultiplicative`, `KummerTheory.rationalCyclotomicCharacterPrimeProduct`, `KummerTheory.rationalCyclotomicField`, `KummerTheory.rationalCyclotomicLevel`, `KummerTheory.rationalCyclotomicTorsionClosure`, `KummerTheory.rationalCyclotomicTorsionFixedField`, `LocalClassFieldTheory.ambientEmbeddedSeparableClosureEquiv`, `LocalClassFieldTheory.finiteSeparableAlgHomFintypeRelative`, `LocalClassFieldTheory.towerLowerEmbedding`, `LocalClassFieldTheory.valuationSubringEquivOfComapEq`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.continuousMulEquivOfCompactToT2`, `LocalFieldTheory.Padic.continuousMulEquivProdAssoc`, `LocalFieldTheory.Padic.continuousMulEquivProdCongr`, `LocalFieldTheory.Padic.continuousMultiplicativeEquivOfAddEquiv`, `LocalFieldTheory.Padic.padicFreeContinuousAddEquivOfEq`, `LocalFieldTheory.Padic.prodMultiplicativeContinuousMulEquiv`, `LocalFieldTheory.QuotientGroup.continuousCongr`, `LocalFieldTheory.finiteExtensionSpectralNormedAlgebra`, `LocalFieldTheory.finiteExtensionSpectralNormedField`, `LocalFieldTheory.finiteExtensionSpectralValuativeRel`, `LocalFieldTheory.localFieldNontriviallyNormedField`, `RamificationTheory.Field.absoluteGaloisGroup.ofIntermediateFieldInExtension`, `RamificationTheory.Field.absoluteGaloisGroup.semilinearRingEquivPreimageIntermediateField`, `RayClass.rationalPrime`, `RayClass.realCompletionContinuousMulEquiv`, `RayClass.realPlaceSign`, `RelativeIdeleGroup.relativeInfinitePlaceValue`, `cyclicDegreePrime`, `cyclicGaloisGenerator`, `cyclicPrimeDegreeIntermediate` and 7 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Galois_CyclicPrimeDegreeSubextension`, `AlgebraicNumberTheory_Galois_InfiniteBaseChange`, `AlgebraicNumberTheory_Idele_SinglePlace`, `AlgebraicNumberTheory_NormalClosure`, `AlgebraicNumberTheory_Ramification_Splitting_NormalClosure`, `AlgebraicNumberTheory_Ramification_Splitting_PrimeOrderFixedField`, `AlgebraicNumberTheory_RayClass_Rational`, `AlgebraicNumberTheory_RayClass_Topology`, `AlgebraicNumberTheory_TensorProduct`, `GlobalClassFieldTheory_ClassFieldAxiom_HasseNormPrinciple`, `GlobalClassFieldTheory_ClassFieldAxiom_KummerLocalNormContainment`, `GlobalClassFieldTheory_Reciprocity_CyclotomicAbstractFixedFieldArtin`, `GlobalClassFieldTheory_Reciprocity_FiniteIdeleArtin`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_CrossLocalRestriction`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin`, `GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlace`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicLocalization`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalAwayProduct`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalProduct`, `GlobalClassFieldTheory_Reciprocity_RationalPrimeFactorization`, `GroupTheory_Finite`, `KummerTheory_Concrete_CyclotomicPrimeBaseChange`, `Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_Basic`, `Kummer_Concrete_Cyclotomic_RationalCyclotomicCharacter`, `Kummer_Concrete_Cyclotomic_RationalCyclotomicCharacterEquiv`, `Kummer_Concrete_Cyclotomic_RationalCyclotomicField`, `Kummer_Concrete_Cyclotomic_RationalCyclotomicTorsionField`, `LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityCanonical`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientNormResidue`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeWitness`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldLocalData`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldRelativeNorm`, `LocalClassFieldTheory_Finite_LocalReciprocity_GeneralTowerNaturality`, `LocalField_DiscreteValuationField_FieldUnitFactors`, `LocalField_GroupTheory_ContinuousQuotientEquiv`, `LocalField_NonarchimedeanLocalField_FiniteExtensionTopology`, `LocalField_Padic_UnitDecomposition`, `Ramification_GaloisValuation_AbsoluteGalois_InfiniteGaloisCorrespondence`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke021`.
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

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Galois_CyclicPrimeDegreeSubextension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# A prime-degree intermediate field of a finite cyclic extension

This file supplies an induction field for finite cyclic extensions.
If `L / K` is a nontrivial finite cyclic Galois extension, choose a
prime `p ∣ [L : K]`.  For a generator `σ` of its Galois group, the
subgroup generated by `σ ^ p` has index `p`.  Its fixed field is
therefore an actual cyclic Galois extension of `K` of degree `p`, while
the remaining extension has degree `[L : K] / p`.
-/

noncomputable section

variable {K L : Type}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]

local notation "G" => L ≃ₐ[K] L

/-- A fixed generator of the cyclic Galois group. -/
noncomputable def cyclicGaloisGenerator : G :=
  (IsCyclic.exists_generator (α := G)).choose

omit [FiniteDimensional K L] [IsGalois K L] in
theorem mem_zpowers_cyclicGaloisGenerator (σ : G) :
    σ ∈ Subgroup.zpowers
      (cyclicGaloisGenerator (K := K) (L := L)) :=
  (IsCyclic.exists_generator (α := G)).choose_spec σ

theorem orderOf_cyclicGaloisGenerator :
    orderOf (cyclicGaloisGenerator (K := K) (L := L)) =
      Module.finrank K L := by
  rw [orderOf_eq_card_of_forall_mem_zpowers
    (mem_zpowers_cyclicGaloisGenerator (K := K) (L := L))]
  exact IsGalois.card_aut_eq_finrank K L

/-- A prime divisor of the degree of a nontrivial cyclic extension. -/
noncomputable def cyclicDegreePrime
    (hdegree : 1 < Module.finrank K L) : ℕ :=
  (Nat.exists_prime_and_dvd
    (ne_of_gt hdegree)).choose

omit [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] in
theorem cyclicDegreePrime_prime
    (hdegree : 1 < Module.finrank K L) :
    (cyclicDegreePrime (K := K) (L := L) hdegree).Prime :=
  (Nat.exists_prime_and_dvd
    (ne_of_gt hdegree)).choose_spec.1

omit [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] in
theorem cyclicDegreePrime_dvd_finrank
    (hdegree : 1 < Module.finrank K L) :
    cyclicDegreePrime (K := K) (L := L) hdegree ∣
      Module.finrank K L :=
  (Nat.exists_prime_and_dvd
    (ne_of_gt hdegree)).choose_spec.2

/-- The subgroup generated by `σ ^ p`; it has index `p`. -/
noncomputable def cyclicPrimeDegreeSubgroup
    (hdegree : 1 < Module.finrank K L) :
    Subgroup G :=
  Subgroup.zpowers
    ((cyclicGaloisGenerator (K := K) (L := L)) ^
      cyclicDegreePrime (K := K) (L := L) hdegree)

theorem cyclicPrimeDegreeSubgroup_card
    (hdegree : 1 < Module.finrank K L) :
    Nat.card
        (cyclicPrimeDegreeSubgroup
          (K := K) (L := L) hdegree) =
      Module.finrank K L /
        cyclicDegreePrime (K := K) (L := L) hdegree := by
  rw [cyclicPrimeDegreeSubgroup, Nat.card_zpowers,
    orderOf_pow_of_dvd
      (cyclicDegreePrime_prime
        (K := K) (L := L) hdegree).ne_zero
      (by
        rw [orderOf_cyclicGaloisGenerator]
        exact cyclicDegreePrime_dvd_finrank
          (K := K) (L := L) hdegree),
    orderOf_cyclicGaloisGenerator]

theorem cyclicPrimeDegreeSubgroup_index
    (hdegree : 1 < Module.finrank K L) :
    (cyclicPrimeDegreeSubgroup
      (K := K) (L := L) hdegree).index =
        cyclicDegreePrime (K := K) (L := L) hdegree := by
  let P :=
    cyclicPrimeDegreeSubgroup
      (K := K) (L := L) hdegree
  let p :=
    cyclicDegreePrime (K := K) (L := L) hdegree
  have hp : p.Prime :=
    cyclicDegreePrime_prime
      (K := K) (L := L) hdegree
  have hpDvd : p ∣ Module.finrank K L :=
    cyclicDegreePrime_dvd_finrank
      (K := K) (L := L) hdegree
  have hcardP :
      Nat.card P = Module.finrank K L / p :=
    cyclicPrimeDegreeSubgroup_card
      (K := K) (L := L) hdegree
  have hcardG :
      Nat.card G = Module.finrank K L :=
    IsGalois.card_aut_eq_finrank K L
  have hmul :
      (Module.finrank K L / p) * P.index =
        Module.finrank K L := by
    simpa only [hcardP, ← Nat.card_eq_fintype_card, hcardG] using
      P.card_mul_index
  have hdivpos :
      0 < Module.finrank K L / p :=
    Nat.div_pos
      (Nat.le_of_dvd Module.finrank_pos hpDvd)
      hp.pos
  apply Nat.mul_left_cancel hdivpos
  calc
    (Module.finrank K L / p) * P.index =
        Module.finrank K L := hmul
    _ = (Module.finrank K L / p) * p :=
      (Nat.div_mul_cancel hpDvd).symm

noncomputable instance cyclicPrimeDegreeSubgroup_normal
    (hdegree : 1 < Module.finrank K L) :
    (cyclicPrimeDegreeSubgroup
      (K := K) (L := L) hdegree).Normal :=
  inferInstance

/-- The fixed field of the chosen index-prime subgroup. -/
noncomputable def cyclicPrimeDegreeIntermediate
    (hdegree : 1 < Module.finrank K L) :
    IntermediateField K L :=
  IntermediateField.fixedField
    (cyclicPrimeDegreeSubgroup
      (K := K) (L := L) hdegree)

noncomputable instance cyclicPrimeDegreeIntermediate_isGalois
    (hdegree : 1 < Module.finrank K L) :
    IsGalois K
      (cyclicPrimeDegreeIntermediate
        (K := K) (L := L) hdegree) := by
  unfold cyclicPrimeDegreeIntermediate
  infer_instance

theorem cyclicPrimeDegreeIntermediate_finrank
    (hdegree : 1 < Module.finrank K L) :
    Module.finrank K
        (cyclicPrimeDegreeIntermediate
          (K := K) (L := L) hdegree) =
      cyclicDegreePrime (K := K) (L := L) hdegree := by
  let P :=
    cyclicPrimeDegreeSubgroup
      (K := K) (L := L) hdegree
  let M :=
    cyclicPrimeDegreeIntermediate
      (K := K) (L := L) hdegree
  let : P.Normal :=
    cyclicPrimeDegreeSubgroup_normal
      (K := K) (L := L) hdegree
  let : IsGalois K M :=
    cyclicPrimeDegreeIntermediate_isGalois
      (K := K) (L := L) hdegree
  calc
    Module.finrank K M =
        Nat.card (M ≃ₐ[K] M) :=
      (IsGalois.card_aut_eq_finrank K M).symm
    _ = Nat.card (G ⧸ P) :=
      Nat.card_congr
        (IsGalois.normalAutEquivQuotient P).symm.toEquiv
    _ = P.index := by
      rw [P.index_eq_card]
    _ = cyclicDegreePrime (K := K) (L := L) hdegree :=
      cyclicPrimeDegreeSubgroup_index
        (K := K) (L := L) hdegree

theorem cyclicPrimeDegreeIntermediate_top_finrank
    (hdegree : 1 < Module.finrank K L) :
    Module.finrank
        (cyclicPrimeDegreeIntermediate
          (K := K) (L := L) hdegree)
        L =
      Module.finrank K L /
        cyclicDegreePrime (K := K) (L := L) hdegree := by
  unfold cyclicPrimeDegreeIntermediate
  rw [IntermediateField.finrank_fixedField_eq_card,
    cyclicPrimeDegreeSubgroup_card]

noncomputable instance cyclicPrimeDegreeIntermediate_top_isGalois
    (hdegree : 1 < Module.finrank K L) :
    IsGalois
      (cyclicPrimeDegreeIntermediate
        (K := K) (L := L) hdegree)
      L := by
  unfold cyclicPrimeDegreeIntermediate
  exact
    IsGalois.of_fixed_field L
      (cyclicPrimeDegreeSubgroup
        (K := K) (L := L) hdegree)

noncomputable instance cyclicPrimeDegreeIntermediate_base_isCyclic
    (hdegree : 1 < Module.finrank K L) :
    IsCyclic
      (cyclicPrimeDegreeIntermediate
          (K := K) (L := L) hdegree ≃ₐ[K]
        cyclicPrimeDegreeIntermediate
          (K := K) (L := L) hdegree) := by
  let P :=
    cyclicPrimeDegreeSubgroup
      (K := K) (L := L) hdegree
  let : P.Normal :=
    cyclicPrimeDegreeSubgroup_normal
      (K := K) (L := L) hdegree
  exact
    (IsGalois.normalAutEquivQuotient P).isCyclic.mp
      (isCyclic_of_surjective
        (QuotientGroup.mk' P)
        (QuotientGroup.mk'_surjective P))

noncomputable instance cyclicPrimeDegreeIntermediate_top_isCyclic
    (hdegree : 1 < Module.finrank K L) :
    IsCyclic
      (L ≃ₐ[
        cyclicPrimeDegreeIntermediate
          (K := K) (L := L) hdegree] L) := by
  let P :=
    cyclicPrimeDegreeSubgroup
      (K := K) (L := L) hdegree
  exact
    (IntermediateField.subgroupEquivAlgEquiv P).isCyclic.mp
      (inferInstance : IsCyclic P)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Galois_InfiniteBaseChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Infinite Galois base change from finite layers

This module supplies the field-theoretic passage from finite Galois layers to
their union after a change of base field.  It is stated entirely in terms of
mathlib's actual intermediate fields and uses no abstract replacement for the
compositum.
-/

noncomputable section

namespace IntermediateField

variable {R U : Type*} [Field R] [Field U] [Algebra R U]

/-- A Galois intermediate field is the union of the lifts of its finite
Galois intermediate subfields. -/
theorem le_iSup_lift_finiteGalois
    (B : IntermediateField R U) [IsGalois R B] :
    B ≤ ⨆ E : FiniteGaloisIntermediateField R B,
      IntermediateField.lift E.toIntermediateField := by
  intro x hx
  let xB : B := ⟨x, hx⟩
  let E : FiniteGaloisIntermediateField R B :=
    FiniteGaloisIntermediateField.adjoin R {xB}
  have hxE : xB ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin R {xB}
      (Set.mem_singleton xB)
  exact
    (le_iSup
      (fun E : FiniteGaloisIntermediateField R B =>
        IntermediateField.lift E.toIntermediateField)
      E)
      ((IntermediateField.mem_lift xB).2 hxE)

/-- A compositum with a Galois intermediate field is the supremum of the
composita with its finite Galois intermediate layers. -/
theorem sup_eq_iSup_finiteGaloisComposita
    (A B : IntermediateField R U) [IsGalois R B] :
    A ⊔ B = ⨆ E : FiniteGaloisIntermediateField R B,
      A ⊔ IntermediateField.lift E.toIntermediateField := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · let E0 : FiniteGaloisIntermediateField R B := ⊥
      exact
        le_trans le_sup_left
          (le_iSup
            (fun E : FiniteGaloisIntermediateField R B =>
              A ⊔ IntermediateField.lift E.toIntermediateField)
            E0)
    · exact
        (le_iSup_lift_finiteGalois B).trans
          (iSup_mono fun E =>
            (show IntermediateField.lift E.toIntermediateField ≤
              A ⊔ IntermediateField.lift E.toIntermediateField from
              le_sup_right))
  · refine iSup_le fun E => ?_
    exact
      sup_le le_sup_left
        ((IntermediateField.lift_le E.toIntermediateField).trans le_sup_right)

/-- Base change commutes with the supremum of finite Galois composita. -/
theorem extendScalars_sup_eq_iSup_finiteGaloisComposita
    (A B : IntermediateField R U) [IsGalois R B] :
    IntermediateField.extendScalars (F := A) (E := A ⊔ B) le_sup_left =
      ⨆ E : FiniteGaloisIntermediateField R B,
        IntermediateField.extendScalars (F := A)
          (E := A ⊔ IntermediateField.lift E.toIntermediateField)
          le_sup_left := by
  apply le_antisymm
  · apply (IntermediateField.extendScalars_le_iff le_sup_left _).2
    rw [sup_eq_iSup_finiteGaloisComposita]
    refine iSup_le fun E => ?_
    exact
      (IntermediateField.extendScalars_le_iff le_sup_left _).1
        (le_iSup
          (fun E : FiniteGaloisIntermediateField R B =>
            IntermediateField.extendScalars (F := A)
              (E := A ⊔ IntermediateField.lift E.toIntermediateField)
              le_sup_left)
          E)
  · refine iSup_le fun E => ?_
    apply (IntermediateField.extendScalars_le_iff le_sup_left _).2
    rw [IntermediateField.extendScalars_restrictScalars]
    exact
      sup_le le_sup_left
        ((IntermediateField.lift_le E.toIntermediateField).trans le_sup_right)

/-- If every finite Galois layer of a compositum remains Galois after base
change, then so does the full compositum. -/
theorem isGalois_extendScalars_sup_of_forall_finiteGalois
    (A B : IntermediateField R U) [IsGalois R B]
    (hG : ∀ E : FiniteGaloisIntermediateField R B,
      IsGalois A
        (IntermediateField.extendScalars (F := A)
          (E := A ⊔ IntermediateField.lift E.toIntermediateField)
          le_sup_left)) :
    IsGalois A
      (IntermediateField.extendScalars (F := A) (E := A ⊔ B) le_sup_left) := by
  let C : IntermediateField A U :=
    IntermediateField.extendScalars (F := A) (E := A ⊔ B) le_sup_left
  let finiteLayer :
      FiniteGaloisIntermediateField R B → IntermediateField A U :=
    fun E =>
      IntermediateField.extendScalars (F := A)
        (E := A ⊔ IntermediateField.lift E.toIntermediateField)
        le_sup_left
  let : ∀ E : FiniteGaloisIntermediateField R B,
      IsGalois A (finiteLayer E) :=
    fun E => by
      simpa only [finiteLayer] using hG E
  have hC : C = ⨆ E : FiniteGaloisIntermediateField R B, finiteLayer E := by
    simpa only [C, finiteLayer] using
      extendScalars_sup_eq_iSup_finiteGaloisComposita A B
  change IsGalois A C
  rw [hC]
  exact {
    to_isSeparable := IntermediateField.isSeparable_iSup A U
    to_normal := IntermediateField.normal_iSup A U finiteLayer }

end IntermediateField
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The congruence topology on the idele class group

The local higher-unit groups are open,
the ray congruence subgroups are open (and hence closed) of finite index, and
the congruence subgroups are cofinal among the closed finite-index subgroups
of the idele class group.
-/

open scoped Classical NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain
open Topology

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-- An irreducible element of the valuation ring of a finite completion
has norm strictly less than one. -/
theorem local_irreducible_norm_lt_one
    (v : HeightOneSpectrum (𝓞 K))
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    ‖ϖ‖ < 1 := by
  change
    ‖((ϖ : v.adicCompletionIntegers K) :
      v.adicCompletion K)‖ < 1
  apply Valued.toNormedField.norm_lt_one_iff.mpr
  simpa only using!
    ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      K v).valuation_irreducible_lt_one hϖ)

/-- The multiplicative topological equivalence between a real infinite
completion and `ℝ`. -/
def realCompletionContinuousMulEquiv
    (v : InfinitePlace K) (hv : v.IsReal) :
    v.Completion ≃ₜ* ℝ where
  __ :=
    (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMulEquiv
  continuous_toFun :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
  continuous_invFun :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous

/-- The sign of a unit at a real infinite place. -/
def realPlaceSign
    (v : {w : InfinitePlace K // w.IsReal}) :
    v.1.Completionˣ →* SignTypeˣ :=
  (Units.map signHom.toMonoidHom).comp
    (Units.map
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal
        v.2).toMonoidHom)

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_SinglePlace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Ideles supported at one place

Local-to-global diagrams use the canonical embedding of a local multiplicative
group into the idele group. This file constructs
that embedding at finite places and the corresponding one-component
relative idele.
-/

open scoped NumberField Classical TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

/-- The dependent archimedean value which is `x` at `v` and `1`
elsewhere. -/
def infinitePlaceValue
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    (w : InfinitePlace K) → w.Completionˣ :=
  Pi.mulSingle
    (M := fun u : InfinitePlace K ↦ u.Completionˣ)
    v x

omit [NumberField K] in
@[simp]
theorem infinitePlaceValue_same
    (v : InfinitePlace K)
    (x : v.Completionˣ) :
    infinitePlaceValue v x v = x := by
  exact Pi.mulSingle_eq_same
    (M := fun u : InfinitePlace K ↦ u.Completionˣ) v x

omit [NumberField K] in
@[simp]
theorem infinitePlaceValue_of_ne
    (v w : InfinitePlace K)
    (x : v.Completionˣ)
    (h : w ≠ v) :
    infinitePlaceValue v x w = 1 := by
  exact Pi.mulSingle_eq_of_ne
    (M := fun u : InfinitePlace K ↦ u.Completionˣ) h x

/-- The dependent local value which is `x` at `v` and `1` elsewhere. -/
def finitePlaceValue
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (w : HeightOneSpectrum (𝓞 K)) :
    (w.adicCompletion K)ˣ :=
  if h : w = v then h.symm ▸ x else 1

end IdeleGroup

namespace RelativeIdeleGroup

section Relative

variable
    {K : Type*} [Field K] [NumberField K]
    {L : Type*} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The dependent archimedean tensor value which is `z` at `v` and
`1` elsewhere. -/
def relativeInfinitePlaceValue
    (v : InfinitePlace K)
    (z : (v.Completion ⊗[K] L)ˣ)
    (w : InfinitePlace K) :
    (w.Completion ⊗[K] L)ˣ :=
  if h : w = v then h.symm ▸ z else 1

end Relative

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_NormalClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# A finite normal closure of a number-field extension

This file places the normal-closure construction used throughout the
global theory below the adelic and splitting developments that consume
it.  The closure is formed inside mathlib's fixed algebraic closure, and
the original field is embedded by the canonical chosen lift.
-/

noncomputable section

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
/-- Normal closure is invariant under replacing its source by an
isomorphic field. -/
theorem normalClosure_eq_top_of_source_algEquiv
    {M E : Type*}
    [Field M] [Algebra K M]
    [Field E] [Algebra K E]
    (e : L ≃ₐ[K] E)
    (hclosure :
      IntermediateField.normalClosure K L M = ⊤) :
    IntermediateField.normalClosure K E M = ⊤ := by
  apply top_unique
  rw [← hclosure]
  apply
    (normalClosure_le_iff
      (K := L)).2
  intro f
  let g : E →ₐ[K] M :=
    f.comp e.symm.toAlgHom
  have hRange :
      f.fieldRange = g.fieldRange := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e y, by simp [g]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, by simp [g]⟩
  rw [hRange]
  exact g.fieldRange_le_normalClosure
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace LocalClassFieldTheory

/-!
# Finite local reciprocity: canonicity of local reciprocity

The construction of local reciprocity realizes a finite Galois extension in
a fixed separable closure.  This file proves that the transported reciprocity
isomorphism is independent of that realization.  Two embeddings are extended
to an automorphism of the separable closure, and
the abstract reciprocity naturality theorem supplies the required naturality.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Conjugating two realizations -/

/-! ## The two vertical maps of the abstract reciprocity naturality theorem -/

section EmbeddingConjugation

/-! ## Concrete comparison on representatives -/

/-! ## The two outer comparison squares -/

/-! ## The abstract reciprocity naturality theorem and embedding independence -/

/-- The final pointwise diagram chase: the source, middle, and target squares
determine the transported value without any further unfolding. -/
theorem reciprocityTransport_pointwise
    {A B C D E F : Type}
    (q : A → B) (b : C → D)
    (ri : A ≃ C) (rj : B ≃ D)
    (ni : C → E) (nj : D → E)
    (si : A ≃ F) (sj : B ≃ F)
    (hsource : ∀ z, sj (q z) = si z)
    (hnorm : ∀ a, nj (b a) = ni a)
    (hforward : ∀ z, b (ri z) = rj (q z))
    (x : F) :
    ni (ri (si.symm x)) = nj (rj (sj.symm x)) := by
  have hq : q (si.symm x) = sj.symm x := by
    apply sj.injective
    calc
      sj (q (si.symm x)) = si (si.symm x) := hsource (si.symm x)
      _ = x := si.apply_symm_apply x
      _ = sj (sj.symm x) := (sj.apply_symm_apply x).symm
  calc
    ni (ri (si.symm x)) = nj (b (ri (si.symm x))) :=
      (hnorm (ri (si.symm x))).symm
    _ = nj (rj (q (si.symm x))) := congrArg nj (hforward (si.symm x))
    _ = nj (rj (sj.symm x)) := congrArg (fun z ↦ nj (rj z)) hq

end EmbeddingConjugation

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_GaloisValuation_AbsoluteGalois_InfiniteGaloisCorrespondence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false
/-! Provides the public declarations in the `RamificationTheory.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence` Lean module. -/

namespace RamificationTheory

noncomputable section

universe u v w z

namespace Field
namespace absoluteGaloisGroup

open scoped Topology Pointwise
open CategoryTheory

theorem finiteDimensional_comap_algEquiv
    {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) (E : IntermediateField F B)
    [FiniteDimensional F E] :
    FiniteDimensional F (E.comap e.toAlgHom) := by
  let Ecomap : IntermediateField F A := E.comap e.toAlgHom
  let eLin : Ecomap ≃ₗ[F] E :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun x => ⟨e.symm x.1, by
        change e (e.symm x.1) ∈ E
        rw [e.apply_symm_apply]
        exact x.2⟩
      left_inv := by
        intro x
        ext
        exact e.symm_apply_apply x.1
      right_inv := by
        intro x
        ext
        exact e.apply_symm_apply x.1
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  exact Module.Finite.equiv eLin.symm

/-- Pull back an intermediate field along a ring equivalence which is
semilinear over a base-field equivalence.  This is the finite-level source
needed for Krull-continuity of conjugation by such a semilinear equivalence. -/
def semilinearRingEquivPreimageIntermediateField
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') : IntermediateField F Ω where
  carrier := {x : Ω | e x ∈ E}
  zero_mem' := by
    simp
  one_mem' := by
    simp
  add_mem' := by
    intro x y hx hy
    simpa using E.add_mem hx hy
  mul_mem' := by
    intro x y hx hy
    simpa using E.mul_mem hx hy
  inv_mem' := by
    intro x hx
    simpa using E.inv_mem hx
  algebraMap_mem' := by
    intro x
    change e (algebraMap F Ω x) ∈ E
    rw [he x]
    exact E.algebraMap_mem (τ x)

/-- States the theorem `mem_semilinearRingEquivPreimageIntermediateField_iff`. -/
@[simp]
theorem mem_semilinearRingEquivPreimageIntermediateField_iff
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') (x : Ω) :
    x ∈ semilinearRingEquivPreimageIntermediateField τ e he E ↔ e x ∈ E :=
  Iff.rfl

/-- States the theorem `semilinearRingEquivPreimageIntermediateField_symm_mem`. -/
theorem semilinearRingEquivPreimageIntermediateField_symm_mem
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') {x : Ω'} (hx : x ∈ E) :
    e.symm x ∈ semilinearRingEquivPreimageIntermediateField τ e he E := by
  change e (e.symm x) ∈ E
  simpa using hx

/-- The semilinear pullback of a finite intermediate field is finite. -/
theorem finiteDimensional_semilinearRingEquivPreimageIntermediateField
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (E : IntermediateField F' Ω') [FiniteDimensional F' E] :
    FiniteDimensional F
      (semilinearRingEquivPreimageIntermediateField τ e he E) := by
  let T := semilinearRingEquivPreimageIntermediateField τ e he E
  let f : E →ₛₗ[(τ.symm : F' →+* F)] T :=
    { toFun := fun x =>
        ⟨e.symm x.1,
          semilinearRingEquivPreimageIntermediateField_symm_mem
            τ e he E x.2⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp only [Algebra.smul_def]
        change e.symm (algebraMap F' Ω' a * x.1) =
          algebraMap F Ω (τ.symm a) * e.symm x.1
        have hbase :
            e (algebraMap F Ω (τ.symm a)) =
              algebraMap F' Ω' a := by
          simpa using he (τ.symm a)
        apply e.injective
        calc
          e (e.symm (algebraMap F' Ω' a * x.1)) =
              algebraMap F' Ω' a * x.1 := by
                rw [e.apply_symm_apply]
          _ = e (algebraMap F Ω (τ.symm a)) * x.1 := by
                rw [hbase]
          _ = e (algebraMap F Ω (τ.symm a)) * e (e.symm x.1) := by
                rw [e.apply_symm_apply]
          _ = e (algebraMap F Ω (τ.symm a) * e.symm x.1) := by
                rw [map_mul] }
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨⟨e y.1, y.2⟩, ?_⟩
    ext
    exact e.symm_apply_apply y.1
  have hfgImage : Submodule.FG ((⊤ : Submodule F' E).map f) :=
    (Module.Finite.fg_top (R := F') (M := E)).map f
  have hmaptop : (⊤ : Submodule F' E).map f =
      (⊤ : Submodule F T) := by
    rw [Submodule.map_top, LinearMap.range_eq_top_of_surjective f hsurj]
  change Module.Finite F T
  exact Module.Finite.of_fg_top (by simpa [hmaptop] using hfgImage)

/-- Conjugation by a semilinear equivalence of an algebraic closure is
continuous for the Krull topology.  The semilinear base action is recorded
explicitly by `he`, and the group homomorphism is required only to have the
corresponding conjugation formula on underlying ring equivalences. -/
theorem semilinear_conjugation_continuous
    {F : Type u} {F' : Type w} {Ω : Type v} {Ω' : Type z}
    [Field F] [Field F'] [Field Ω] [Field Ω']
    [Algebra F Ω] [Algebra F' Ω']
    (τ : F ≃+* F') (e : Ω ≃+* Ω')
    (he : ∀ x : F,
      e (algebraMap F Ω x) = algebraMap F' Ω' (τ x))
    (φ : Gal(Ω / F) →* Gal(Ω' / F'))
    (hφ : ∀ g : Gal(Ω / F),
      (φ g).toRingEquiv =
        e.symm.trans (g.toRingEquiv.trans e)) :
    Continuous φ := by
  refine continuous_of_continuousAt_one φ ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff F' Ω' s).1 hs with
    ⟨E, hE, hEs⟩
  let Epre : IntermediateField F Ω :=
    semilinearRingEquivPreimageIntermediateField τ e he E
  have : FiniteDimensional F' E := hE
  have : FiniteDimensional F Epre :=
    finiteDimensional_semilinearRingEquivPreimageIntermediateField
      τ e he E
  refine (krullTopology_mem_nhds_one_iff F Ω (φ ⁻¹' s)).2 ?_
  refine ⟨Epre, inferInstance, ?_⟩
  intro σ hσ
  apply hEs
  change φ σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hxpre : e.symm x ∈ Epre :=
    semilinearRingEquivPreimageIntermediateField_symm_mem
      τ e he E hx
  have hfix :=
    (IntermediateField.mem_fixingSubgroup_iff Epre σ).1 hσ
      (e.symm x) hxpre
  change (φ σ).toRingEquiv x = x
  rw [hφ σ]
  change e (σ (e.symm x)) = x
  rw [hfix, e.apply_symm_apply]

/-- Algebra-equivalence conjugation is continuous for Krull topologies. -/
theorem algEquiv_autCongr_continuous
    {F : Type u} {A : Type v} {B : Type w} [Field F] [Field A] [Field B]
    [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) :
    Continuous (AlgEquiv.autCongr e : Gal(A / F) → Gal(B / F)) := by
  refine continuous_of_continuousAt_one (AlgEquiv.autCongr e).toMonoidHom ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  rcases (krullTopology_mem_nhds_one_iff F B s).1 hs with
    ⟨E, hE, hEs⟩
  let Ecomap : IntermediateField F A := E.comap e.toAlgHom
  have : FiniteDimensional F E := hE
  have : FiniteDimensional F Ecomap :=
    finiteDimensional_comap_algEquiv e E
  refine (krullTopology_mem_nhds_one_iff F A
    ((AlgEquiv.autCongr e) ⁻¹' s)).2 ?_
  refine ⟨Ecomap, inferInstance, ?_⟩
  intro σ hσ
  apply hEs
  change AlgEquiv.autCongr e σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change e (σ (e.symm x)) = x
  have hxEcomap : e.symm x ∈ Ecomap := by
    change e (e.symm x) ∈ E
    rw [e.apply_symm_apply]
    exact hx
  have hfix := (IntermediateField.mem_fixingSubgroup_iff Ecomap σ).1 hσ
    (e.symm x) hxEcomap
  rw [hfix]
  exact e.apply_symm_apply x

/-- The natural inclusion `Gal(M/E) -> Gal(M/K)` for an intermediate field
`E` of a field extension `M/K`. -/
def ofIntermediateFieldInExtension
    {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M]
    (E : IntermediateField K M) :
    Gal(M / E) →* Gal(M / K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

/-- States the theorem `ofIntermediateFieldInExtension_apply`. -/
@[simp]
theorem ofIntermediateFieldInExtension_apply
    {K : Type u} {M : Type v} [Field K] [Field M] [Algebra K M]
    (E : IntermediateField K M) (σ : Gal(M / E)) :
    ofIntermediateFieldInExtension E σ = σ.restrictScalars K :=
  rfl

variable (K : Type u) [Field K]

theorem finiteDimensional_extendScalars_sup
    (k : Type u) (M : Type v) [Field k] [Field M] [Algebra k M]
    (E F : IntermediateField k M)
    [FiniteDimensional k E] [FiniteDimensional k F] :
    FiniteDimensional E
      (IntermediateField.extendScalars (F := E) (E := E ⊔ F) le_sup_left) := by
  let EF : IntermediateField k M := E ⊔ F
  let EEF : IntermediateField E M :=
    IntermediateField.extendScalars (F := E) (E := EF) le_sup_left
  have : FiniteDimensional k EF := E.finiteDimensional_sup F
  let : Algebra E EF := (IntermediateField.inclusion le_sup_left).toAlgebra
  have : IsScalarTower k E EF := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    change (algebraMap k M) x =
      ((IntermediateField.inclusion le_sup_left) ((algebraMap k E) x) :
        M)
    rfl
  have : Module.Finite E EF := FiniteDimensional.right k E EF
  let eLin : EEF ≃ₗ[E] EF :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl
      map_add' := by
        intro x y
        ext
        rfl
      map_smul' := by
        intro a x
        ext
        rfl }
  exact Module.Finite.equiv eLin.symm

/-- For a finite intermediate extension `E/K`, the natural inclusion
`Gal(M/E) → Gal(M/K)` is continuous for the two Krull topologies. -/
theorem ofIntermediateFieldInExtension_continuous
    {k : Type u} {M : Type v} [Field k] [Field M] [Algebra k M]
    [IsGalois k M]
    (E : IntermediateField k M) [FiniteDimensional k E] :
    Continuous (ofIntermediateFieldInExtension E) := by
  refine continuous_of_continuousAt_one
    (ofIntermediateFieldInExtension E) ?_
  rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
  intro s hs
  rcases (krullTopology_mem_nhds_one_iff k M s).1 hs with
    ⟨F, hF, hFs⟩
  let EF : IntermediateField k M := E ⊔ F
  let EEF : IntermediateField E M :=
    IntermediateField.extendScalars (F := E) (E := EF) le_sup_left
  have : FiniteDimensional k F := hF
  have : FiniteDimensional E EEF :=
    finiteDimensional_extendScalars_sup k M E F
  refine (krullTopology_mem_nhds_one_iff E M
    ((ofIntermediateFieldInExtension E) ⁻¹' s)).2 ?_
  refine ⟨EEF, inferInstance, ?_⟩
  intro σ hσ
  apply hFs
  change ofIntermediateFieldInExtension E σ ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  change σ x = x
  have hxEF : x ∈ EF := (show F ≤ EF from le_sup_right) hx
  have hxEEF : x ∈ EEF := by
    change x ∈ EF
    exact hxEF
  exact (IntermediateField.mem_fixingSubgroup_iff EEF σ).1 hσ x hxEEF

end absoluteGaloisGroup
end Field

end

end RamificationTheory
end

section
-- module Solutions.OAIQ244_DUKE.GroupTheory_Finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Finite group theory for the splitting corollaries

This file isolates the finite-group inputs for prime-power and normal-closure
splitting arguments.

For the prime-power subgroup reduction, a proper subgroup of a finite group of order `p ^ v` is
contained in a subgroup of index `p`.  The proof below gives the
slightly stronger statement for arbitrary finite `p`-groups.  In the
cyclic case the resulting subgroup is normal, hence produces the
degree-`p` quotient used to choose the intermediate field.

For the normal-closure splitting argument, the normal closure is encoded by a core-free subgroup
`H`.  The canonical map from left cosets to double cosets is
surjective.  If it does not decrease cardinality, its right subgroup
is contained in the normal core of `H`; therefore it is trivial when
`H` is core-free.
-/

noncomputable section

universe uG

section PrimeOrder

variable (G : Type uG) [Group G] [Finite G] [Nontrivial G]

/-- Every nontrivial finite group contains an element of prime order.
This supplies the cyclic prime-degree subgroup used after passing to a
normal closure. -/
theorem exists_element_of_prime_order :
    ∃ (p : ℕ) (g : G),
      p.Prime ∧ orderOf g = p := by
  obtain ⟨p, hp, hpDvd⟩ :=
    Nat.exists_prime_and_dvd
      (ne_of_gt (Finite.one_lt_card :
        1 < Nat.card G))
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := G) p hpDvd
  exact ⟨p, g, hp, hg⟩

end PrimeOrder

section DoubleCosets

variable {G : Type uG} [Group G]

/-- The canonical projection
`H \ G = H \ G / 1 → H \ G / D`. -/
def doubleCosetRightProjection
    (H D : Subgroup G) :
    DoubleCoset.Quotient
        (H : Set G) (⊥ : Subgroup G) →
      DoubleCoset.Quotient (H : Set G) D :=
  Quotient.map' id fun a b hab ↦ by
    rw [DoubleCoset.rel_iff] at hab ⊢
    obtain ⟨h, hh, k, hk, hab⟩ := hab
    have hkOne : k = 1 :=
      Subgroup.mem_bot.mp hk
    subst k
    exact
      ⟨h, hh, 1, D.one_mem, by simpa using hab⟩

@[simp]
theorem doubleCosetRightProjection_mk
    (H D : Subgroup G)
    (g : G) :
    doubleCosetRightProjection H D
        (DoubleCoset.mk H (⊥ : Subgroup G) g) =
      DoubleCoset.mk H D g :=
  Quotient.map'_mk'' _ _ _

/-- The projection from left cosets to double cosets is onto. -/
theorem doubleCosetRightProjection_surjective
    (H D : Subgroup G) :
    Function.Surjective
      (doubleCosetRightProjection H D) := by
  intro q
  refine
    ⟨DoubleCoset.mk H (⊥ : Subgroup G) q.out, ?_⟩
  rw [doubleCosetRightProjection_mk]
  exact DoubleCoset.out_eq' _ _ q

/-- If the left-coset to double-coset projection is injective, then
the right subgroup lies in the normal core of the left subgroup. -/
theorem rightSubgroup_le_normalCore_of_doubleCoset_projection_injective
    (H D : Subgroup G)
    (hinj : Function.Injective
      (doubleCosetRightProjection H D)) :
    D ≤ H.normalCore := by
  intro d hd g
  have hdouble :
      DoubleCoset.mk H D g =
        DoubleCoset.mk H D (g * d) := by
    rw [DoubleCoset.eq]
    exact
      ⟨1, H.one_mem, d, hd, by simp⟩
  have hleft :
      DoubleCoset.mk H (⊥ : Subgroup G) g =
        DoubleCoset.mk H (⊥ : Subgroup G)
          (g * d) := by
    apply hinj
    simpa only
      [doubleCosetRightProjection_mk]
      using hdouble
  rw [DoubleCoset.eq] at hleft
  obtain ⟨h, hh, k, hk, heq⟩ := hleft
  have hkOne : k = 1 :=
    Subgroup.mem_bot.mp hk
  subst k
  simp only [mul_one] at heq
  have hconj : g * d * g⁻¹ = h := by
    calc
      g * d * g⁻¹ =
          (g * d) * g⁻¹ := rfl
      _ = (h * g) * g⁻¹ := by
        rw [heq]
      _ = h := by simp
  rw [hconj]
  exact hh

/-- Equality between the number of left cosets and the number of
double cosets forces the right subgroup into the normal core. -/
theorem rightSubgroup_le_normalCore_of_doubleCoset_card_eq
    [Finite G]
    (H D : Subgroup G)
    (hcard :
      Nat.card
          (DoubleCoset.Quotient (H : Set G) D) =
        Nat.card
          (DoubleCoset.Quotient (H : Set G)
            (⊥ : Subgroup G))) :
    D ≤ H.normalCore := by
  let :
      Finite
        (DoubleCoset.Quotient (H : Set G)
          (⊥ : Subgroup G)) :=
    Finite.of_surjective
      (DoubleCoset.mk H (⊥ : Subgroup G))
      (by
        intro q
        exact
          ⟨q.out,
            DoubleCoset.out_eq' _ _ q⟩)
  have hbij :
      Function.Bijective
        (doubleCosetRightProjection H D) :=
    Function.Surjective.bijective_of_nat_card_le
      (doubleCosetRightProjection_surjective H D)
      hcard.symm.le
  exact
    rightSubgroup_le_normalCore_of_doubleCoset_projection_injective
      H D hbij.injective

/-- For a core-free subgroup `H`, the double-coset count equals the
left-coset count exactly when the right subgroup is trivial.

This is the finite-group content of the normal-closure reduction. -/
theorem doubleCoset_card_eq_leftCoset_iff_of_normalCore_eq_bot
    [Finite G]
    (H D : Subgroup G)
    (hcore : H.normalCore = ⊥) :
    Nat.card
          (DoubleCoset.Quotient (H : Set G) D) =
        Nat.card
          (DoubleCoset.Quotient (H : Set G)
            (⊥ : Subgroup G)) ↔
      D = ⊥ := by
  constructor
  · intro hcard
    apply le_bot_iff.mp
    rw [← hcore]
    exact
      rightSubgroup_le_normalCore_of_doubleCoset_card_eq
        H D hcard
  · rintro rfl
    rfl

end DoubleCosets
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_NormalClosure
attribute [-instance] _root_.cyclicPrimeDegreeIntermediate_isGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Complete splitting and normal closures

This file formalizes the normal-closure reduction for complete splitting.
For a finite Galois extension `M / K`, an intermediate field `L`, a
nontrivial absolute value `v` of `K`, and an extension `w` to `M`, put

* `G = Gal(M / K)`,
* `H = Gal(M / L)`, and
* `D = D(w / v)`.

Restriction of the conjugates of `w` gives an equivalence

`H \ G / D ≃ { extensions of v to L }`.

Thus the intrinsic complete-splitting condition for the possibly
non-Galois extension `L / K` is exactly the equality between the number
of double cosets and the number of left cosets.  If `M` is generated by
the `K`-conjugates of `L`, then `H` has trivial normal core.
`SplittingGroupTheory` consequently forces `D = 1`, so the place splits
completely already in `M`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

section DoubleCosetCount

variable {K M : Type}
    [Field K] [Field M] [Algebra K M]
    [IsGalois K M]

local notation "G" => M ≃ₐ[K] M

/-- The left-coset space `H \ G = H \ G / 1` has cardinality
`[L : K]` for `H = Gal(M / L)`. -/
theorem leftCosetDoubleCoset_card_eq_finrank
    (L : IntermediateField K M) :
    Nat.card
        (DoubleCoset.Quotient
          (L.fixingSubgroup : Set G)
          (⊥ : Subgroup G)) =
      Module.finrank K L := by
  calc
    Nat.card
        (DoubleCoset.Quotient
          (L.fixingSubgroup : Set G)
          (⊥ : Subgroup G)) =
        Nat.card
          (Quotient
            (QuotientGroup.rightRel
              L.fixingSubgroup)) := by
      rw [DoubleCoset.right_bot_eq_right_quot]
    _ = Nat.card (G ⧸ L.fixingSubgroup) :=
      Nat.card_congr
        (QuotientGroup.quotientRightRelEquivQuotientLeftRel
          L.fixingSubgroup)
    _ = L.fixingSubgroup.index :=
      L.fixingSubgroup.index_eq_card.symm
    _ = Module.finrank K L :=
      (IntermediateField.finrank_eq_fixingSubgroup_index
        (F := K) (E' := M) L).symm

end DoubleCosetCount

section NormalClosure

variable {K M : Type}
    [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]

/-- If the conjugates of `L` generate the ambient Galois extension,
then `Gal(M / L)` is core-free.  This derives the group-theoretic
normal-closure condition from the actual field-theoretic normal
closure, rather than taking it as an additional hypothesis. -/
theorem fixingSubgroup_normalCore_eq_bot_of_normalClosure_eq_top
    (L : IntermediateField K M)
    (hclosure :
      IntermediateField.normalClosure K L M = ⊤) :
    L.fixingSubgroup.normalCore = ⊥ := by
  let N : Subgroup (M ≃ₐ[K] M) :=
    L.fixingSubgroup.normalCore
  let : N.Normal :=
    L.fixingSubgroup.normalCore_normal
  have hLle :
      L ≤ IntermediateField.fixedField N := by
    rw [← IsGalois.fixedField_fixingSubgroup L]
    exact
      IntermediateField.fixedField_le
        L.fixingSubgroup.normalCore_le
  let :
      IsGalois K (IntermediateField.fixedField N) :=
    IsGalois.of_fixedField_normal_subgroup N
  have hclosureLe :
      IntermediateField.normalClosure K L M ≤
        IntermediateField.fixedField N :=
    (IntermediateField.normalClosure_le_iff_of_normal).2
      hLle
  have htop :
      IntermediateField.fixedField N = ⊤ :=
    top_unique (hclosure ▸ hclosureLe)
  change N = ⊥
  rw [← IntermediateField.fixingSubgroup_fixedField N,
    htop, IntermediateField.fixingSubgroup_top]

end NormalClosure
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_PrimeOrderFixedField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Prime-order fixed fields and complete splitting

This file formalizes a prime-order fixed-field reduction.
From a nontrivial finite Galois extension `L / K` we choose an
automorphism `σ` of prime order `p` and form

`K' = L ^ ⟨σ⟩`.

The extension `L / K'` is an actual cyclic Galois extension of prime
degree.  We also prove the finite-place bridge used immediately before
applying the cyclic prime-power splitting criterion: if a finite place of `K` splits completely in `L`
and a finite place of `K'` lies above it, then the latter splits
completely in `L / K'`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

section PrimeOrderConstruction

variable {K L : Type}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

local notation "G" => L ≃ₐ[K] L

/-- A nontrivial finite Galois extension has an automorphism of prime
order.  Nontriviality is supplied by the actual degree inequality. -/
theorem exists_prime_order_automorphism_of_one_lt_finrank
    (hdegree : 1 < Module.finrank K L) :
    ∃ (p : ℕ) (σ : G),
      p.Prime ∧ orderOf σ = p := by
  have hcard : 1 < Nat.card G := by
    rw [IsGalois.card_aut_eq_finrank K L]
    exact hdegree
  let : Nontrivial G :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  exact exists_element_of_prime_order G

/-- The chosen prime order in the nontrivial Galois group. -/
noncomputable def fixedFieldPrime
    (hdegree : 1 < Module.finrank K L) : ℕ :=
  (exists_prime_order_automorphism_of_one_lt_finrank
    (K := K) (L := L) hdegree).choose

/-- The chosen automorphism of prime order. -/
noncomputable def primeOrderAutomorphism
    (hdegree : 1 < Module.finrank K L) : G :=
  (exists_prime_order_automorphism_of_one_lt_finrank
    (K := K) (L := L) hdegree).choose_spec.choose

theorem fixedFieldPrime_prime
    (hdegree : 1 < Module.finrank K L) :
    (fixedFieldPrime
      (K := K) (L := L) hdegree).Prime :=
  (exists_prime_order_automorphism_of_one_lt_finrank
    (K := K) (L := L) hdegree).choose_spec.choose_spec.1

theorem primeOrderAutomorphism_orderOf
    (hdegree : 1 < Module.finrank K L) :
    orderOf
        (primeOrderAutomorphism
          (K := K) (L := L) hdegree) =
      fixedFieldPrime
        (K := K) (L := L) hdegree :=
  (exists_prime_order_automorphism_of_one_lt_finrank
    (K := K) (L := L) hdegree).choose_spec.choose_spec.2

/-- The cyclic subgroup generated by the chosen prime-order
automorphism. -/
noncomputable def primeOrderSubgroup
    (hdegree : 1 < Module.finrank K L) :
    Subgroup G :=
  Subgroup.zpowers
    (primeOrderAutomorphism
      (K := K) (L := L) hdegree)

theorem primeOrderSubgroup_card
    (hdegree : 1 < Module.finrank K L) :
    Nat.card
        (primeOrderSubgroup
          (K := K) (L := L) hdegree) =
      fixedFieldPrime
        (K := K) (L := L) hdegree := by
  rw [primeOrderSubgroup, Nat.card_zpowers,
    primeOrderAutomorphism_orderOf]

/-- The actual intermediate field `K' = L ^ ⟨σ⟩`. -/
noncomputable def primeOrderFixedField
    (hdegree : 1 < Module.finrank K L) :
    IntermediateField K L :=
  IntermediateField.fixedField
    (primeOrderSubgroup
      (K := K) (L := L) hdegree)

/-- The ambient field is Galois over the fixed field of the chosen
finite subgroup. -/
noncomputable instance primeOrderFixedField_isGalois
    (hdegree : 1 < Module.finrank K L) :
    IsGalois
      (primeOrderFixedField
        (K := K) (L := L) hdegree)
      L := by
  unfold primeOrderFixedField
  exact
    IsGalois.of_fixed_field L
      (primeOrderSubgroup
        (K := K) (L := L) hdegree)

/-- The constructed relative extension has prime degree `p`. -/
theorem primeOrderFixedField_finrank
    (hdegree : 1 < Module.finrank K L) :
    Module.finrank
        (primeOrderFixedField
          (K := K) (L := L) hdegree)
        L =
      fixedFieldPrime
        (K := K) (L := L) hdegree := by
  unfold primeOrderFixedField
  rw [IntermediateField.finrank_fixedField_eq_card,
    primeOrderSubgroup_card]

/-- The relative Galois group is cyclic, transported from the
generating subgroup through the finite Galois correspondence. -/
noncomputable instance primeOrderFixedField_isCyclic
    (hdegree : 1 < Module.finrank K L) :
    IsCyclic
      (L ≃ₐ[
        primeOrderFixedField
          (K := K) (L := L) hdegree] L) := by
  let P :=
    primeOrderSubgroup
      (K := K) (L := L) hdegree
  have hP : IsCyclic P := by
    dsimp [P, primeOrderSubgroup]
    exact
      Subgroup.isCyclic_zpowers
        (primeOrderAutomorphism
          (K := K) (L := L) hdegree)
  exact
    (IntermediateField.subgroupEquivAlgEquiv P).isCyclic.mp
      hP

/-- The order of the relative Galois group is the chosen prime.  In
particular it is a prime-power order with exponent one, exactly the
input expected by the cyclic prime-power splitting criterion. -/
theorem primeOrderFixedField_card_aut
    (hdegree : 1 < Module.finrank K L) :
    Nat.card
        (L ≃ₐ[
          primeOrderFixedField
            (K := K) (L := L) hdegree] L) =
      fixedFieldPrime
        (K := K) (L := L) hdegree := by
  rw [IsGalois.card_aut_eq_finrank,
    primeOrderFixedField_finrank]

end PrimeOrderConstruction
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Rational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Ray class groups of the rational numbers

This file computes ray class groups of the rational numbers. A positive integer
`m` determines a full narrow ray modulus: its finite part has exponent
`m.factorization p` at `p`, and its real place imposes positivity. The
positive generator of an ideal prime to this modulus gives the explicit
isomorphism with `(ZMod m)ˣ`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section


namespace RayClass

local instance rationalRingOfIntegersIsPrincipalIdealRing_rda254e_1 :
    IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm
    Rat.ringOfIntegersEquiv.symm.surjective
local instance rationalNatGeneratorPrimeFact_rda254e_1
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.natGenerator v)) :=
  ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
local instance rationalPrimesEquivPrimeFact_rda254e_1
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact
      (Nat.Prime
        ((Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ) v : Nat.Primes) : ℕ)) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv
    (R := 𝓞 ℚ) v).property⟩
/-- The height-one prime of `𝓞 ℚ` associated with a natural prime. -/
noncomputable abbrev rationalPrime (p : Nat.Primes) :
    HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p

@[simp]
theorem natGenerator_rationalPrime (p : Nat.Primes) :
    Rat.HeightOneSpectrum.natGenerator (rationalPrime p) = p := by
  exact congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)

/-! ### The local congruence condition over `ℚ` -/

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_TensorProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Coprime tensor-product base change of a Galois extension

The roots-of-unity descent uses the following concrete fact. If finite field
extensions `M / K` and `L / K` have
coprime degrees, then `M ⊗[K] L` is a field.  If `L / K` is Galois,
the resulting extension over `M` is Galois of the same degree.

The proof constructs the field structure from linear disjointness.
For Galoisness, every automorphism of `L / K` is extended by
`id_M ⊗ σ`; these distinct automorphisms already account for the full
dimension of the tensor product.
-/

open scoped TensorProduct

noncomputable section

universe u

variable
    (K M L : Type u)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L]
    [hKM : FiniteDimensional K M]
    [hKL : FiniteDimensional K L]

/-- Coprime finite field extensions are linearly disjoint, hence their
tensor product is a field. -/
theorem tensorProduct_isField_of_finrank_coprime
    (hcoprime :
      (Module.finrank K M).Coprime
        (Module.finrank K L)) :
    IsField (M ⊗[K] L) := by
  let Ω := AlgebraicClosure K
  let iM : M →ₐ[K] Ω := IsAlgClosed.lift
  let iL : L →ₐ[K] Ω := IsAlgClosed.lift
  let eM : M ≃ₐ[K] iM.fieldRange :=
    AlgEquiv.ofInjectiveField iM
  let eL : L ≃ₐ[K] iL.fieldRange :=
    AlgEquiv.ofInjectiveField iL
  have hdegrees :
      (Module.finrank K iM.fieldRange).Coprime
        (Module.finrank K iL.fieldRange) := by
    rw [← eM.toLinearEquiv.finrank_eq,
      ← eL.toLinearEquiv.finrank_eq]
    exact hcoprime
  have hdisjoint :
      iM.fieldRange.LinearDisjoint iL.fieldRange :=
    IntermediateField.LinearDisjoint.of_finrank_coprime
      hdegrees
  exact
    IntermediateField.LinearDisjoint.isField_of_isAlgebraic'
      hdisjoint
      (Or.inl (Algebra.IsAlgebraic.of_finite K M))

section TensorAutomorphisms

variable [hGalois : IsGalois K L]

/-- Extend a `K`-automorphism of `L` to the coprime tensor base
change, fixing the left factor `M`. -/
def tensorBaseChangeAut
    (σ : L ≃ₐ[K] L) :
    (M ⊗[K] L) ≃ₐ[M] (M ⊗[K] L) :=
  { (Algebra.TensorProduct.congr
      (AlgEquiv.refl : M ≃ₐ[K] M) σ).toRingEquiv with
    commutes' := by
      intro m
      simp [Algebra.TensorProduct.algebraMap_apply] }

omit hKM hKL hGalois in
@[simp]
theorem tensorBaseChangeAut_tmul
    (σ : L ≃ₐ[K] L)
    (m : M) (x : L) :
    tensorBaseChangeAut K M L σ (m ⊗ₜ[K] x) =
      m ⊗ₜ[K] σ x := by
  simp [tensorBaseChangeAut]

omit hKM hKL hGalois in
/-- Distinct automorphisms remain distinct after tensor base change. -/
theorem tensorBaseChangeAut_injective :
    Function.Injective (tensorBaseChangeAut K M L) := by
  intro σ τ hστ
  apply AlgEquiv.ext
  intro x
  have hx :=
    DFunLike.congr_fun hστ
      ((1 : M) ⊗ₜ[K] x)
  have htensor :
      (1 : M) ⊗ₜ[K] σ x =
        (1 : M) ⊗ₜ[K] τ x := by
    simpa using hx
  exact
    (Algebra.TensorProduct.includeRight
      (R := K) (A := M) (B := L)).injective
      htensor

/-- Galoisness survives the coprime tensor-product base change. -/
theorem tensorProduct_isGalois_of_finrank_coprime
    (hcoprime :
      (Module.finrank K M).Coprime
        (Module.finrank K L)) :
    letI : Field (M ⊗[K] L) :=
      (tensorProduct_isField_of_finrank_coprime
        K M L hcoprime).toField
    IsGalois M (M ⊗[K] L) := by
  let N := M ⊗[K] L
  let : Field N :=
    (tensorProduct_isField_of_finrank_coprime
      K M L hcoprime).toField
  have hfinite : FiniteDimensional M N := by
    exact Module.Finite.of_restrictScalars_finite K M N
  let : FiniteDimensional M N := hfinite
  have hlow :
      Nat.card (L ≃ₐ[K] L) ≤
        Nat.card (N ≃ₐ[M] N) :=
    Nat.card_le_card_of_injective
      (tensorBaseChangeAut K M L)
      (tensorBaseChangeAut_injective K M L)
  have hdim :
      Module.finrank M N = Module.finrank K L := by
    exact Module.finrank_baseChange
  have hlow' :
      Module.finrank M N ≤
        Nat.card (N ≃ₐ[M] N) := by
    rw [hdim, ← IsGalois.card_aut_eq_finrank K L]
    exact hlow
  have hupp :
      Nat.card (N ≃ₐ[M] N) ≤
        Module.finrank M N := by
    rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  exact
    IsGalois.of_card_aut_eq_finrank M N
      (Nat.le_antisymm hupp hlow')

end TensorAutomorphisms
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_FieldUnitFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- A continuous algebraic equivalence from a compact group to a Hausdorff
group is automatically a topological group equivalence. -/
noncomputable def continuousMulEquivOfCompactToT2
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [Mul A] [Mul B] [CompactSpace A] [T2Space B]
    (e : A ≃* B) (he : Continuous e) : A ≃ₜ* B :=
  ContinuousMulEquiv.mk'
    (he.homeoOfEquivCompactToT2 (f := e.toEquiv)) e.map_mul

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_KummerLocalNormContainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Local norm containment for Kummer extensions

This module proves that local powers, and then the concrete simple-Kummer
power subgroup, lie in the norm subgroup at a chosen finite place.
-/

open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- Coordinates in `(Z/nZ)^r` show that every Galois automorphism has
exponent dividing `n`. -/
theorem galois_pow_eq_one_of_field_equiv_pi_zmod
    {L : Type*} [Field L] [Algebra K L]
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ)))) :
    ∀ sigma : L ≃ₐ[K] L, sigma ^ (n : ℕ) = 1 := by
  intro sigma
  apply eG.injective
  rw [map_pow, map_one]
  ext i
  apply Multiplicative.toAdd.injective
  change (n : ℕ) • Multiplicative.toAdd (eG sigma i) = 0
  simp


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_CyclotomicPrimeBaseChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Prime cyclotomic base change

This file constructs the roots-of-unity base change for a prime-degree
extension.  If `L / K` has prime degree `p`, the
cyclotomic extension `K(μ_p) / K` has degree strictly smaller than `p`.
The two degrees are therefore coprime, and

`K(μ_p) ⊗[K] L`

is an actual field, Galois of degree `p` over `K(μ_p)`.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace KummerTheory

universe u

variable
    (K L : Type u)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]

/-- Over a characteristic-zero field, the concrete cyclotomic field
of order `m` has degree at most `φ(m)`. -/
theorem cyclotomicField_finrank_le_totient
    (F : Type*) [Field F] [CharZero F]
    (m : ℕ) (hm : 0 < m) :
    Module.finrank F (CyclotomicField m F) ≤
      Nat.totient m := by
  let : NeZero m := ⟨hm.ne'⟩
  let C := CyclotomicField m F
  let : IsCyclotomicExtension {m} F C :=
    CyclotomicField.isCyclotomicExtension m F
  let : FiniteDimensional F C :=
    IsCyclotomicExtension.finiteDimensional {m} F C
  obtain ⟨ζ, hζ⟩ :=
    (CyclotomicField.isCyclotomicExtension m F).exists_isPrimitiveRoot
      (Set.mem_singleton m) hm.ne'
  have hgen : Algebra.adjoin F ({ζ} : Set C) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have htop :
      IntermediateField.adjoin F ({ζ} : Set C) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra
      F ({ζ} : Set C) hgen
  have hroot :
      Polynomial.aeval ζ
          (Polynomial.cyclotomic m F) = 0 := by
    rw [Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic,
      ← Polynomial.IsRoot.def]
    exact hζ.isRoot_cyclotomic hm
  have hdegree :
      (minpoly F ζ).natDegree ≤
        (Polynomial.cyclotomic m F).natDegree :=
    Polynomial.natDegree_le_natDegree
      (minpoly.min F ζ
        (Polynomial.cyclotomic.monic m F) hroot)
  calc
    Module.finrank F (CyclotomicField m F) =
        Module.finrank F C := rfl
    _ = Module.finrank F
          (IntermediateField.adjoin F ({ζ} : Set C)) := by
      rw [htop]
      simp
    _ = (minpoly F ζ).natDegree :=
      IntermediateField.adjoin.finrank
        (IsIntegral.of_finite F ζ)
    _ ≤ (Polynomial.cyclotomic m F).natDegree :=
      hdegree
    _ = Nat.totient m :=
      Polynomial.natDegree_cyclotomic m F

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_HasseNormPrinciple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The Hasse norm principle: the concrete local-global map

This file proves the Hasse norm principle on the actual idele and field norm
maps.  The local condition is expressed canonically:
at a place `v` it is the image of the determinant norm on
`K_v ⊗[K] L`.  At finite places this is the chosen completion norm
subgroup by
`_root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup`.

The resulting homomorphism

`Kˣ / N(Lˣ) ⟶ I_K / I_K,loc-norm`

is the concrete diagonal local-norm map.  Its injectivity is exactly the
Hasse norm principle.  The global-to-local inclusion and this equivalence
are independent of the global class-field axiom; the reverse inclusion
follows from degree-minus-one Tate-cohomology vanishing.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

open CategoryTheory

/-- The actual global field-norm subgroup `N_{L/K}(Lˣ)` of `Kˣ`. -/
def globalFieldNormSubgroup
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    Subgroup Kˣ :=
  (Units.map
    (Algebra.norm K : L →* K)).range

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Padic_UnitDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- After identifying the residue characteristic with `p` and the relative
degree with one, the free additive factor is canonically `ℤ_[p]`. -/
noncomputable def padicFreeContinuousAddEquivOfEq
    (p q d : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hq : q = p) (hd : d = 1) :
    (Fin d → ℤ_[q]) ≃ₜ+ ℤ_[p] := by
  subst q
  subst d
  exact
    { AddEquiv.funUnique (Fin 1) ℤ_[p] with
      continuous_toFun := continuous_apply 0
      continuous_invFun := continuous_pi fun _ => continuous_id }

/-- Multiplicative tagging turns a continuous additive equivalence into a
continuous multiplicative equivalence. -/
noncomputable def continuousMultiplicativeEquivOfAddEquiv
    {A B : Type*} [AddZeroClass A] [AddZeroClass B]
    [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ+ B) :
    Multiplicative A ≃ₜ* Multiplicative B :=
  { e.toAddEquiv.toMultiplicative with
    continuous_toFun := e.continuous_toFun
    continuous_invFun := e.continuous_invFun }

/-- Multiplicative tagging commutes continuously with binary products. -/
noncomputable def prodMultiplicativeContinuousMulEquiv
    (A B : Type*) [AddZeroClass A] [AddZeroClass B]
    [TopologicalSpace A] [TopologicalSpace B] :
    Multiplicative (A × B) ≃ₜ*
      Multiplicative A × Multiplicative B :=
  { MulEquiv.prodMultiplicative A B with
    continuous_toFun := continuous_fst.prodMk continuous_snd
    continuous_invFun := continuous_fst.prodMk continuous_snd }

/-- The product of two continuous multiplicative equivalences. -/
noncomputable def continuousMulEquivProdCongr
    {A B C D : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D]
    [MulOneClass A] [MulOneClass B] [MulOneClass C] [MulOneClass D]
    (e : A ≃ₜ* B) (f : C ≃ₜ* D) :
    A × C ≃ₜ* B × D :=
  { MulEquiv.prodCongr e.toMulEquiv f.toMulEquiv with
    continuous_toFun :=
      (e.continuous_toFun.comp continuous_fst).prodMk
        (f.continuous_toFun.comp continuous_snd)
    continuous_invFun :=
      (e.continuous_invFun.comp continuous_fst).prodMk
        (f.continuous_invFun.comp continuous_snd) }

/-- Continuous multiplicative reassociation of a triple product. -/
noncomputable def continuousMulEquivProdAssoc
    (A B C : Type*) [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [MulOneClass A] [MulOneClass B] [MulOneClass C] :
    (A × B) × C ≃ₜ* A × (B × C) :=
  { MulEquiv.prodAssoc with
    continuous_toFun :=
      (continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    continuous_invFun :=
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd) }

end Padic
end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Basic topological product equivalences for profinite units

This module contains the reusable, inexpensive product equivalences used by
the compiled stages of the profinite-unit decomposition.
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.Padic

namespace ProfiniteUnitDecomposition.Internal

/-- The prime certificate shared by every compiled stage of the profinite
unit decomposition. -/
instance primeFact (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

end ProfiniteUnitDecomposition.Internal

/-- Coordinatewise product of topological multiplicative equivalences. -/
noncomputable def continuousMulEquivPiCongr
    {ι : Type*} {A B : ι → Type*}
    [(i : ι) → TopologicalSpace (A i)]
    [(i : ι) → TopologicalSpace (B i)]
    [(i : ι) → Mul (A i)] [(i : ι) → Mul (B i)]
    (e : (i : ι) → A i ≃ₜ* B i) :
    ((i : ι) → A i) ≃ₜ* ((i : ι) → B i) :=
  { MulEquiv.piCongrRight fun i => (e i).toMulEquiv with
    continuous_toFun :=
      continuous_pi fun i =>
        (e i).continuous_toFun.comp (continuous_apply i)
    continuous_invFun :=
      continuous_pi fun i =>
        (e i).continuous_invFun.comp (continuous_apply i) }

/-- Multiplicative tagging commutes with topological products. -/
noncomputable def continuousPiMultiplicative
    {ι : Type*} (A : ι → Type*)
    [(i : ι) → TopologicalSpace (A i)]
    [(i : ι) → Add (A i)] :
    Multiplicative ((i : ι) → A i) ≃ₜ*
      ((i : ι) → Multiplicative (A i)) :=
  { MulEquiv.piMultiplicative A with
    continuous_toFun :=
      continuous_pi fun i => continuous_apply i
    continuous_invFun :=
      continuous_pi fun i => continuous_apply i }

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_RationalCyclotomicField
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The rational cyclotomic closure

This file constructs the actual field `ℚ(μ∞)` inside `SeparableClosure ℚ`.
It uses mathlib's general `IsCyclotomicExtension` API, so the infinite
field and its finite cyclotomic levels are not replaced by abstract copies
of their expected Galois groups.

The finite levels form the divisibility-directed system whose supremum is
the whole cyclotomic field.  This supplies the field-theoretic source for
the rational cyclotomic calculation.
-/

noncomputable section

namespace KummerTheory

/-- The actual field `ℚ(μ∞)` in a fixed separable closure of `ℚ`. -/
def rationalCyclotomicField :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  IntermediateField.adjoin ℚ
    {ζ : SeparableClosure ℚ |
      ∃ n ∈ (Set.univ : Set ℕ), n ≠ 0 ∧ ζ ^ n = 1}

/-- The field `ℚ(μ∞)` is the cyclotomic extension generated by roots of
unity of all positive orders. -/
noncomputable instance rationalCyclotomicField_isCyclotomicExtension :
    IsCyclotomicExtension (Set.univ : Set ℕ) ℚ
      rationalCyclotomicField := by
  exact
    IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      (Set.univ : Set ℕ) ℚ (SeparableClosure ℚ)
      (fun n _hn hn0 =>
        IsCyclotomicExtension.exists_isPrimitiveRoot
          (S := (Set.univ : Set ℕ))
          (SeparableClosure ℚ) (SeparableClosure ℚ)
          (Set.mem_univ n) hn0)

/-- The actual infinite rational cyclotomic extension is abelian Galois. -/
noncomputable instance rationalCyclotomicField_isAbelianGalois :
    IsAbelianGalois ℚ rationalCyclotomicField :=
  IsCyclotomicExtension.isAbelianGalois
    (Set.univ : Set ℕ) ℚ rationalCyclotomicField

/-- The `n`-th finite cyclotomic level inside `ℚ(μ∞)`.  Positive naturals
are used so that the zero-order degeneracy cannot enter the directed
system. -/
def rationalCyclotomicLevel (n : ℕ+) :
    IntermediateField ℚ rationalCyclotomicField :=
  IntermediateField.adjoin ℚ
    {ζ : rationalCyclotomicField |
      ∃ m ∈ ({(n : ℕ)} : Set ℕ),
        m ≠ 0 ∧ ζ ^ m = 1}

/-- Each internal finite level is the standard singleton cyclotomic
extension. -/
noncomputable instance rationalCyclotomicLevel_isCyclotomicExtension
    (n : ℕ+) :
    IsCyclotomicExtension {(n : ℕ)} ℚ
      (rationalCyclotomicLevel n) := by
  exact
    IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      {(n : ℕ)} ℚ rationalCyclotomicField
      (fun m _hm _hm0 =>
        IsCyclotomicExtension.exists_isPrimitiveRoot
          (S := (Set.univ : Set ℕ))
          ℚ rationalCyclotomicField
          (Set.mem_univ m) _hm0)

/-- Every finite internal cyclotomic level is Galois over `ℚ`. -/
noncomputable instance rationalCyclotomicLevel_isGalois
    (n : ℕ+) :
    IsGalois ℚ (rationalCyclotomicLevel n) :=
  IsCyclotomicExtension.isGalois
    {(n : ℕ)} ℚ (rationalCyclotomicLevel n)

/-- A finite level of `ℚ(μ∞)` carries mathlib's standard number-field
structure coming from its singleton cyclotomic presentation. -/
noncomputable instance rationalCyclotomicLevel_numberField
    (n : ℕ+) :
    NumberField (rationalCyclotomicLevel n) :=
  IsCyclotomicExtension.numberField
    {(n : ℕ)} ℚ (rationalCyclotomicLevel n)

/-- Divisibility of orders gives the canonical inclusion between internal
cyclotomic levels. -/
theorem rationalCyclotomicLevel_mono
    {m n : ℕ+}
    (h : (m : ℕ) ∣ (n : ℕ)) :
    rationalCyclotomicLevel m ≤
      rationalCyclotomicLevel n :=
  IntermediateField.isCyclotomicExtension_le_of_dvd
    ℚ rationalCyclotomicField (m : ℕ) (n : ℕ)
    (rationalCyclotomicLevel m)
    (rationalCyclotomicLevel n)
    (h₁ := rationalCyclotomicLevel_isCyclotomicExtension m)
    (h₂ := rationalCyclotomicLevel_isCyclotomicExtension n)
    h

/-- The internal finite cyclotomic levels exhaust `ℚ(μ∞)`. -/
theorem iSup_rationalCyclotomicLevel :
    (⨆ n : ℕ+, rationalCyclotomicLevel n) = ⊤ := by
  have htop :
      IntermediateField.adjoin ℚ
          {ζ : rationalCyclotomicField |
            ∃ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧
              n ≠ 0 ∧ ζ ^ n = 1} =
        ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra ℚ _
      ((IsCyclotomicExtension.iff_adjoin_eq_top
        (Set.univ : Set ℕ) ℚ rationalCyclotomicField).1
          inferInstance).2
  apply le_antisymm le_top
  rw [← htop, IntermediateField.adjoin_le_iff]
  rintro ζ ⟨n, _hn, hn0, hpow⟩
  let npos : ℕ+ := ⟨n, Nat.pos_of_ne_zero hn0⟩
  exact
    (le_iSup
      (fun m : ℕ+ => rationalCyclotomicLevel m) npos)
      (IntermediateField.subset_adjoin ℚ
        {x : rationalCyclotomicField |
          ∃ m ∈ ({(npos : ℕ)} : Set ℕ),
            m ≠ 0 ∧ x ^ m = 1}
        (by
          refine
            ⟨(npos : ℕ), by simp, npos.ne_zero, ?_⟩
          change ζ ^ n = 1
          exact hpow))

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_RationalCyclotomicCharacter
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The cyclotomic character of the rational cyclotomic field

This file assembles mathlib's `p`-adic cyclotomic characters of the
actual extension `rationalCyclotomicField / ℚ`.  Their product takes
values in the canonical product of the local unit groups, and the
topological Chinese-remainder equivalence identifies that product with
`ZHatˣ`.

No abstract copy of either the Galois group or its expected target is
introduced here.
-/

noncomputable section

namespace KummerTheory

/-- The actual rational cyclotomic field contains primitive roots of
unity of every nonzero order. -/
noncomputable instance rationalCyclotomicField_hasEnoughRootsOfUnity
    (n : ℕ) [NeZero n] :
    HasEnoughRootsOfUnity rationalCyclotomicField n where
  prim :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      (S := (Set.univ : Set ℕ))
      ℚ rationalCyclotomicField (Set.mem_univ n) (NeZero.ne n)
  cyc := rootsOfUnity.isCyclic rationalCyclotomicField n

local instance instFactPrimeValNat_solutions (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

/-- The product, over all rational primes, of mathlib's `p`-adic
cyclotomic characters of `Gal(rationalCyclotomicField / ℚ)`. -/
noncomputable def rationalCyclotomicCharacterPrimeProduct :
    (rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField) →ₜ*
      ((p : Nat.Primes) → ℤ_[p.1]ˣ) where
  toMonoidHom :=
    MonoidHom.pi fun p =>
      (cyclotomicCharacter rationalCyclotomicField p.1).comp
        (MulSemiringAction.toRingAut
          (rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
          rationalCyclotomicField)
  continuous_toFun :=
    continuous_pi fun p =>
      cyclotomicCharacter.continuous
        p.1 ℚ rationalCyclotomicField

/-- Evaluation at a prime is the corresponding mathlib cyclotomic
character. -/
@[simp]
theorem rationalCyclotomicCharacterPrimeProduct_apply
    (σ : rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
    (p : Nat.Primes) :
    rationalCyclotomicCharacterPrimeProduct σ p =
      cyclotomicCharacter rationalCyclotomicField p.1
        (MulSemiringAction.toRingAut
          (rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
          rationalCyclotomicField σ) :=
  rfl

section PrimePowerCharacter

-- Expose the exact prime-power index to instance synthesis. Both
-- proposition-valued instances are supplied by the existing canonical factories.
local instance primePowerLevelNumberField (p : Nat.Primes) (k : ℕ) :
    NumberField (rationalCyclotomicLevel ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevel_numberField ⟨p.1 ^ k, pow_pos p.2.pos k⟩

local instance primePowerLevelIsGalois (p : Nat.Primes) (k : ℕ) :
    IsGalois ℚ (rationalCyclotomicLevel ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevel_isGalois ⟨p.1 ^ k, pow_pos p.2.pos k⟩

/-- Reduction of the `p`-coordinate modulo `p ^ k` is the standard
mathlib character of the finite internal cyclotomic level. -/
theorem rationalCyclotomicCharacterPrimeProduct_toZModPow
    (σ : rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
    (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalCyclotomicCharacterPrimeProduct σ p) =
      IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ k)
        (rationalCyclotomicLevel
          ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (hK :=
          rationalCyclotomicLevel_isCyclotomicExtension
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        (σ.restrictNormal
          (rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)) := by
  let n : ℕ+ := ⟨p.1 ^ k, pow_pos p.2.pos k⟩
  let F := rationalCyclotomicLevel n
  let : IsCyclotomicExtension {p.1 ^ k} ℚ F := by
    change IsCyclotomicExtension {(n : ℕ)} ℚ (rationalCyclotomicLevel n)
    exact rationalCyclotomicLevel_isCyclotomicExtension n
  let ζ : F :=
    IsCyclotomicExtension.zeta (p.1 ^ k) ℚ F
  have hζ : IsPrimitiveRoot ζ (p.1 ^ k) :=
    IsCyclotomicExtension.zeta_spec (p.1 ^ k) ℚ F
  let t : rationalCyclotomicField :=
    algebraMap F rationalCyclotomicField ζ
  have ht : t ^ (p.1 ^ k) = 1 := by
    dsimp only [t]
    rw [← map_pow, hζ.pow_eq_one, map_one]
  let g : rationalCyclotomicField ≃+* rationalCyclotomicField :=
    MulSemiringAction.toRingAut
      (rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
      rationalCyclotomicField σ
  have hinfinite :
      g t =
        t ^ ((cyclotomicCharacter
          rationalCyclotomicField p.1 g).val.toZModPow k).val :=
    cyclotomicCharacter.spec p.1 g t ht
  have hfinite :
      (σ.restrictNormal F) ζ =
        ζ ^ (IsCyclotomicExtension.Rat.galEquivZMod
          (p.1 ^ k) F (σ.restrictNormal F)).val.val :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (p.1 ^ k) F (σ.restrictNormal F) hζ.pow_eq_one
  have hζmap : IsPrimitiveRoot t (p.1 ^ k) := by
    exact hζ.map_of_injective
      (algebraMap F rationalCyclotomicField).injective
  change
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalCyclotomicCharacterPrimeProduct σ p) =
      IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ k) F (σ.restrictNormal F)
  apply Units.ext
  apply ZMod.val_injective
  apply hζmap.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  calc
    t ^ ((PadicInt.toZModPow k)
        (rationalCyclotomicCharacterPrimeProduct σ p).val).val =
        g t := by
      rw [rationalCyclotomicCharacterPrimeProduct_apply]
      exact hinfinite.symm
    _ = σ t := rfl
    _ = algebraMap F rationalCyclotomicField
        ((σ.restrictNormal F) ζ) :=
      (AlgEquiv.restrictNormal_commutes σ F ζ).symm
    _ = algebraMap F rationalCyclotomicField
        (ζ ^ (IsCyclotomicExtension.Rat.galEquivZMod
          (p.1 ^ k) F (σ.restrictNormal F)).val.val) := by
      rw [hfinite]
    _ = t ^ (IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ k) F (σ.restrictNormal F)).val.val := by
      rw [map_pow]

end PrimePowerCharacter

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_RationalCyclotomicCharacterEquiv
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The rational cyclotomic character equivalence

Finite cyclotomic levels are detected by their prime-power reductions,
using mathlib's Chinese-remainder equivalence for `ZMod`.  Surjectivity
is obtained from the finite-intersection property for the closed fibers
of the restriction maps to those levels.
-/

noncomputable section

namespace KummerTheory

local instance instFactPrimeValNat_solutions_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

/-- The `p ^ k` reduction of the cyclotomic character can be read from
any finite cyclotomic level whose order is divisible by `p ^ k`. -/
theorem rationalCyclotomicCharacterPrimeProduct_toZModPow_of_dvd
    (σ : rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
    (p : Nat.Primes) (k : ℕ) (n : ℕ+)
    (h : p.1 ^ k ∣ (n : ℕ)) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalCyclotomicCharacterPrimeProduct σ p) =
      ZMod.unitsMap h
        (IsCyclotomicExtension.Rat.galEquivZMod
          (n : ℕ) (rationalCyclotomicLevel n)
          (σ.restrictNormal (rationalCyclotomicLevel n))) := by
  let m : ℕ+ := ⟨p.1 ^ k, pow_pos p.2.pos k⟩
  let F := rationalCyclotomicLevel m
  let K := rationalCyclotomicLevel n
  let : IsCyclotomicExtension {p.1 ^ k} ℚ F := by
    change IsCyclotomicExtension {(m : ℕ)} ℚ
      (rationalCyclotomicLevel m)
    exact rationalCyclotomicLevel_isCyclotomicExtension m
  have hFK : F ≤ K :=
    rationalCyclotomicLevel_mono h
  let ζ : F :=
    IsCyclotomicExtension.zeta (p.1 ^ k) ℚ F
  have hζ : IsPrimitiveRoot ζ (p.1 ^ k) :=
    IsCyclotomicExtension.zeta_spec (p.1 ^ k) ℚ F
  let x : rationalCyclotomicField :=
    algebraMap F rationalCyclotomicField ζ
  have hζx : IsPrimitiveRoot x (p.1 ^ k) :=
    hζ.map_of_injective
      (algebraMap F rationalCyclotomicField).injective
  let y : K :=
    IntermediateField.inclusion hFK ζ
  have hy : y ^ (n : ℕ) = 1 := by
    apply Subtype.ext
    change x ^ (n : ℕ) = 1
    exact (hζx.pow_eq_one_iff_dvd _).2 h
  let a :=
    IsCyclotomicExtension.Rat.galEquivZMod
      (p.1 ^ k) F (σ.restrictNormal F)
  let b :=
    IsCyclotomicExtension.Rat.galEquivZMod
      (n : ℕ) K (σ.restrictNormal K)
  have ha :
      (σ.restrictNormal F) ζ =
        ζ ^ a.val.val := by
    exact
      IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
        (p.1 ^ k) F (σ.restrictNormal F) hζ.pow_eq_one
  have hb :
      (σ.restrictNormal K) y =
        y ^ b.val.val := by
    exact
      IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
        (n : ℕ) K (σ.restrictNormal K) hy
  change
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalCyclotomicCharacterPrimeProduct σ p) =
      ZMod.unitsMap h b
  calc
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalCyclotomicCharacterPrimeProduct σ p) =
        a := by
      simpa only [a, F, m] using
        rationalCyclotomicCharacterPrimeProduct_toZModPow σ p k
    _ = ZMod.unitsMap h b := by
      suffices x ^ a.val.val = x ^ b.val.val by
        rw [(hζx.isOfFinOrder (NeZero.ne _)).pow_inj_mod,
          ← hζx.eq_orderOf,
          ← ZMod.natCast_eq_natCast_iff',
          ZMod.natCast_val, ZMod.natCast_val,
          ZMod.cast_id] at this
        rwa [Units.ext_iff]
      calc
        x ^ a.val.val =
            algebraMap F rationalCyclotomicField
              (ζ ^ a.val.val) := by
          rw [map_pow]
        _ = algebraMap F rationalCyclotomicField
              ((σ.restrictNormal F) ζ) := by
          rw [ha]
        _ = σ x :=
          AlgEquiv.restrictNormal_commutes σ F ζ
        _ = algebraMap K rationalCyclotomicField
              ((σ.restrictNormal K) y) :=
          (AlgEquiv.restrictNormal_commutes σ K y).symm
        _ = algebraMap K rationalCyclotomicField
              (y ^ b.val.val) := by
          rw [hb]
        _ = x ^ b.val.val := by
          rw [map_pow]
          congr 1

/-- The product of the `p`-adic cyclotomic characters separates
automorphisms of the actual rational cyclotomic field. -/
theorem rationalCyclotomicCharacterPrimeProduct_injective :
    Function.Injective rationalCyclotomicCharacterPrimeProduct := by
  intro σ τ hστ
  have hrestrict (n : ℕ+) :
      σ.restrictNormal (rationalCyclotomicLevel n) =
        τ.restrictNormal (rationalCyclotomicLevel n) := by
    let K := rationalCyclotomicLevel n
    apply
      (IsCyclotomicExtension.Rat.galEquivZMod
        (n : ℕ) K).injective
    apply Units.ext
    let e :=
      ZMod.equivPi (n := (n : ℕ)) n.2.ne'
    apply e.injective
    funext q
    have hqPrime : q.1.Prime :=
      Nat.prime_of_mem_primeFactors q.2
    let p : Nat.Primes := ⟨q.1, hqPrime⟩
    let k := (n : ℕ).factorization q.1
    have hpow :
        p.1 ^ k ∣ (n : ℕ) :=
      (hqPrime.pow_dvd_iff_le_factorization n.2.ne').2 le_rfl
    have hpCoordinate :=
      congrArg (fun z => z p) hστ
    have hpReduction :=
      congrArg (Units.map (PadicInt.toZModPow k).toMonoidHom)
        hpCoordinate
    rw [
      rationalCyclotomicCharacterPrimeProduct_toZModPow_of_dvd
        σ p k n hpow,
      rationalCyclotomicCharacterPrimeProduct_toZModPow_of_dvd
        τ p k n hpow] at hpReduction
    have heval (z : ZMod (n : ℕ)) :
        e z q =
          ZMod.castHom hpow (ZMod (p.1 ^ k)) z := by
      change
        ((Pi.evalRingHom
            (fun r : (n : ℕ).primeFactors =>
              ZMod (r.1 ^ (n : ℕ).factorization r.1)) q).comp
          e.toRingHom) z =
            ZMod.castHom hpow (ZMod (p.1 ^ k)) z
      exact RingHom.congr_fun (Subsingleton.elim _ _) z
    rw [heval, heval]
    simpa only [p, k, ZMod.unitsMap_val,
      ZMod.castHom_apply] using
      congrArg
        (fun u : (ZMod (p.1 ^ k))ˣ =>
          (u : ZMod (p.1 ^ k)))
        hpReduction
  let E : IntermediateField ℚ rationalCyclotomicField :=
    { AlgHom.equalizer σ.toAlgHom τ.toAlgHom with
      inv_mem' := by
        intro x hx
        change σ x = τ x at hx
        change σ x⁻¹ = τ x⁻¹
        simpa only [map_inv₀] using congrArg Inv.inv hx }
  have hlevel (n : ℕ+) :
      rationalCyclotomicLevel n ≤ E := by
    intro x hx
    change σ x = τ x
    let y : rationalCyclotomicLevel n := ⟨x, hx⟩
    calc
      σ x =
          algebraMap (rationalCyclotomicLevel n)
            rationalCyclotomicField
            ((σ.restrictNormal
              (rationalCyclotomicLevel n)) y) :=
        (AlgEquiv.restrictNormal_commutes σ
          (rationalCyclotomicLevel n) y).symm
      _ = algebraMap (rationalCyclotomicLevel n)
            rationalCyclotomicField
            ((τ.restrictNormal
              (rationalCyclotomicLevel n)) y) := by
        rw [hrestrict n]
      _ = τ x :=
        AlgEquiv.restrictNormal_commutes τ
          (rationalCyclotomicLevel n) y
  have hE : E = ⊤ := by
    apply top_unique
    rw [← iSup_rationalCyclotomicLevel]
    exact iSup_le hlevel
  apply AlgEquiv.ext
  intro x
  have hx : x ∈ E := by
    rw [hE]
    trivial
  change x ∈ AlgHom.equalizer σ.toAlgHom τ.toAlgHom at hx
  exact (AlgHom.mem_equalizer σ.toAlgHom τ.toAlgHom x).mp hx

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_RationalCyclotomicTorsionField
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The torsion fixed field in the rational cyclotomic extension

The rational cyclotomic construction takes the fixed field of the closure
of the torsion subgroup in `Gal(ℚ(μ∞)/ℚ)`.  This file defines that actual closed subgroup
and fixed field.  No copy of the Galois group is replaced definitionally by
`ℤ̂ˣ`; the comparison with profinite units is a later theorem.
-/

noncomputable section

namespace KummerTheory

open scoped IsMulCommutative

/-- The closure of the torsion subgroup in the actual Krull-topological
Galois group of `ℚ(μ∞)/ℚ`. -/
def rationalCyclotomicTorsionClosure :
    ClosedSubgroup
      (rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField) where
  toSubgroup :=
    (CommGroup.torsion
      (rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField)).topologicalClosure
  isClosed' :=
    Subgroup.isClosed_topologicalClosure _

/-- The actual subfield of `ℚ(μ∞)` fixed by the closure of all
finite-order cyclotomic automorphisms. -/
def rationalCyclotomicTorsionFixedField :
    IntermediateField ℚ rationalCyclotomicField :=
  IntermediateField.fixedField
    rationalCyclotomicTorsionClosure.toSubgroup

/-- The torsion fixed field is integral over `ℚ`, since it is an
intermediate field of the rational cyclotomic extension. -/
noncomputable instance
    rationalCyclotomicTorsionFixedField_isIntegral :
    Algebra.IsIntegral ℚ rationalCyclotomicTorsionFixedField := by
  rw [Algebra.isIntegral_def]
  intro x
  exact IntermediateField.isIntegral_iff.mpr
    (Algebra.IsIntegral.isIntegral
      (x : rationalCyclotomicField))

/-- The torsion fixed field is normal over `ℚ`: its defining closed subgroup
is normal in the abelian cyclotomic Galois group. -/
noncomputable instance
    rationalCyclotomicTorsionFixedField_normal :
    Normal ℚ rationalCyclotomicTorsionFixedField := by
  let : Subgroup.Normal rationalCyclotomicTorsionClosure.toSubgroup :=
    inferInstance
  apply IntermediateField.normal_iff_forall_map_le'.mpr
  rintro σ x ⟨a, ha, rfl⟩ τ
  exact
    (AlgEquiv.symm_apply_eq σ).mp
      (ha
        ⟨σ⁻¹ * τ * σ,
          Subgroup.Normal.conj_mem'
            (H := rationalCyclotomicTorsionClosure.toSubgroup)
            inferInstance τ.1 τ.2 σ⟩)

/-- The torsion-fixed cyclotomic field is Galois over `ℚ`. -/
noncomputable instance
    rationalCyclotomicTorsionFixedField_isGalois :
    IsGalois ℚ rationalCyclotomicTorsionFixedField :=
  isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

/-- The torsion-fixed subextension of the abelian rational cyclotomic
extension is itself abelian Galois. -/
noncomputable instance
    rationalCyclotomicTorsionFixedField_isAbelianGalois :
    IsAbelianGalois ℚ rationalCyclotomicTorsionFixedField :=
  IsAbelianGalois.tower_bot ℚ rationalCyclotomicTorsionFixedField
    rationalCyclotomicField

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_GeneralTowerNaturality
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Restriction naturality in an arbitrary finite abelian tower

The fixed-separable-closure form of finite local reciprocity naturality is
transported here to an arbitrary tower `K ⊂ E ⊂ L`.  The two extensions are
realized compatibly in the chosen separable closure by first embedding `L`
and then restricting that embedding to `E`.  Abstract norm--residue
naturality then becomes the actual restriction homomorphism
`Gal(L/K) → Gal(E/K)`.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory KummerTheory
open LocalClassFieldTheory
open scoped IsMulCommutative

def towerLowerEmbedding
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    (iL : L →ₐ[K] SeparableClosure K) :
    E →ₐ[K] SeparableClosure K :=
  iL.comp (IsScalarTower.toAlgHom K E L)

theorem towerEmbeddedFieldRange_le
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    (iL : L →ₐ[K] SeparableClosure K) :
    AlgHom.fieldRange (towerLowerEmbedding K E L iL) ≤
      AlgHom.fieldRange iL := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact ⟨algebraMap E L y, rfl⟩

/-- When `L` is regarded as an `M`-algebra through the inverse of a
`K`-algebra equivalence, restriction from `L` to `M` is conjugation by that
equivalence. -/
theorem restrictNormalHom_eq_autCongr
    (K L M : Type)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [Normal K M]
    (e : L ≃ₐ[K] M) :
    letI : Algebra M L := e.symm.toRingHom.toAlgebra
    letI : IsScalarTower K M L :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        exact (e.symm.commutes x).symm)
    (AlgEquiv.restrictNormalHom M :
        Gal(L / K) →* Gal(M / K)) =
      (AlgEquiv.autCongr e).toMonoidHom := by
  let : Algebra M L := e.symm.toRingHom.toAlgebra
  let : IsScalarTower K M L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (e.symm.commutes x).symm)
  apply MonoidHom.ext
  intro sigma
  apply AlgEquiv.ext
  intro x
  apply e.symm.injective
  calc
    e.symm ((AlgEquiv.restrictNormalHom M sigma) x) =
        sigma (e.symm x) := by
      exact AlgEquiv.restrictNormal_commutes sigma M x
    _ = e.symm ((AlgEquiv.autCongr e sigma) x) := by
      simp [AlgEquiv.autCongr_apply]

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_CrossLocalRestriction
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

theorem finitePlaceCrossDecompositionTransport_core
    {K K' L L' C D E E' : Type}
    [Field K] [Field K'] [Field L] [Field L']
    [Field C] [Field D] [Field E] [Field E']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra K L] [Algebra L L'] [IsScalarTower K L L']
    [Normal K L]
    [Algebra C D] [Algebra D E'] [Algebra C E']
    [IsScalarTower C D E']
    [Algebra C E] [Algebra E E'] [IsScalarTower C E E']
    [Normal C E]
    (phiLower : (E ≃ₐ[C] E) → (L ≃ₐ[K] L))
    (phiUpper : (E' ≃ₐ[D] E') → (L' ≃ₐ[K'] L'))
    (lowerEmbedding : L →+* E)
    (upperEmbedding : L' →+* E')
    (hEmbedding : ∀ z : L,
      algebraMap E E' (lowerEmbedding z) =
        upperEmbedding (algebraMap L L' z))
    (hUpperAction : ∀ (tau : E' ≃ₐ[D] E') (z : L'),
      upperEmbedding (phiUpper tau z) =
        tau (upperEmbedding z))
    (hLowerAction : ∀ (tau : E ≃ₐ[C] E) (z : L),
      tau (lowerEmbedding z) =
        lowerEmbedding (phiLower tau z))
    (tauUpper : E' ≃ₐ[D] E') :
    AlgEquiv.restrictNormalHom L
        (AlgEquiv.restrictScalarsHom K (phiUpper tauUpper)) =
      phiLower
        (AlgEquiv.restrictNormalHom E
          (AlgEquiv.restrictScalarsHom C tauUpper)) := by
  let tauLower :=
    AlgEquiv.restrictNormalHom E
      (AlgEquiv.restrictScalarsHom C tauUpper)
  apply AlgEquiv.ext
  intro z
  apply (algebraMap L L').injective
  apply upperEmbedding.injective
  calc
    upperEmbedding
        (algebraMap L L'
          ((AlgEquiv.restrictNormalHom L
            (AlgEquiv.restrictScalarsHom K
              (phiUpper tauUpper))) z)) =
      upperEmbedding
        (phiUpper tauUpper (algebraMap L L' z)) := by
      exact congrArg upperEmbedding
        (AlgEquiv.restrictNormal_commutes
          (AlgEquiv.restrictScalarsHom K
            (phiUpper tauUpper)) L z)
    _ = tauUpper
        (upperEmbedding (algebraMap L L' z)) :=
      hUpperAction tauUpper (algebraMap L L' z)
    _ = tauUpper
        (algebraMap E E' (lowerEmbedding z)) := by
      rw [hEmbedding]
    _ = algebraMap E E'
        (tauLower (lowerEmbedding z)) := by
      exact
        (AlgEquiv.restrictNormal_commutes
          (AlgEquiv.restrictScalarsHom C tauUpper)
          E (lowerEmbedding z)).symm
    _ = algebraMap E E'
        (lowerEmbedding (phiLower tauLower z)) := by
      rw [hLowerAction]
    _ = upperEmbedding
        (algebraMap L L' (phiLower tauLower z)) := by
      rw [hEmbedding]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_FiniteExtensionTopology
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The canonical topology on a finite extension of a local field

This file packages the spectral norm topology on a finite extension of a
nonarchimedean local field.  The definitions are deliberately explicit: they
let downstream constructions put several finite extensions in one diagram
while using the same topology on every field.
-/

noncomputable section

namespace LocalFieldTheory

open scoped NNReal ValuativeRel

/-- The normed-field structure canonically associated with the native
topology of a nonarchimedean local field. -/
@[reducible]
noncomputable def localFieldNontriviallyNormedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : NontriviallyNormedField K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  exact Valued.toNontriviallyNormedField
    (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)

/-- The native norm obtained from a nonarchimedean local field is
ultrametric.  This is kept as a named companion to
`localFieldNontriviallyNormedField` so that every use of the spectral norm
starts from the same norm and the same ultrametric structure. -/
theorem localFieldIsUltrametricDist
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField K :=
      localFieldNontriviallyNormedField K
    IsUltrametricDist K := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  let : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  infer_instance

/-- A finite extension, equipped with the spectral norm extending the native
topology of its nonarchimedean local base field. -/
@[reducible]
noncomputable def finiteExtensionSpectralNormedField
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : NontriviallyNormedField L := by
  letI : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  letI : IsUltrametricDist K := localFieldIsUltrametricDist K
  exact spectralNorm.nontriviallyNormedField K L

/-- A finite extension is locally compact for its canonical spectral norm. -/
theorem finiteExtensionSpectralLocallyCompactSpace
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    LocallyCompactSpace L := by
  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K := localFieldIsUltrametricDist K
  exact
    (fun (V : Type) [nV : NontriviallyNormedField V]
        [spaceKV : NormedSpace K V] [FiniteDimensional K V] =>
      LocallyCompactSpace.of_finiteDimensional_of_complete K V)
      L (nV := finiteExtensionSpectralNormedField K L)
      (spaceKV := spectralNorm.normedSpace K L)

/-- The spectral norm on a finite extension of a nonarchimedean local field
is ultrametric. -/
theorem finiteExtensionSpectralIsUltrametricDist
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    IsUltrametricDist L := by
  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K := localFieldIsUltrametricDist K
  exact
    (fun (F : Type) [nF : NormedField F]
        (h : IsNonarchimedean (norm : F → ℝ)) =>
      IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm h)
      L (nF := (finiteExtensionSpectralNormedField K L).toNormedField)
      (isNonarchimedean_spectralNorm (K := K) (L := L))

/-- The valuative relation induced by the canonical spectral norm. -/
@[reducible]
noncomputable def finiteExtensionSpectralValuativeRel
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    ValuativeRel L := by
  letI hUltra := finiteExtensionSpectralIsUltrametricDist K L
  exact ValuativeRel.ofValuation
    (NormedField.valuation (K := L)
      (hK := (finiteExtensionSpectralNormedField K L).toNormedField))

/-- The valuative relation coming from the spectral norm is the canonical
extension of the native valuation on the local base field. -/
theorem finiteExtensionSpectralValuation_hasExtension
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    letI : ValuativeRel L := finiteExtensionSpectralValuativeRel K L
    Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L) := by
  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K := localFieldIsUltrametricDist K
  let : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  apply Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, Valuation.mem_integer_iff]
  have hL :=
    (fun (F : Type) [nF : NormedField F] [hUltra : IsUltrametricDist F]
        (y : F) =>
      let v : Valuation F ℝ≥0 := NormedField.valuation (K := F)
      letI : ValuativeRel F := ValuativeRel.ofValuation v
      letI : v.Compatible := Valuation.Compatible.ofValuation v
      (Valuation.vle_one_iff (ValuativeRel.valuation F) (x := y)).symm.trans
        (Valuation.vle_one_iff v (x := y)))
      L (nF := (finiteExtensionSpectralNormedField K L).toNormedField)
      (hUltra := finiteExtensionSpectralIsUltrametricDist K L)
      (algebraMap K L x)
  refine hL.trans ?_
  change spectralNorm K L (algebraMap K L x) ≤ 1 ↔
    ValuativeRel.valuation K x ≤ 1
  rw [spectralNorm_extends (K := K) (L := L) x]
  exact Valued.toNormedField.norm_le_one_iff
    (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)

/-- If `E/K` and `L/K` carry their canonical `K`-spectral norms in a
tower `K \to E \to L`, then the given `E`-algebra structure on `L` is a
normed algebra.  In particular, inclusion and norm maps in finite towers are
continuous for one topology on each field. -/
@[reducible]
noncomputable def finiteExtensionSpectralNormedAlgebra
    (K E L : Type) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField E :=
      finiteExtensionSpectralNormedField K E
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    NormedAlgebra E L := by
  letI : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  letI : IsUltrametricDist K := localFieldIsUltrametricDist K
  exact
    (fun (F : Type) [nF : NormedField F] [aKF : NormedAlgebra K F]
        [Algebra F L] [IsScalarTower K F L] =>
      spectralNorm.normedAlgebra' (K := K) F L)
      E (nF := (finiteExtensionSpectralNormedField K E).toNormedField)
      (aKF := spectralNorm.normedAlgebra K E)

end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldLocalData
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Canonical local data on finite fixed fields

This file compares the normalized valuation induced on a finite abstract
field by the local class formation with the ordinary normalized valuation
of its concrete fixed field.  The concrete field is equipped with the
canonical spectral extension of the topology on the original local field.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped NNReal Pointwise ValuativeRel
open LocalFieldTheory RamificationTheory

@[reducible]
def valuationSubringEquivOfComapEq
    {L M : Type} [Field L] [Field M]
    (A : ValuationSubring M) (B : ValuationSubring L)
    (e : L ≃+* M) (h : B = A.comap e.toRingHom) :
    B ≃+* A where
  toFun x := ⟨e x, by
    change (x : L) ∈ A.comap e.toRingHom
    rw [← h]
    exact x.property⟩
  invFun y := ⟨e.symm y, by
    rw [h]
    change e (e.symm y) ∈ A
    simp⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_mul' x y := by
    ext
    simp
  map_add' x y := by
    ext
    simp

theorem semilinearConjugate_commutes
    {k k' Omega Omega' : Type}
    [Field k] [Field k'] [Field Omega] [Field Omega']
    [Algebra k Omega] [Algebra k' Omega']
    (tau : k ≃+* k') (e : Omega ≃+* Omega')
    (he :
      ∀ x : k,
        e (algebraMap k Omega x) =
          algebraMap k' Omega' (tau x))
    (sigma : Omega ≃ₐ[k] Omega) (x : k') :
    e (sigma (e.symm (algebraMap k' Omega' x))) =
      algebraMap k' Omega' x := by
  have hpre :
      e.symm (algebraMap k' Omega' x) =
        algebraMap k Omega (tau.symm x) := by
    apply e.injective
    rw [e.apply_symm_apply, he, tau.apply_symm_apply]
  rw [hpre, sigma.commutes, he, tau.apply_symm_apply]


end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldRelativeNorm
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Relative norms on actual fixed fields

This file identifies the class-formation relative norm on ambient fixed units
with the ordinary field norm between two concrete fixed fields.  The
intermediate extension need not be normal: relative left cosets are
identified with field embeddings into the common separably closed ambient
field, and both norms are then the same product of conjugates.
-/

noncomputable section

open scoped BigOperators

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory KummerTheory
open LocalClassFieldTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsSepClosed Ω]

noncomputable local instance finiteSeparableAlgHomFintypeRelative
    {F E T : Type} [Field F] [Field E] [Field T]
    [Algebra F E] [Algebra F T]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    Fintype (E →ₐ[F] T) :=
  PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable F E)

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_GroupTheory_ContinuousQuotientEquiv
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Continuous equivalences of quotient groups

This module supplies the quotient equivalence induced by a continuous
multiplicative equivalence.  It belongs to the general local-field support
layer and does not depend on the separate pro-\(C\) groups library.
-/

open scoped Topology

noncomputable section

namespace LocalFieldTheory.QuotientGroup

universe u v

variable {G : Type u} {H : Type v}
variable [Group G] [TopologicalSpace G]
variable [Group H] [TopologicalSpace H]

/-- A continuous multiplicative equivalence descends to continuously
equivalent quotients when it maps one normal subgroup onto the other. -/
noncomputable def continuousCongr
    (N : Subgroup G) (M : Subgroup H) [N.Normal] [M.Normal]
    (e : G ≃ₜ* H) (h : N.map e.toMulEquiv.toMonoidHom = M) :
    G ⧸ N ≃ₜ* H ⧸ M := by
  let eAlg : G ⧸ N ≃* H ⧸ M :=
    QuotientGroup.congr (G' := N) (H' := M) e.toMulEquiv h
  refine
    { toMulEquiv := eAlg
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · refine (QuotientGroup.isQuotientMap_mk N).continuous_iff.2 ?_
    change Continuous fun x : G => QuotientGroup.mk' M (e x)
    exact continuous_quotient_mk'.comp e.continuous_toFun
  · refine (QuotientGroup.isQuotientMap_mk M).continuous_iff.2 ?_
    have hsymm : M.map e.symm.toMulEquiv.toMonoidHom = N :=
      (Subgroup.map_symm_eq_iff_map_eq (K := N) (H := M)
        (e := e.toMulEquiv)).mpr h
    change Continuous fun y : H => QuotientGroup.mk' N (e.symm y)
    exact continuous_quotient_mk'.comp e.symm.continuous_toFun

/-- The descended equivalence acts on quotient classes through the original
equivalence. -/
@[simp] theorem continuousCongr_mk
    (N : Subgroup G) (M : Subgroup H) [N.Normal] [M.Normal]
    (e : G ≃ₜ* H) (h : N.map e.toMulEquiv.toMonoidHom = M) (g : G) :
    continuousCongr N M e h (QuotientGroup.mk' N g) =
      QuotientGroup.mk' M (e g) :=
  rfl

end LocalFieldTheory.QuotientGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientNormResidue
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Ambient embedded norm-residue values

This module defines the ambient fixed-field norm-residue value attached
to a unit of the intrinsically presented base field, both before and
after identifying the abelianization of an abelian Galois group with
the group itself.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory KummerTheory
open scoped ValuativeRel
open scoped IsMulCommutative

/-- The separable-closure equivalence used to compare the intrinsic extension
over `F` with its realization inside the ambient separable closure of `K`. -/
abbrev ambientEmbeddedSeparableClosureEquiv
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) :=
  @AlgEquiv F (SeparableClosure F) (SeparableClosure K)
    _ _ _
    (separableClosure F (AlgebraicClosure F)).algebra
    (j.comp (IsScalarTower.toAlgHom K F E)).toRingHom.toAlgebra

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeWitness
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Ambient prime witnesses

This module constructs the ambient norm-residue value, a valuation-one
prime witness for each abelianized Galois element, and the corresponding
ambient Frobenius target.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory KummerTheory
open scoped ValuativeRel

/-- Transporting an identified abelianized prime value back through one
quotient equivalence and forward through another preserves its target. -/
theorem abelianizationCongr_symm_eq_primeTarget
    {Q₀ G₀ G : Type}
    [Group Q₀] [Group G₀] [Group G]
    (q₀ : Q₀ ≃* G₀)
    (qE : Q₀ ≃* G)
    (qAmbient : Q₀)
    (r : Additive (Abelianization G₀))
    (hprime :
      r =
        Additive.ofMul
          (q₀.abelianizationCongr
            (Abelianization.of qAmbient))) :
    qE.abelianizationCongr
        (q₀.abelianizationCongr.symm
          (Additive.toMul r)) =
      qE.abelianizationCongr
        (Abelianization.of qAmbient) := by
  have hprimeMul :=
    congrArg Additive.toMul hprime
  change
    Additive.toMul r =
      q₀.abelianizationCongr
        (Abelianization.of qAmbient) at hprimeMul
  calc
    qE.abelianizationCongr
        (q₀.abelianizationCongr.symm
          (Additive.toMul r)) =
        qE.abelianizationCongr
          (q₀.abelianizationCongr.symm
            (q₀.abelianizationCongr
              (Abelianization.of qAmbient))) :=
      congrArg qE.abelianizationCongr
        (congrArg q₀.abelianizationCongr.symm hprimeMul)
    _ = qE.abelianizationCongr
          (Abelianization.of qAmbient) := by
      rw [q₀.abelianizationCongr.symm_apply_apply]

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

theorem finitePlaceArtinHasExtension_of_norm
    {A B C D : Type}
    [NormedField A] [NormedField B]
    [NormedField C] [NormedField D]
    [Algebra C D]
    [Valued C ℝ≥0] [Valued D ℝ≥0]
    [ValuativeRel C] [ValuativeRel D]
    [(Valued.v : Valuation C ℝ≥0).Compatible]
    [(Valued.v : Valuation D ℝ≥0).Compatible]
    (eC : C ≃+* A) (eD : D ≃+* B)
    (baseMap : A →+* B)
    (hAlgebraMap : ∀ x : C,
      algebraMap C D x =
        eD.symm (baseMap (eC x)))
    (hDNorm : ∀ y : B, ‖eD.symm y‖ = ‖y‖)
    (hCNorm : ∀ x : C, ‖eC x‖ = ‖x‖)
    (hBaseNorm : ∀ x : A,
      ‖baseMap x‖ ≤ 1 ↔ ‖x‖ ≤ 1)
    (hDValuation : ∀ x : D,
      (Valued.v : Valuation D ℝ≥0) x = ‖x‖₊)
    (hCValuation : ∀ x : C,
      (Valued.v : Valuation C ℝ≥0) x = ‖x‖₊) :
    (ValuativeRel.valuation C).HasExtension
      (ValuativeRel.valuation D) := by
  let vC : Valuation C ℝ≥0 := Valued.v
  let vD : Valuation D ℝ≥0 := Valued.v
  apply Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, Valuation.mem_integer_iff]
  rw [
    ← (ValuativeRel.valuation D).vle_one_iff,
    vD.vle_one_iff,
    ← (ValuativeRel.valuation C).vle_one_iff,
    vC.vle_one_iff]
  rw [hDValuation, hCValuation]
  have hTargetNorm :
      ‖algebraMap C D x‖ =
        ‖baseMap (eC x)‖ := by
    rw [hAlgebraMap]
    exact hDNorm (baseMap (eC x))
  have hTargetNormNN :
      ‖algebraMap C D x‖₊ =
        ‖baseMap (eC x)‖₊ := by
    apply NNReal.eq
    exact hTargetNorm
  have hSourceNormNN :
      ‖eC x‖₊ = ‖x‖₊ := by
    apply NNReal.eq
    exact hCNorm x
  rw [hTargetNormNN, ← hSourceNormNN]
  exact_mod_cast hBaseNorm (eC x)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FiniteIdeleArtin
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The finite-place product of local Artin homomorphisms

For a finite abelian extension of number fields `L / K`, the local
Artin factors of an idele are trivial at all but finitely many finite
places.  This file forms their `finprod` directly in the actual global
Galois group.
-/

open scoped Classical IsMulCommutative NumberField NNReal ValuativeRel
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open Function

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- A finitely supported product may be regrouped over the fibers of an
arbitrary indexing map. -/
theorem finprod_fibers_eq_sigma
    {α β G : Type*} [CommMonoid G]
    (g : α → β) (f : α → G)
    (hf : HasFiniteMulSupport f) :
    (∏ᶠ b : β,
        ∏ᶠ x : {x : α // g x = b}, f x.1) =
      ∏ᶠ x : α, f x := by
  classical
  let s := hf.toFinset
  have hFiber (b : β) :
      (∏ᶠ x : {x : α // g x = b}, f x.1) =
        ∏ x ∈ s with g x = b, f x := by
    rw [finprod_eq_prod_of_mulSupport_subset
      (fun x : {x : α // g x = b} => f x.1)
      (s := s.subtype fun x => g x = b)]
    · simp only [Finset.prod_subtype_eq_prod_filter]
    · intro x hx
      change x ∈ s.subtype (fun x => g x = b)
      change f x.1 ≠ 1 at hx
      exact Finset.mem_subtype.mpr (hf.mem_toFinset.2 hx)
  calc
    (∏ᶠ b : β,
        ∏ᶠ x : {x : α // g x = b}, f x.1) =
        ∏ᶠ b : β,
          ∏ x ∈ s with g x = b, f x :=
      finprod_congr hFiber
    _ = ∏ x ∈ s, f x := by
      rw [finprod_eq_prod_of_mulSupport_subset _
        (s.mulSupport_of_fiberwise_prod_subset_image f g)]
      exact
        Finset.prod_fiberwise_of_maps_to
          (t := s.image g)
          (fun x hx => Finset.mem_image_of_mem g hx) f
    _ = ∏ᶠ x : α, f x :=
      (finprod_eq_prod f hf).symm

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section Galois

variable [IsGalois K L]

noncomputable def ramifiedInfinitePlaceConjugation
    (w : InfinitePlace L) (hRamified : w.IsRamified K) :
    L ≃ₐ[K] L :=
  Classical.choose
    (InfinitePlace.exists_isConj_of_isRamified
      (k := K) (K := L)
      ((InfinitePlace.mk_embedding w).symm ▸ hRamified))

omit [NumberField K] [NumberField L] in
theorem ramifiedInfinitePlaceConjugation_isConj
    (w : InfinitePlace L) (hRamified : w.IsRamified K) :
    NumberField.ComplexEmbedding.IsConj
      (InfinitePlace.embedding w)
      (ramifiedInfinitePlaceConjugation
        (K := K) w hRamified) :=
  Classical.choose_spec
    (InfinitePlace.exists_isConj_of_isRamified
      (k := K) (K := L)
      ((InfinitePlace.mk_embedding w).symm ▸ hRamified))

omit [NumberField K] [NumberField L] in
theorem ramifiedInfinitePlaceConjugation_sq
    (w : InfinitePlace L) (hRamified : w.IsRamified K) :
    ramifiedInfinitePlaceConjugation
          (K := K) w hRamified *
        ramifiedInfinitePlaceConjugation
          (K := K) w hRamified =
      1 := by
  ext x
  simpa using
    NumberField.ComplexEmbedding.isConj_apply_apply
      (ramifiedInfinitePlaceConjugation_isConj
        (K := K) w hRamified) x

end Galois

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- Every infinite place of `ℚ` is the canonical real place. -/
theorem rationalInfinitePlace_isReal
    (v : InfinitePlace ℚ) :
    v.IsReal := by
  rw [Subsingleton.elim v Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

noncomputable def rationalPositiveArchimedeanLocalComponent
    (v : InfinitePlace ℚ) :
    ℝ≥0ˣ →* v.Completionˣ :=
  (Units.mapEquiv
      (InfinitePlace.Completion.ringEquivRealOfIsReal
        (rationalInfinitePlace_isReal v)).symm.toMulEquiv).toMonoidHom.comp
    (Units.map NNReal.toRealHom.toMonoidHom)

/-!
## Assembly in the finite-Galois inverse limit

The following construction is the global analogue of LCFT's
`residueFrobeniusToLimit`: its coordinates are the actual finite global
Artin homomorphisms, and compatibility is restriction in a finite
abelian tower.
-/

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlace
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

local instance instFactPrimeValNat_solutions (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicLocalization
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Localized rational cyclotomic levels

This file identifies the algebraic localization of an actual finite
rational cyclotomic level with a cyclotomic extension of the completed
base.  The primitive root is the image of a genuine primitive root in
the global level under the canonical global-to-local map.
-/

open scoped NumberField
open NumberField IsDedekindDomain
open LocalClassFieldTheory

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- The finite adic absolute value of the rational base at `v`. -/
abbrev rationalCyclotomicAdicAbsoluteValue
    (v : HeightOneSpectrum (𝓞 ℚ)) :=
  HeightOneSpectrum.adicAbv ℚ v

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalPrimeFactorization
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Prime factorization of a nonzero rational number

This file records the elementary rational factorization needed for the
principal-idele calculation over `ℚ`.  At a fixed rational prime `p`, removing
the `p`-power from `x : ℚˣ` leaves the sign of `x` times the finite product of
the powers of all primes different from `p`.

The last declarations package rational `p`-adic units as units of `ℤ_[p]` and
identify the reduction of a natural unit modulo `p ^ k`.
-/

open scoped BigOperators Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance localInst_rda254e_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
/-- A nonzero rational number of `p`-adic valuation zero, regarded as a
unit of the `p`-adic integers. -/
def padicIntUnitOfRat
    (p : Nat.Primes) (y : ℚ)
    (hy : y ≠ 0) (hval : padicValRat p.1 y = 0) :
    ℤ_[p.1]ˣ :=
  PadicInt.mkUnits (u := (y : ℚ_[p.1])) (by
    rw [Padic.eq_padicNorm,
      padicNorm.eq_zpow_of_nonzero hy, hval]
    simp)

/-- The underlying `p`-adic number of `padicIntUnitOfRat` is the original
rational number. -/
@[simp]
theorem padicIntUnitOfRat_coe
    (p : Nat.Primes) (y : ℚ)
    (hy : y ≠ 0) (hval : padicValRat p.1 y = 0) :
    (((padicIntUnitOfRat p y hy hval : ℤ_[p.1]) : ℚ_[p.1])) =
      (y : ℚ_[p.1]) := by
  exact PadicInt.mkUnits_eq _

/-- The sign of a nonzero rational numerator is a unit at every finite
prime. -/
theorem padicValRat_rational_num_sign
    (x : ℚˣ) (p : Nat.Primes) :
    padicValRat p.1 ((((x : ℚ).num.sign : ℤ) : ℚ)) = 0 := by
  have hnum : (x : ℚ).num ≠ 0 :=
    Rat.num_ne_zero.mpr x.ne_zero
  rcases lt_or_gt_of_ne hnum with hneg | hpos
  · have hsign : (x : ℚ).num.sign = -1 := by
      rw [Int.sign_eq_sign, sign_neg hneg]
      rfl
    rw [hsign]
    simp
  · have hsign : (x : ℚ).num.sign = 1 := by
      rw [Int.sign_eq_sign, sign_pos hpos]
      rfl
    rw [hsign]
    simp

/-- The actual sign of `x`, regarded as a unit of the `p`-adic integers. -/
def rationalSignPadicUnit
    (x : ℚˣ) (p : Nat.Primes) : ℤ_[p.1]ˣ :=
  padicIntUnitOfRat p ((((x : ℚ).num.sign : ℤ) : ℚ))
    (by
      exact_mod_cast
        (Int.sign_eq_zero_iff_zero.not.mpr
          (Rat.num_ne_zero.mpr x.ne_zero)))
    (padicValRat_rational_num_sign x p)

/-- The underlying `p`-adic number of `rationalSignPadicUnit` is the sign of
the rational numerator. -/
@[simp]
theorem rationalSignPadicUnit_coe
    (x : ℚˣ) (p : Nat.Primes) :
    (((rationalSignPadicUnit x p : ℤ_[p.1]) : ℚ_[p.1])) =
      (((((x : ℚ).num.sign : ℤ) : ℚ) : ℚ_[p.1])) := by
  exact padicIntUnitOfRat_coe _ _ _ _

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField

local instance instFactPrimeValNat_solutions_2 (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩

local instance instNeZeroNatVal_solutions (m : ℕ+) : NeZero (m : ℕ) :=
  ⟨m.ne_zero⟩

/-! Named compatibility witnesses used by the ramified-prime and ray-norm
modules.  They are not installed as a duplicate module-level instance family;
the canonical instances above already provide the same data. -/

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalAwayProduct
attribute [-instance] _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

local instance instFactPrimeValNat_solutions_3 (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

local instance instFactPrimeValNat_solutions_5 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicAbstractFixedFieldArtin
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Cyclotomic Artin coordinates over abstract fixed fields

The cyclotomic degree datum on the rational absolute Galois group has
an actual maximal-unramified field over every finite abstract fixed
field.  This file identifies its genuine Galois group with
`Multiplicative ZHat`, using the normalized degree map, and supplies
the abelian Galois structure needed by the actual infinite global
Artin homomorphism.

These constructions are the source side of the comparison between
abstract finite reciprocity and the chosen local-factor product.  No
reciprocity comparison is assumed in their definitions.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory

/-- Keep this module on the rational algebra structures used by the
cyclotomic fixed-field API.  Generic intermediate-field instances are
propositionally equal here but not definitionally interchangeable. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtin_separableClosureAlgebra :
    Algebra ℚ (SeparableClosure ℚ) :=
  DivisionRing.toRatAlgebra

end Reciprocity
end GlobalClassFieldTheory
end
end


