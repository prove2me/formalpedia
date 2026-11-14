-- Prove2me | Definitions.Def_OAIQ244Duke021
-- name    : OAIQ244Duke021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:19:26.968034+00:00
-- url     : https://prove2.me/theorems/5bc9f5e3-d6af-4fb2-90a0-bb9d7d416ef3
-- title:
--   Definitions bundle OAIQ244Duke021 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 139 declarations of OpenAI's Lean: 37 definitions, 8 instances and 94 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.RationalCyclotomicPrincipalPrimeCompletion`, `GlobalClassFieldTheory.Reciprocity.chosenInfinitePlaceArtinMonoidHom`, `GlobalClassFieldTheory.Reciprocity.finitePlaceArtinCompletionValuativeRel`, `GlobalClassFieldTheory.Reciprocity.finitePlaceArtinCompletionValued`, `GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel`, `GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinInput`, `GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinInputMonoidHom`, `GlobalClassFieldTheory.Reciprocity.finitePlaceNormUpperValuativeRel`, `GlobalClassFieldTheory.Reciprocity.infinitePlaceArtinMonoidHomOfPlace`, `GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield`, `GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfieldEmbedding`, `GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfieldRationalAlgebra`, `GlobalClassFieldTheory.Reciprocity.padicNatUnit`, `GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicOrder`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinBaseAbv`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinPlace`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelPrimitiveRoot`, `GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseNontriviallyNormedField`, `GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRel`, `GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValued`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeFactorCompletionNontriviallyNormedField`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeFactorCompletionValuativeRel`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeFactorCompletionValued`, `LocalFieldTheory.Padic.padicIntValuationSubringContinuousMulEquiv`, `RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension`, `RamificationTheory.HilbertRamification.Higher.dvfHigherPrincipalUnitGroup`, `RamificationTheory.HilbertRamification.Higher.dvfPrincipalUnitGradedPiece`, `RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut`, `RamificationTheory.HilbertRamification.Higher.integralOrbitPolynomial`, `RamificationTheory.HilbertRamification.Higher.lowerRamificationGradedPiece`, `RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup`, `RamificationTheory.HilbertRamification.Higher.realRamificationExponent`, `RamificationTheory.HilbertRamification.Higher.realRamificationIdeal`, `RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension`, `RamificationTheory.HilbertRamification.Higher.valuationSubringDisplacementSubalgebraOfUniqueExtension`, `finiteNormalClosureOriginalField`, `finiteNormalClosureOriginalFieldEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_Extension_EmbeddingNorm`, `AlgebraicNumberTheory_Idele_Topology`, `AlgebraicNumberTheory_NormalClosure`, `AlgebraicNumberTheory_Ramification_Splitting_FinitePlaceIdeal`, `AlgebraicNumberTheory_SUnit_Herbrand`, `AlgebraicNumberTheory_SUnit_LogLattice`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Construction`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`, `GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlace`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicLocalization`, `GlobalClassFieldTheory_Reciprocity_RationalPrimeFactorization`, `GlobalClassFieldTheory_Reciprocity_TopologicalGlobalNormResidueAbelianization`, `KummerTheory_Concrete_CyclotomicPrimeBaseChange`, `Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_DenseTorsion`, `LocalField_DiscreteValuationField_PadicField`, `LocalField_NonarchimedeanLocalField_FiniteExtensionTopology`, `LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients`, `LocalField_NonarchimedeanLocalField_ResidueExtension`, `LocalField_NonarchimedeanLocalField_UnramifiedFrobenius`, `LocalField_Padic_NonarchimedeanLocalField`, `LocalField_Padic_UnitDecomposition`, `PrimePackets_LeafNormalization`, `Ramification_Different`, `Ramification_HilbertRamification_CompleteDVF`, `Ramification_HilbertRamification_DecompositionGroup`, `Ramification_HilbertRamification_Monogeneity`, `Ramification_HilbertRamification_RamificationNumber`, `Ramification_HilbertRamification_RealLowerGroups`, `Ramification_HilbertRamification_UniformizerGradedHom`, `Ramification_HilbertRamification_UniqueExtensionIntegralClosure`, `Valuation_DiscreteValuationField_Basic`, `Valuation_DiscreteValuationField_ValuationExtension`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke000`, `OAIQ244Duke001`, `OAIQ244Duke002`, `OAIQ244Duke003`, `OAIQ244Duke004`, `OAIQ244Duke005`, `OAIQ244Duke006`, `OAIQ244Duke007`, `OAIQ244Duke008`, `OAIQ244Duke009`, `OAIQ244Duke010` and `OAIQ244Duke011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke027`, `OAIQ244Duke031`, `OAIQ244Duke033`, `OAIQ244Duke034`, `OAIQ244Duke035` and `OAIQ244Duke036`.
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
import Definitions.Def_OAIQ244Duke000
import Definitions.Def_OAIQ244Duke001
import Definitions.Def_OAIQ244Duke002
import Definitions.Def_OAIQ244Duke003
import Definitions.Def_OAIQ244Duke004
import Definitions.Def_OAIQ244Duke005
import Definitions.Def_OAIQ244Duke006
import Definitions.Def_OAIQ244Duke007
import Definitions.Def_OAIQ244Duke008
import Definitions.Def_OAIQ244Duke009
import Definitions.Def_OAIQ244Duke010
import Definitions.Def_OAIQ244Duke011

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_EmbeddingNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms through an ambient Galois extension

This file proves the embedded-subextension determinant-norm formula.
If `L/K` is embedded in a finite Galois extension `M/K`, extending the
determinant norm of an element of `A ⊗[K] L` to `A ⊗[K] M` gives the
product over all `K`-embeddings `L → M`.
-/

open scoped BigOperators TensorProduct
open NumberField

noncomputable section

namespace RelativeIdeleGroup

universe u v w z

section UniversalPolynomial

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M]

/-- The determinant-norm polynomial becomes the product of all embeddings
after extending coefficients to the ambient Galois field. -/
theorem map_normPolynomial_eq_embeddingProductPolynomial
    [Infinite K]
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) :
    MvPolynomial.map (algebraMap K M)
        (normPolynomial b) =
      embeddingProductPolynomial (M := M) b := by
  apply MvPolynomial.funext_set
    (fun _ : ι ↦ Set.range (algebraMap K M))
  · intro i
    exact Set.infinite_range_of_injective
      (algebraMap K M).injective
  · intro c hc
    choose d hd using fun i ↦
      hc i (Set.mem_univ i)
    let x : L :=
      b.repr.symm (Finsupp.equivFunOnFinite.symm d)
    have hcoords :
        c = fun i ↦
          algebraMap K M (b.repr x i) := by
      funext i
      calc
        c i = algebraMap K M (d i) :=
          (hd i).symm
        _ = algebraMap K M (b.repr x i) := by
          simp [x]
    rw [hcoords, eval_embeddingProductPolynomial]
    rw [MvPolynomial.eval_map]
    change MvPolynomial.eval₂ (algebraMap K M)
        ((algebraMap K M) ∘
          fun i ↦ b.repr x i)
        (normPolynomial b) =
      _
    rw [← MvPolynomial.eval₂_comp]
    rw [eval_normPolynomial]
    exact
      norm_eq_prod_embeddings_in_galoisExtension x

omit [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M] in
/-- Evaluation of an embedding polynomial after arbitrary scalar extension
is the corresponding tensor-algebra embedding. -/
theorem eval₂_embeddingPolynomial_baseChange
    (A : Type*) [CommRing A] [Algebra K A]
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (f : L →ₐ[K] M)
    (x : A ⊗[K] L) :
    MvPolynomial.eval₂
        ((Algebra.TensorProduct.includeRight
          (R := K) (A := A) (B := M)).toRingHom)
        (fun i ↦
          (Algebra.TensorProduct.includeLeft
            (R := K) (S := K) (A := A) (B := M))
            ((Algebra.TensorProduct.basis A b).repr x i))
        (embeddingPolynomial b f) =
      scalarEmbedding A f x := by
  simp only [embeddingPolynomial,
    MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_C]
  calc
    ∑ i,
        (Algebra.TensorProduct.includeLeft
          (R := K) (S := K) (A := A) (B := M))
          ((Algebra.TensorProduct.basis A b).repr x i) *
        (Algebra.TensorProduct.includeRight
          (R := K) (A := A) (B := M))
          (f (b i)) =
      ∑ i, scalarEmbedding A f
        (((Algebra.TensorProduct.basis A b).repr x i) •
          Algebra.TensorProduct.basis A b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Algebra.TensorProduct.basis_apply,
          Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.smul_def]
    _ = scalarEmbedding A f
        (∑ i,
          ((Algebra.TensorProduct.basis A b).repr x i) •
            Algebra.TensorProduct.basis A b i) := by
      rw [map_sum]
    _ = scalarEmbedding A f x := by
      rw [(Algebra.TensorProduct.basis A b).sum_repr]

end UniversalPolynomial

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Topology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The idele topology

The idele group `I_K` carries the restricted-product topology. This file records
the topological-group structure and the continuity of every local
component map.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

instance finiteLocalUnitsOpen :
    Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen
        ((v.adicCompletionIntegers K).units :
          Set (v.adicCompletion K)ˣ)) :=
  ⟨isOpen_finiteLocalUnits K⟩

instance finiteIdeleGroupIsTopologicalGroup :
    IsTopologicalGroup (FiniteIdeleGroup K) :=
  inferInstance

instance ideleGroupIsTopologicalGroup :
    IsTopologicalGroup (IdeleGroup K) :=
  inferInstance
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_NormalClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

/-- The distinguished copy of `L` in its finite normal closure. -/
noncomputable def finiteNormalClosureOriginalField :
    IntermediateField K (finiteNormalClosure K L) :=
  (finiteNormalClosureEmbedding K L).fieldRange

/-- The original extension is canonically equivalent to its
distinguished copy in the finite normal closure. -/
noncomputable def finiteNormalClosureOriginalFieldEquiv :
    L ≃ₐ[K] finiteNormalClosureOriginalField K L :=
  (finiteNormalClosureEmbedding K L).equivFieldRange

/-- The distinguished copy of `L` generates its finite normal closure
under its `K`-conjugates. -/
theorem finiteNormalClosureOriginalField_normalClosure_eq_top :
    IntermediateField.normalClosure K
        (finiteNormalClosureOriginalField K L)
        (finiteNormalClosure K L) =
      ⊤ := by
  let : Nonempty (L →ₐ[K] AlgebraicClosure K) :=
    ⟨IsAlgClosed.lift⟩
  have hAbstract :
      IntermediateField.normalClosure K L
          (finiteNormalClosure K L) =
        ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp
      (show IsNormalClosure K L
          (finiteNormalClosure K L) from inferInstance)).2
  exact
    normalClosure_eq_top_of_source_algEquiv
      (K := K) (L := L)
      (finiteNormalClosureOriginalFieldEquiv K L)
      hAbstract

/-- The degree of the original extension is bounded by the degree of
its finite normal closure. -/
theorem finrank_le_finiteNormalClosure :
    Module.finrank K L ≤
      Module.finrank K (finiteNormalClosure K L) := by
  exact
    (finiteNormalClosureEmbedding K L).toLinearMap
      |>.finrank_le_finrank_of_injective
        (finiteNormalClosureEmbedding K L).injective
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_PrincipalUnitQuotients
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsConcreteEquiv_mk _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsLift_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Successive principal-unit quotients

Develops `U^n/U^(n+1)` and identifies it with the additive ideal quotient
`𝓂^n/𝓂^(n+1)` through the first-order map `a ↦ 1 + a`.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open Filter

/-! ### Separatedness of the principal-unit filtration -/

/-- The principal-unit filtration is separated: a unit lying in every `U^n`
is the unit `1`. -/
theorem principalUnits_eq_one_of_mem_all
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (u : 𝒪[K]ˣ)
    (hu : ∀ n : Nat, u ∈ principalUnits K n) :
    u = 1 := by
  apply Units.ext
  have hsub :
      ((u : 𝒪[K]) - 1) = 0 :=
    eq_zero_of_mem_all_maximalIdeal_pow K ((u : 𝒪[K]) - 1) (by
      intro n
      exact (mem_principalUnits_iff K u n).1 (hu n))
  exact sub_eq_zero.mp hsub

/-! ### Maximal-ideal powers as local neighborhoods -/

/-- If a sequence of valuation integers converges, then its difference from
the limit is eventually in any fixed power of the maximal ideal. -/
theorem eventually_sub_mem_maximalIdeal_pow_of_tendsto
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] {f : Nat → 𝒪[K]} {x : 𝒪[K]} (n : Nat)
    (hf : Tendsto f atTop (nhds x)) :
    ∀ᶠ d in atTop, f d - x ∈ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  have hdiff : Tendsto (fun d : Nat => f d - x) atTop (nhds (0 : 𝒪[K])) := by
    simpa using hf.sub (tendsto_const_nhds (x := x))
  exact hdiff.eventually (maximalIdeal_pow_mem_nhds_zero K n)

/-- If valuation-ring units converge in the valuation integer ring, then their
quotient by the limit is eventually in every fixed principal-unit level. -/
theorem eventually_div_mem_principalUnits_of_tendsto_units
    (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K] {f : Nat → 𝒪[K]ˣ} {x : 𝒪[K]ˣ} (n : Nat)
    (hf : Tendsto (fun d : Nat => ((f d : 𝒪[K]ˣ) : 𝒪[K])) atTop
      (nhds ((x : 𝒪[K]ˣ) : 𝒪[K]))) :
    ∀ᶠ d in atTop, f d / x ∈ principalUnits K n := by
  have hsub := eventually_sub_mem_maximalIdeal_pow_of_tendsto K n hf
  filter_upwards [hsub] with d hd
  rw [mem_principalUnits_iff]
  change (((f d / x : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])
  rw [show (((f d / x : 𝒪[K]ˣ) : 𝒪[K]) - 1) =
      (((f d : 𝒪[K]ˣ) : 𝒪[K]) - ((x : 𝒪[K]ˣ) : 𝒪[K])) * ↑(x⁻¹) by
    simp only [div_eq_mul_inv, Units.val_mul]
    calc
      ((f d : 𝒪[K]ˣ) : 𝒪[K]) * ↑(x⁻¹) - 1 =
          ((f d : 𝒪[K]ˣ) : 𝒪[K]) * ↑(x⁻¹) -
            ((x : 𝒪[K]ˣ) : 𝒪[K]) * ↑(x⁻¹) := by
            simp
      _ = (((f d : 𝒪[K]ˣ) : 𝒪[K]) - ((x : 𝒪[K]ˣ) : 𝒪[K])) * ↑(x⁻¹) := by
            ring]
  exact (𝓂[K] ^ n : Ideal 𝒪[K]).mul_mem_right _ hd

/-! ### Finite correction products for complete lifting -/

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ResidueExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Residue extensions

Constructs the maps induced on valuation rings, residue fields, and residue
units by a valued extension, with degree, trace, norm, and Frobenius results.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The trace map for the canonical residue-field extension supplied by a
valuation extension is surjective. -/
theorem residueField_trace_surjective_of_valuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Function.Surjective (Algebra.trace 𝓀[K] 𝓀[L]) := by
  let : Algebra.IsSeparable 𝓀[K] 𝓀[L] :=
    residueFieldAlgebra_isSeparable_of_valuationExtension K L
  exact Algebra.trace_surjective 𝓀[K] 𝓀[L]

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Discretely valued fields

This is the basic one-dimensional API for fields equipped with a chosen
rank-one discrete valuation.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

namespace DVF

variable {K : Type u} [Field K]

/-- The valuation ring of a DVF is a fraction ring inside the field. -/
theorem valuationSubring_isFractionRing (F : DVF.{u, v} K) :
    IsFractionRing F.valuationSubring K :=
  (Valuation.valuationSubring.integers (v := F.valuation)).isFractionRing

/-- The valuation ring of a DVF is integrally closed. -/
theorem valuationSubring_isIntegrallyClosed (F : DVF.{u, v} K) :
    IsIntegrallyClosed F.valuationSubring := by
  change IsIntegrallyClosed F.valuation.valuationSubring
  infer_instance

/-- Zero residue is equivalent to membership in the maximal ideal. -/
theorem residue_eq_zero_iff (F : DVF.{u, v} K)
    (x : F.valuationSubring) :
    F.residueMap x = 0 ↔ x ∈ F.maximalIdeal := by
  change
    IsLocalRing.residue F.valuation.valuationSubring x = 0 ↔
    x ∈ IsLocalRing.maximalIdeal F.valuation.valuationSubring
  exact IsLocalRing.residue_eq_zero_iff x

/-! ### Successive quotients of powers of the maximal ideal -/

end DVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_ValuationExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Valuation extensions

Mathlib's uniqueness criterion for valuations is expressed through
`Valuation.IsEquiv`: two valuations on the same field are equivalent exactly
when they have the same valuation subring.  The results here use the ambient
valued-extension property directly; no marker object is introduced.
-/

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

section LocalValuationSubringMap

variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)

/-- A local map between the valuation rings, whose map on fraction fields is
the given algebra map, determines an extension of valuations.

The locality hypothesis is the essential point: if an element of the base
field is not integral, its inverse lies in the maximal ideal.  Locality sends
that inverse into the target maximal ideal, so the image of the original
element cannot be integral. -/
theorem valuation_hasExtension_of_local_valuationSubring_map
    (f : base.valuationSubring →+* target.valuationSubring)
    [IsLocalHom f]
    (hcoe : ∀ z : base.valuationSubring,
      ((f z : target.valuationSubring) : L) =
        algebraMap K L (z : K)) :
    base.valuation.HasExtension target.valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext z
  change
    algebraMap K L z ∈ target.valuation.valuationSubring ↔
      z ∈ base.valuation.valuationSubring
  constructor
  · intro hzTarget
    by_contra hzBase
    have hz_ne : z ≠ 0 := by
      intro hz
      subst z
      exact hzBase base.valuation.valuationSubring.zero_mem
    have hinvNonunit :
        z⁻¹ ∈ base.valuation.valuationSubring.nonunits :=
      (base.valuation.valuationSubring.inv_mem_nonunits_iff).2
        (Or.inr hzBase)
    let zinverse : base.valuationSubring :=
      ⟨z⁻¹,
        base.valuation.valuationSubring.nonunits_subset hinvNonunit⟩
    have hzinverseMaximal :
        zinverse ∈ IsLocalRing.maximalIdeal base.valuationSubring := by
      apply
        base.valuation.valuationSubring.coe_mem_nonunits_iff.mp
      exact hinvNonunit
    have hmapMaximal :
        f zinverse ∈ IsLocalRing.maximalIdeal target.valuationSubring :=
      map_nonunit f zinverse hzinverseMaximal
    let ztarget : target.valuationSubring :=
      ⟨algebraMap K L z, hzTarget⟩
    have hproduct : f zinverse * ztarget = 1 := by
      apply Subtype.ext
      change
        ((f zinverse : target.valuationSubring) : L) *
            algebraMap K L z =
          1
      rw [hcoe]
      change algebraMap K L (z⁻¹) * algebraMap K L z = 1
      rw [← map_mul, inv_mul_cancel₀ hz_ne, map_one]
    have hone :
        (1 : target.valuationSubring) ∈
          IsLocalRing.maximalIdeal target.valuationSubring := by
      rw [← hproduct]
      exact
        (IsLocalRing.maximalIdeal target.valuationSubring).mul_mem_right
          ztarget hmapMaximal
    exact
      (IsLocalRing.maximalIdeal.isMaximal target.valuationSubring).isPrime.one_notMem
        hone
  · intro hzBase
    let zbase : base.valuationSubring := ⟨z, hzBase⟩
    have hzMap :
        ((f zbase : target.valuationSubring) : L) ∈
          target.valuation.valuationSubring :=
      (f zbase).property
    rwa [hcoe] at hzMap

/-- An equivalence of valuation subrings whose underlying field map is the
given algebra map determines an extension of valuations.  Surjectivity makes
the induced ring homomorphism local, so this is the source-producing
equivalence form of
`valuation_hasExtension_of_local_valuationSubring_map`. -/
theorem valuation_hasExtension_of_valuationSubring_equiv
    (e : base.valuationSubring ≃+* target.valuationSubring)
    (hcoe : ∀ z : base.valuationSubring,
      ((e z : target.valuationSubring) : L) =
        algebraMap K L (z : K)) :
    base.valuation.HasExtension target.valuation := by
  let : IsLocalHom e.toRingHom :=
    IsLocalHom.of_surjective e.toRingHom e.surjective
  exact
    valuation_hasExtension_of_local_valuationSubring_map
      base target e.toRingHom hcoe

end LocalValuationSubringMap

end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_DecompositionGroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition-group restriction law

This file gives the three tower-intersection formulas in their common ambient
Galois group.  The decomposition-group statement is formulated for arbitrary
absolute values, including the archimedean case.  The inertia and ramification
statements use valuation subrings and therefore cover the nonarchimedean case
in which those groups are defined.
-/

noncomputable section

universe u v w

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations
open RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type u) {L : Type w} [Field K] [Field L] [Algebra K L]

section IntermediateField

variable {M : Type v} [Field M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L]

/-- The decomposition-group restriction law, decomposition-group membership form: scalar restriction
does not change the action on the chosen valuation of `L`. -/
theorem decompositionGroupRestriction_mem_absoluteValueDecompositionGroup_restrictScalars_iff
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[M] L) :
    RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars (K := K) (M := M) σ ∈
        absoluteValueDecompositionGroup K w ↔
      σ ∈ absoluteValueDecompositionGroup M w :=
  Iff.rfl

end IntermediateField

end HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_LogLattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The logarithmic lattice of `S`-units

This file develops the logarithmic lattice of `S`-units. The
finite set `S` consists of the finite places; all infinite places are
understood to belong to the set of places used in the theorem.

The first construction uses the usual reduced archimedean logarithmic
space (one infinite coordinate is omitted) together with the integral
principal-divisor coordinates at `S`.  Its image is proved directly to
be a complete `ℤ`-lattice.  The normalized, all-place logarithmic map
and its coordinate-sum-zero hyperplane are constructed below from this
lattice.
-/

noncomputable section

open IsDedekindDomain Module
open scoped Classical NumberField nonZeroDivisors


variable {K : Type*} [Field K] [NumberField K]

namespace SUnitGroup

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- A reduced logarithmic vector in the lattice vanishes when all of its
finite coordinates have norm less than one. -/
theorem norm_reducedLog_finite_lt_one_implies_zero
    {x : Additive (SUnitGroup (K := K) S)}
    (hx :
      ‖reducedLog (K := K) S x‖ < 1) :
    (reducedLog (K := K) S x).2 = 0 := by
  ext v
  have hv :
      ‖(reducedLog (K := K) S x).2 v‖ < 1 := by
    exact
      (norm_le_pi_norm _ v).trans_lt
        ((norm_snd_le
          (reducedLog (K := K) S x)).trans_lt hx)
  change
    (divisorCoordinate (K := K) S
      (Additive.toMul x) v : ℝ) = 0
  change
    |(divisorCoordinate (K := K) S
      (Additive.toMul x) v : ℝ)| < 1 at hv
  rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at hv
  exact_mod_cast Int.abs_lt_one_iff.mp hv

/-- The reduced logarithmic space has dimension equal to the Dirichlet
unit rank plus the number of finite places in `S`. -/
theorem finrank_reducedLogSpace :
    Module.finrank ℝ (ReducedLogSpace (K := K) S) =
      NumberField.Units.rank K + S.card := by
  classical
  simp [NumberField.Units.rank]

end SUnitGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_FinitePlaceIdeal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place splitting through prime ideals

For a finite Galois extension of number fields, an exact extension of a
normalized finite absolute value and its centre prime ideal have the same
decomposition group.  This file makes that comparison independent of the
chosen extension and records the finiteness of the fibres of contraction.
These are the place-theoretic ingredients used in the cyclic prime-power and
normal-closure splitting reductions.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section IntermediateField

variable {M : Type}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]
    [IsGalois M L]

omit [NumberField K] [NumberField M] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L] [IsGalois M L] in
/-- Restricting the scalars of a Galois automorphism does not change
its action on the finite primes of the top field. -/
theorem finitePlaceEquiv_restrictAutomorphismScalars
    (σ : L ≃ₐ[M] L)
    (W : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv K L
        (RamificationTheory.HilbertRamification.ValuationSubring.restrictAutomorphismScalars
          (K := K) (M := M) σ) W =
      finitePlaceEquiv M L σ W := by
  apply HeightOneSpectrum.ext
  ext x
  rfl

end IntermediateField
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_Herbrand
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The Herbrand quotient of the global S-unit group

This file computes the Herbrand quotient of the global `S`-unit group. It connects the actual
`S`-unit group to its logarithmic lattice, adds the invariant diagonal
integer direction, and combines the resulting exact sequences with the
permutation-lattice calculation.
-/

open scoped BigOperators Classical NumberField nonZeroDivisors Pointwise
open IsDedekindDomain Module

noncomputable section

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section LocalDegreeInterpretation

omit [NumberField K] [NumberField L] in
/-- Stabilizing a finite place is equivalent to stabilizing its
underlying prime ideal. -/
theorem finitePlace_stabilizer_eq_idealStabilizer
    (P : HeightOneSpectrum (𝓞 L)) :
    letI _finitePlaceAction :=
      finitePlaceMulAction K L
    MulAction.stabilizer (L ≃ₐ[K] L) P =
      MulAction.stabilizer (L ≃ₐ[K] L) P.asIdeal := by
  let finitePlaceAction :=
    finitePlaceMulAction K L
  ext σ
  simp only [MulAction.mem_stabilizer_iff]
  change
    finitePlaceEquiv K L σ P = P ↔
      σ • P.asIdeal = P.asIdeal
  rw [HeightOneSpectrum.ext_iff,
    finitePlaceEquiv_asIdeal,
    Ideal.pointwise_smul_def]
  change
    Ideal.map
          (NumberField.RingOfIntegers.mapAlgEquiv
            σ).toRingEquiv.toRingHom P.asIdeal =
        P.asIdeal ↔
      Ideal.map
          (MulSemiringAction.toRingHom
            (L ≃ₐ[K] L) (𝓞 L) σ) P.asIdeal =
        P.asIdeal
  have hhom :
      (NumberField.RingOfIntegers.mapAlgEquiv
          σ).toRingEquiv.toRingHom =
        MulSemiringAction.toRingHom
          (L ≃ₐ[K] L) (𝓞 L) σ := by
    ext x
    rfl
  rw [hhom]

/-- The stabilizer of a finite place has order equal to its local
degree. -/
theorem finitePlace_stabilizer_card_eq_localDegree
    [IsGalois K L]
    (P : HeightOneSpectrum (𝓞 L)) :
    letI _finitePlaceAction :=
      finitePlaceMulAction K L
    Nat.card
        (MulAction.stabilizer (L ≃ₐ[K] L) P) =
      finiteLogPlaceLocalDegree K L P := by
  let finitePlaceAction :=
    finitePlaceMulAction K L
  rw [finitePlace_stabilizer_eq_idealStabilizer K L P]
  unfold finiteLogPlaceLocalDegree
  let p := P.asIdeal.under (𝓞 K)
  have hp : p ≠ ⊥ :=
    Ideal.under_ne_bot (𝓞 K) P.ne_bot
  let quotientFinite : Finite ((𝓞 K) ⧸ p) :=
    Ring.HasFiniteQuotients.finiteQuotient hp
  let residueFinite : Finite p.ResidueField :=
    inferInstance
  let residuePerfect : PerfectField p.ResidueField :=
    inferInstance
  exact
    Ideal.card_stabilizer_eq p P.asIdeal

end LocalDegreeInterpretation
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicField
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The concrete p-adic field `ℚ_[p]`

This file is the first concrete example leaf for the DVF navigation library.
It deliberately uses mathlib's public p-adic objects directly in theorem
statements instead of introducing public aliases for `ℚ_[p]` or its unit group.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField
namespace Examples
namespace Qp

open Filter
open scoped Topology
open scoped WithZero

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

/-- The canonical prime element has normalized value `exp (-1)` for the
chosen DVR valuation on `ℚ_[p]`. -/
theorem padicDVRValuation_apply_p
    (p : ℕ) [Fact p.Prime] :
    padicDVRValuation p (p : ℚ_[p]) =
      WithZero.exp (-1 : ℤ) := by
  change (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]
      (((p : ℤ_[p]) : ℚ_[p])) = WithZero.exp (-1 : ℤ)
  calc
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]
        (((p : ℤ_[p]) : ℚ_[p])) =
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).intValuation
          (p : ℤ_[p]) := by
      simpa using
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation_of_algebraMap
          (K := ℚ_[p]) (p : ℤ_[p])
    _ = WithZero.exp (-1 : ℤ) :=
      IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
        (IsDiscreteValuationRing.maximalIdeal ℤ_[p])
        (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
        PadicInt.maximalIdeal_eq_span_p

/-- The canonical prime element is a uniformizer for the chosen DVR
valuation on `ℚ_[p]`. -/
theorem padicDVRValuation_isUniformizer_p
    (p : ℕ) [Fact p.Prime] :
    (padicDVRValuation p).IsUniformizer (p : ℚ_[p]) :=
  WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
    (padicDVRValuation p) (p : ℚ_[p])
    (padicDVRValuation_apply_p p)

end Qp
end Examples
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_Construction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Construction of finite-place Artin homomorphisms

This module constructs the local Artin map for a chosen extension of a finite place and transports it through the actual decomposition group into the global Galois group.
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
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]

/-- A completion attached to a nonarchimedean absolute value has an ultrametric distance. -/
theorem finitePlaceArtinCompletionIsUltrametricDist
    {F : Type} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    IsUltrametricDist vF.Completion :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
      vF hvF)

/-- The valued-field structure on a finite-place completion induced by its nonarchimedean norm. -/
@[reducible]
noncomputable def finitePlaceArtinCompletionValued
    {F : Type} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    Valued vF.Completion ℝ≥0 :=
  letI : IsUltrametricDist vF.Completion :=
    finitePlaceArtinCompletionIsUltrametricDist vF hvF
  NormedField.toValued

/-- The valuation relation on a finite-place completion induced by its canonical valuation. -/
@[reducible]
noncomputable def finitePlaceArtinCompletionValuativeRel
    {F : Type} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    ValuativeRel vF.Completion := by
  letI : Valued vF.Completion ℝ≥0 :=
    finitePlaceArtinCompletionValued vF hvF
  exact ValuativeRel.ofValuation
    (Valued.v : Valuation vF.Completion ℝ≥0)

/-- The canonical valued structure makes a locally compact finite-place completion a nonarchimedean local field. -/
theorem
    finitePlaceArtinCompletionIsNonarchimedeanLocalField
    {F : Type} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    [IsUltrametricDist vF.Completion]
    [NontriviallyNormedField vF.Completion]
    [(NormedField.valuation
      (K := vF.Completion)).IsNontrivial]
    [LocallyCompactSpace vF.Completion] :
    letI : Valued vF.Completion ℝ≥0 :=
      finitePlaceArtinCompletionValued vF hvF
    letI : ValuativeRel vF.Completion :=
      finitePlaceArtinCompletionValuativeRel vF hvF
    IsNonarchimedeanLocalField vF.Completion := by
  let : Valued vF.Completion ℝ≥0 :=
    finitePlaceArtinCompletionValued vF hvF
  let vC : Valuation vF.Completion ℝ≥0 := Valued.v
  let : vC.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation
        (K := vF.Completion)).IsNontrivial)
  let : ValuativeRel vF.Completion :=
    finitePlaceArtinCompletionValuativeRel vF hvF
  let : vC.Compatible :=
    Valuation.Compatible.ofValuation vC
  let : ValuativeRel.IsNontrivial vF.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vC).2
      inferInstance
  let : IsValuativeTopology vF.Completion :=
    isValuativeTopology_of_valued_ofValuation
      vF.Completion ℝ≥0
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

/-- The canonical completion input used by the finite-place local Artin map. -/
noncomputable def finitePlaceLocalArtinInputMonoidHom
    (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →*
      (NumberField.HeightOneSpectrum.adicAbv K v).Completionˣ :=
  (finitePlaceCompletionUnitsContinuousMulEquiv v).symm.toMonoidHom

/-- Evaluation of the canonical completion input for the finite-place local
Artin map. -/
noncomputable def finitePlaceLocalArtinInput
    (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completionˣ :=
  finitePlaceLocalArtinInputMonoidHom v x

/-- The canonical valuation relation used on a finite-place completion by
the local Artin construction. -/
@[reducible]
noncomputable def finitePlaceLocalArtinCompletionValuativeRel
    (v : HeightOneSpectrum (𝓞 K)) :
    ValuativeRel
      (NumberField.HeightOneSpectrum.adicAbv K v).Completion :=
  finitePlaceArtinCompletionValuativeRel
    (NumberField.HeightOneSpectrum.adicAbv K v)
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)

/-- The canonical nonarchimedean-local-field certificate used on a
finite-place completion by the local Artin construction. -/
theorem
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField
    (v : HeightOneSpectrum (𝓞 K)) :
    @IsNonarchimedeanLocalField
      (NumberField.HeightOneSpectrum.adicAbv K v).Completion
      (inferInstance : Field
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion)
      (finitePlaceLocalArtinCompletionValuativeRel v)
      (inferInstance : TopologicalSpace
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let : NontriviallyNormedField vK.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField
      vK hvK
  let : LocallyCompactSpace vK.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
  let : IsUltrametricDist vK.Completion :=
    finitePlaceArtinCompletionIsUltrametricDist vK hvKna
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceArtinCompletionValued vK hvKna
  let : ValuativeRel vK.Completion :=
    finitePlaceLocalArtinCompletionValuativeRel v
  exact
    finitePlaceArtinCompletionIsNonarchimedeanLocalField
      vK hvKna

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_UnramifiedFrobenius
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Actual unramified Frobenius

The arithmetic Frobenius is first defined as finite-field Frobenius on the
residue extension, then lifted to `Gal(L / K)` through the canonical
residue-action isomorphism for a finite unramified extension.
-/

noncomputable section

universe u

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The arithmetic Frobenius of a finite residue extension raises each residue element to the size
of the base residue field. -/
theorem residueExtensionArithmeticFrobeniusOfValuationExtension_apply
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (x : 𝓀[L]) :
    residueExtensionArithmeticFrobeniusOfValuationExtension K L x =
      x ^ Nat.card 𝓀[K] := by
  let := Fintype.ofFinite 𝓀[K]
  let : Algebra.IsAlgebraic 𝓀[K] 𝓀[L] := inferInstance
  change
    FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L] x =
      x ^ Nat.card 𝓀[K]
  simp [Nat.card_eq_fintype_card]

/-- Two simple roots over a local domain with the same residue are equal. -/
theorem eq_of_simple_roots_of_residue_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {f : Polynomial R} {a b : R}
    (ha : f.IsRoot a) (hb : f.IsRoot b)
    (hres : IsLocalRing.residue R b = IsLocalRing.residue R a)
    (hderiv : IsUnit (f.derivative.eval a)) :
    b = a := by
  let q : Polynomial R := f /ₘ (Polynomial.X - Polynomial.C a)
  have hfactor : (Polynomial.X - Polynomial.C a) * q = f := by
    dsimp [q]
    rw [Polynomial.mul_divByMonic_eq_iff_isRoot]
    exact ha
  have hqEval : q.eval a = f.derivative.eval a := by
    simpa [q] using
      ValuationTheory.DiscreteValuationField.divByMonic_X_sub_C_eval_eq_derivative_eval f a
  have hqUnit : IsUnit (q.eval a) := by
    simpa [hqEval] using hderiv
  have hqResidue :
      IsLocalRing.residue R (q.eval b) =
        IsLocalRing.residue R (q.eval a) := by
    calc
      IsLocalRing.residue R (q.eval b) =
          (q.map (IsLocalRing.residue R)).eval
            (IsLocalRing.residue R b) := by
        exact (Polynomial.eval_map_apply
          (f := IsLocalRing.residue R) (p := q) b).symm
      _ = (q.map (IsLocalRing.residue R)).eval
            (IsLocalRing.residue R a) := by rw [hres]
      _ = IsLocalRing.residue R (q.eval a) := by
        exact Polynomial.eval_map_apply
          (f := IsLocalRing.residue R) (p := q) a
  have hqResidueNe : IsLocalRing.residue R (q.eval b) ≠ 0 := by
    rw [hqResidue]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit (q.eval a)).2 hqUnit
  have hqNe : q.eval b ≠ 0 := by
    intro hzero
    exact hqResidueNe (by rw [hzero, map_zero])
  have hmul : (b - a) * q.eval b = 0 := by
    have hbEval : ((Polynomial.X - Polynomial.C a) * q).eval b = 0 := by
      rw [hfactor]
      exact Polynomial.IsRoot.def.mp hb
    simpa [Polynomial.eval_mul, Polynomial.eval_sub] using hbEval
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hqNe)

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_FiniteExtensionTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

/-- A finite extension with the spectral norm is again a nonarchimedean
local field. -/
theorem finiteExtensionSpectralIsNonarchimedeanLocalField
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    letI : ValuativeRel L := finiteExtensionSpectralValuativeRel K L
    IsNonarchimedeanLocalField L := by
  exact
    (fun (F : Type) [nF : NontriviallyNormedField F] [hUltra : IsUltrametricDist F]
        [hCompact : LocallyCompactSpace F] =>
      letI : Valued F ℝ≥0 := NormedField.toValued
      let vL : Valuation F ℝ≥0 := Valued.v
      letI : ValuativeRel F := ValuativeRel.ofValuation vL
      letI : vL.Compatible := Valuation.Compatible.ofValuation vL
      letI : ValuativeRel.IsNontrivial F :=
        (ValuativeRel.isNontrivial_iff_isNontrivial vL).2
          (inferInstanceAs (NormedField.valuation (K := F)).IsNontrivial)
      letI : IsValuativeTopology F :=
        isValuativeTopology_of_valued_ofValuation F ℝ≥0
      show IsNonarchimedeanLocalField F from
        { toIsValuativeTopology := inferInstance
          toLocallyCompactSpace := hCompact
          toIsNontrivial := inferInstance })
      L (nF := finiteExtensionSpectralNormedField K L)
      (hUltra := finiteExtensionSpectralIsUltrametricDist K L)
      (hCompact := finiteExtensionSpectralLocallyCompactSpace K L)

/-- In a finite tower equipped throughout with the spectral norms over its
local base, the upper spectral valuation extends the intermediate spectral
valuation. -/
theorem finiteExtensionSpectralValuation_hasExtension_of_tower
    (K E L : Type) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    letI : NontriviallyNormedField E :=
      finiteExtensionSpectralNormedField K E
    letI : NontriviallyNormedField L :=
      finiteExtensionSpectralNormedField K L
    letI : ValuativeRel E :=
      finiteExtensionSpectralValuativeRel K E
    letI : ValuativeRel L :=
      finiteExtensionSpectralValuativeRel K L
    Valuation.HasExtension (ValuativeRel.valuation E)
      (ValuativeRel.valuation L) := by
  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K := localFieldIsUltrametricDist K
  apply Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, Valuation.mem_integer_iff]
  have hCompare :=
    (fun (F : Type) [nF : NormedField F] [hUltra : IsUltrametricDist F]
        (y : F) =>
      let v : Valuation F ℝ≥0 := NormedField.valuation (K := F)
      letI : ValuativeRel F := ValuativeRel.ofValuation v
      letI : v.Compatible := Valuation.Compatible.ofValuation v
      (Valuation.vle_one_iff (ValuativeRel.valuation F) (x := y)).symm.trans
        (Valuation.vle_one_iff v (x := y)))
  have hL :=
    hCompare L (nF := (finiteExtensionSpectralNormedField K L).toNormedField)
      (hUltra := finiteExtensionSpectralIsUltrametricDist K L)
      (algebraMap E L x)
  have hE :=
    hCompare E (nF := (finiteExtensionSpectralNormedField K E).toNormedField)
      (hUltra := finiteExtensionSpectralIsUltrametricDist K E) x
  refine hL.trans (Iff.trans ?_ hE.symm)
  change spectralNorm K L (algebraMap E L x) ≤ 1 ↔
    spectralNorm K E x ≤ 1
  rw [(spectralNorm.eq_of_tower (K := K) (E := E) (L := L) x).symm]

end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

section FinitePlaceNormRestrictionInstances

variable {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')

local notation "vKₙ" =>
  NumberField.HeightOneSpectrum.adicAbv K v
local notation "vKₙ'" =>
  NumberField.HeightOneSpectrum.adicAbv K' W
local notation "Cₙ" =>
  finitePlaceNormCompletion K v
local notation "Dₙ" =>
  finitePlaceNormCompletion K' W

local instance finitePlaceNormLowerExtensionAlgebra_ra7f188_1 :
    Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K) w.1
local instance finitePlaceNormLowerCompletionAlgebra_ra7f188_1 :
    Algebra Cₙ w.1.Completion :=
  AbsoluteValue.completionAlgebra vKₙ w.1 w.2
local instance finitePlaceNormUpperExtensionAlgebra_ra7f188_1 :
    Algebra K' w'.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := K') w'.1
local instance finitePlaceNormUpperCompletionAlgebra_ra7f188_1 :
    Algebra Dₙ w'.1.Completion :=
  AbsoluteValue.completionAlgebra vKₙ' w'.1 w'.2
local instance finitePlaceNormLowerNontriviallyNormedField_ra7f188_1 :
    NontriviallyNormedField Cₙ :=
  absoluteValueExtension_completionNontriviallyNormedField
    vKₙ (RayClass.adicAbv_isNontrivial v)
local instance finitePlaceNormLowerLocallyCompactSpace_ra7f188_1 :
    LocallyCompactSpace Cₙ :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry v)
local instance finitePlaceNormUpperNontriviallyNormedField_ra7f188_1 :
    NontriviallyNormedField Dₙ :=
  absoluteValueExtension_completionNontriviallyNormedField
    vKₙ' (RayClass.adicAbv_isNontrivial W)
local instance finitePlaceNormUpperLocallyCompactSpace_ra7f188_1 :
    LocallyCompactSpace Dₙ :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry W)
local instance finitePlaceNormLowerUltrametric_ra7f188_1 :
    IsUltrametricDist Cₙ :=
  finitePlaceArtinCompletionIsUltrametricDist vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValued_ra7f188_1 :
    Valued Cₙ ℝ≥0 :=
  finitePlaceArtinCompletionValued vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValuationNontrivial_ra7f188_1 :
    (Valued.v : Valuation Cₙ ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation (K := Cₙ)).IsNontrivial)
local instance finitePlaceNormLowerValuativeRel_ra7f188_1 :
    ValuativeRel Cₙ :=
  finitePlaceArtinCompletionValuativeRel vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormLowerValuationCompatible_ra7f188_1 :
    (Valued.v : Valuation Cₙ ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation
    (Valued.v : Valuation Cₙ ℝ≥0)
local instance finitePlaceNormLowerValuativeRelNontrivial_ra7f188_1 :
    ValuativeRel.IsNontrivial Cₙ :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation Cₙ ℝ≥0)).2 inferInstance
local instance finitePlaceNormLowerLocalField_ra7f188_1 :
    IsNonarchimedeanLocalField Cₙ :=
  finitePlaceArtinCompletionIsNonarchimedeanLocalField vKₙ
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v)
local instance finitePlaceNormUpperUltrametric :
    IsUltrametricDist Dₙ :=
  finitePlaceArtinCompletionIsUltrametricDist vKₙ'
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W)

local instance finitePlaceNormUpperValued_ra7f188_1 :
    Valued Dₙ ℝ≥0 :=
  finitePlaceArtinCompletionValued vKₙ'
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W)
local instance finitePlaceNormUpperValuationNontrivial_ra7f188_1 :
    (Valued.v : Valuation Dₙ ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation (K := Dₙ)).IsNontrivial)
local instance finitePlaceNormUpperValuativeRel :
    ValuativeRel Dₙ :=
  finitePlaceArtinCompletionValuativeRel vKₙ'
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K' W)

end FinitePlaceNormRestrictionInstances

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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
/-- The height-one prime of `𝓞 ℚ` indexed by `q` lies over the principal
prime ideal `(q)` of `ℤ`. -/
theorem rationalPrime_liesOver_integerSpan
    (q : Nat.Primes) :
    (RayClass.rationalPrime q).asIdeal.LiesOver
      (Ideal.span {(q.1 : ℤ)}) := by
  constructor
  change
    Ideal.span {(q.1 : ℤ)} =
      (RayClass.rationalPrime q).asIdeal.comap
        (algebraMap ℤ (𝓞 ℚ))
  rw [← RayClass.natGenerator_rationalPrime q,
    Rat.HeightOneSpectrum.span_natGenerator]
  have hAlgebraMap :
      (algebraMap ℤ (𝓞 ℚ)) =
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.toRingHom :=
    Subsingleton.elim _ _
  rw [hAlgebraMap]
  exact Ideal.map_comap_of_equiv _

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicLocalization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.rationalCyclotomicCharacterPrimeProduct_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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
open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- A genuine primitive root in the actual `m`-th rational cyclotomic
level. -/
noncomputable def rationalCyclotomicLevelPrimitiveRoot
    (m : ℕ+) : KummerTheory.rationalCyclotomicLevel m :=
  Classical.choose
    (IsCyclotomicExtension.exists_isPrimitiveRoot
      (S := {(m : ℕ)})
      (n := (m : ℕ))
      ℚ (KummerTheory.rationalCyclotomicLevel m)
      (by simp) m.ne_zero)

/-- The selected root in the actual rational cyclotomic level is
primitive of order `m`. -/
theorem rationalCyclotomicLevelPrimitiveRoot_isPrimitiveRoot
    (m : ℕ+) :
    IsPrimitiveRoot (rationalCyclotomicLevelPrimitiveRoot m)
      (m : ℕ) :=
  Classical.choose_spec
    (IsCyclotomicExtension.exists_isPrimitiveRoot
      (S := {(m : ℕ)})
      (n := (m : ℕ))
      ℚ (KummerTheory.rationalCyclotomicLevel m)
      (by simp) m.ne_zero)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalPrimeFactorization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

local instance localInst_ra7f188_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
/-- Removing the `p`-power from a nonzero rational number leaves
`p`-adic valuation zero. -/
@[simp]
theorem padicValRat_rationalPrimeUnit
    (x : ℚˣ) (p : Nat.Primes) :
    padicValRat p.1 (rationalPrimeUnit x p : ℚ) = 0 := by
  have hp0 : (p.1 : ℚ) ≠ 0 := by
    exact_mod_cast p.2.ne_zero
  have hpow0 :
      (p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) ≠ 0 :=
    zpow_ne_zero _ hp0
  rw [rationalPrimeUnit_val,
    padicValRat.mul hpow0 x.ne_zero,
    padicValRat.zpow,
    padicValRat.self p.2.one_lt]
  ring

/-- The value in `ℤ_[p]` of `rationalSignPadicUnit` is the integer sign. -/
@[simp]
theorem rationalSignPadicUnit_val
    (x : ℚˣ) (p : Nat.Primes) :
    (rationalSignPadicUnit x p : ℤ_[p.1]) =
      ((x : ℚ).num.sign : ℤ) := by
  apply Subtype.ext
  simp only [rationalSignPadicUnit_coe, PadicInt.coe_intCast,
    Rat.cast_intCast]

/-- The rational sign unit has square one. -/
@[simp]
theorem rationalSignPadicUnit_sq
    (x : ℚˣ) (p : Nat.Primes) :
    rationalSignPadicUnit x p ^ 2 = 1 := by
  apply Units.ext
  change (rationalSignPadicUnit x p : ℤ_[p.1]) ^ 2 = 1
  rw [rationalSignPadicUnit_val]
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

/-- Reduction of the rational sign unit modulo `p ^ k` has the expected
integer value. -/
@[simp]
theorem rationalSignPadicUnit_toZModPow_val
    (x : ℚˣ) (p : Nat.Primes) (k : ℕ) :
    ((Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) :
          (ZMod (p.1 ^ k))ˣ) : ZMod (p.1 ^ k)) =
      ((x : ℚ).num.sign : ℤ) := by
  change
    PadicInt.toZModPow k
        (rationalSignPadicUnit x p : ℤ_[p.1]) =
      ((x : ℚ).num.sign : ℤ)
  rw [rationalSignPadicUnit_val]
  simp

/-- Reduction of the rational sign unit still has square one. -/
@[simp]
theorem rationalSignPadicUnit_toZModPow_sq
    (x : ℚˣ) (p : Nat.Primes) (k : ℕ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
          (rationalSignPadicUnit x p) ^ 2 =
      1 := by
  rw [← map_pow, rationalSignPadicUnit_sq, map_one]

/-- A natural number prime to `p`, regarded as a unit of `ℤ_[p]`. -/
def padicNatUnit
    (p : Nat.Primes) (q : ℕ) (h : p.1.Coprime q) :
    ℤ_[p.1]ˣ :=
  PadicInt.mkUnits
    (u := (((q : ℤ_[p.1]) : ℚ_[p.1])))
    (by
      simpa using
        (PadicInt.norm_natCast_eq_one_iff (p := p.1)).2 h)

@[simp]
theorem padicNatUnit_val
    (p : Nat.Primes) (q : ℕ) (h : p.1.Coprime q) :
    (padicNatUnit p q h : ℤ_[p.1]) = q := by
  apply Subtype.ext
  rfl

/-- Reducing the canonical `p`-adic unit attached to `q` modulo `p ^ k`
gives the canonical unit represented by `q` in `ZMod (p ^ k)`. -/
@[simp]
theorem padicNatUnit_toZModPow
    (p : Nat.Primes) (q k : ℕ) (h : p.1.Coprime q) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (padicNatUnit p q h) =
      ZMod.unitOfCoprime q (h.symm.pow_right k) := by
  apply Units.ext
  simp

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_CompleteDVF
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instSMulCommClass _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition and inertia for finite extensions of complete DVFs

For a finite separable extension of complete discretely valued fields, the
extension of the base valuation is unique.  Consequently every
base-field automorphism stabilizes the chosen target valuation ring and the
full Galois group is the decomposition group.  Reduction then gives the
finite Galois exact sequence

`1 -> I(L/K) -> Gal(L/K) -> Gal(k_L/k_K) -> 1`.

The valuation-subring definitions and their ordinary exactness are reused
from `HilbertRamification.ValuationSubring`; this file only supplies the
complete-DVF specialization and the finite-Galois surjectivity theorem.
-/

noncomputable section

open scoped Pointwise

universe u v w x

namespace RamificationTheory.HilbertRamification.CompleteDVF

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

instance decompositionGroupMulSemiringAction :
    MulSemiringAction
      (ValuationSubring.decompositionGroup K
        target.valuation.valuationSubring)
      target.valuationSubring := by
  change MulSemiringAction
    (target.valuation.valuationSubring.decompositionSubgroup K)
    target.valuation.valuationSubring
  infer_instance

theorem comapValuation_hasExtension
    (sigma : L ≃ₐ[K] L) :
    base.valuation.HasExtension
      (target.valuation.comap (sigma : L →+* L)) where
  val_isEquiv_comap := by
    rw [_root_.Valuation.isEquiv_iff_val_le_one]
    intro a
    simpa [_root_.Valuation.comap, sigma.commutes a] using
      (_root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := base.valuation) (vA := target.valuation) a).symm

end RamificationTheory.HilbertRamification.CompleteDVF

end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_RealLowerGroups
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Real lower ramification groups

This file gives the intrinsic definitions and the elementary structural
facts in the real lower-ramification definition and the lower-ramification base-change law.  It uses
discretely valued fields, not complete discretely valued fields.  The unique
extension hypothesis is stated for `DVF` itself and is used to derive (rather
than assume) preservation of the chosen valuation ring by the Galois group.

The real index is implemented canonically by the maximal-ideal filtration:
the condition at `s` is membership in `m ^ ceil(s + 1)`.  The exponent is
truncated at zero, so the definition extends harmlessly to every real number
and is the full Galois group for `s <= -1`.
-/

noncomputable section

open scoped Pointwise

universe u v w x y

namespace RamificationTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

namespace DVF

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- Unique extension of a valuation, at the general DVF level.

This is the direct noncomplete analogue of the existing predicates on
`HenselianDVF` and `CompleteDVF`: every valuation of `L` extending the chosen
base valuation is equivalent to the chosen target valuation. -/
def HasUniqueValuationExtension (base : DVF.{u, v} K)
    (target : DVF.{w, x} L) : Prop :=
  ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
      target.valuation.IsEquiv v'

/-- Pulling the target valuation back along a `K`-automorphism again gives an
extension of the base valuation. -/
theorem algEquiv_comap_valuation_hasExtension
    {base : DVF.{u, v} K} {target : DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (σ : L ≃ₐ[K] L) :
    base.valuation.HasExtension (target.valuation.comap (σ : L →+* L)) where
  val_isEquiv_comap := by
    rw [_root_.Valuation.isEquiv_iff_val_le_one]
    intro a
    simpa [_root_.Valuation.comap, σ.commutes a] using
      (_root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := base.valuation) (vA := target.valuation) a).symm

/-- Unique extension makes every `K`-automorphism preserve membership in the
chosen target valuation ring. -/
theorem mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
    {base : DVF.{u, v} K} {target : DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (σ : L ≃ₐ[K] L) (z : L) :
    z ∈ target.valuation.valuationSubring ↔
      σ z ∈ target.valuation.valuationSubring := by
  let vσ := target.valuation.comap (σ : L →+* L)
  let : base.valuation.HasExtension vσ :=
    algEquiv_comap_valuation_hasExtension
      (base := base) (target := target) σ
  have hsub :
      target.valuation.valuationSubring = vσ.valuationSubring :=
    (_root_.Valuation.isEquiv_iff_valuationSubring target.valuation vσ).1
      (huniq vσ)
  change z ∈ target.valuation.valuationSubring ↔ z ∈ vσ.valuationSubring
  rw [hsub]

end DVF
end RamificationTheory.DiscreteValuationField

namespace RamificationTheory.HilbertRamification
namespace Higher

open RamificationTheory.DiscreteValuationField.DVF

open RamificationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- The integral exponent corresponding to a real lower ramification index.

For `s >= -1` this is `ceil (s + 1)`.  The use of `Int.toNat` also makes it
zero for `s <= -1`, which gives the expected constant extension below the
natural indexing range. -/
def realRamificationExponent (s : ℝ) : ℕ :=
  (Int.ceil (s + 1)).toNat

/-- States the theorem `realRamificationExponent_neg_one`. -/
@[simp] theorem realRamificationExponent_neg_one :
    realRamificationExponent (-1) = 0 := by
  simp [realRamificationExponent]

/-- States the theorem `realRamificationExponent_nat`. -/
@[simp] theorem realRamificationExponent_nat (n : ℕ) :
    realRamificationExponent (n : ℝ) = n + 1 := by
  simp [realRamificationExponent]

/-- The maximal-ideal power representing the real lower index `s`. -/
def realRamificationIdeal (target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L)
    (s : ℝ) : Ideal target.valuationSubring :=
  target.maximalIdeal ^ realRamificationExponent s

/-- States the theorem `realRamificationIdeal_neg_one`. -/
@[simp] theorem realRamificationIdeal_neg_one :
    realRamificationIdeal target (-1) = ⊤ := by
  simp [realRamificationIdeal]

/-- States the theorem `realRamificationIdeal_nat`. -/
@[simp] theorem realRamificationIdeal_nat (n : ℕ) :
    realRamificationIdeal target (n : ℝ) = target.maximalIdeal ^ (n + 1) := by
  simp [realRamificationIdeal]

/-- The automorphism induced on the target valuation ring by uniqueness of the
valuation extension. -/
def valuationSubringAutOfUniqueExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) :
    target.valuationSubring ≃+* target.valuationSubring where
  toFun a :=
    ⟨σ (a : L),
      (mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
          (base := base) (target := target) huniq σ (a : L)).1 a.property⟩
  invFun a :=
    ⟨σ⁻¹ (a : L),
      (mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
          (base := base) (target := target) huniq σ⁻¹ (a : L)).1 a.property⟩
  left_inv a := by
    ext
    simp
  right_inv a := by
    ext
    simp
  map_mul' a b := by
    ext
    simp
  map_add' a b := by
    ext
    simp

/-- States the theorem `valuationSubringAutOfUniqueExtension_apply_coe`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_apply_coe
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (a : target.valuationSubring) :
    ((valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ a :
        target.valuationSubring) : L) = σ (a : L) :=
  rfl

/-- States the theorem `valuationSubringAutOfUniqueExtension_one_apply`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_one_apply
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq 1 a = a := by
  ext
  simp

/-- States the theorem `valuationSubringAutOfUniqueExtension_mul_apply`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_mul_apply
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ τ : Gal(L/K)) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq (σ * τ) a =
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq τ a) := by
  ext
  rfl

/-- States the theorem `valuationSubringAutOfUniqueExtension_apply_inv_apply`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_apply_inv_apply
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ⁻¹ a) = a := by
  ext
  simp

/-- A uniquely extended valuation-ring automorphism preserves the maximal
ideal. -/
theorem valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a ∈ target.maximalIdeal ↔
      a ∈ target.maximalIdeal := by
  let e := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq σ
  change e a ∈ target.maximalIdeal ↔ a ∈ target.maximalIdeal
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hea ha
    exact hea (by simpa using ha.map (e : target.valuationSubring →* target.valuationSubring))
  · intro ha hea
    exact ha (by simpa using hea.map (e.symm : target.valuationSubring →* target.valuationSubring))

/-- A uniquely extended valuation-ring automorphism preserves every power of
the maximal ideal. -/
theorem valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (n : ℕ) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a ∈ target.maximalIdeal ^ n ↔
      a ∈ target.maximalIdeal ^ n := by
  let e := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq σ
  have hm :
      Ideal.map (e : target.valuationSubring →+* target.valuationSubring)
          target.maximalIdeal = target.maximalIdeal := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective
      (e : target.valuationSubring →+* target.valuationSubring) e.surjective]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact
        (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff
          (base := base) (target := target) huniq σ b).2 hb
    · intro ha
      refine ⟨e.symm a, ?_, by simp [e]⟩
      exact
        (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff
          (base := base) (target := target) huniq σ (e.symm a)).1
          (by simpa [e] using ha)
  have hmap :
      Ideal.map (e : target.valuationSubring →+* target.valuationSubring)
          (target.maximalIdeal ^ n) = target.maximalIdeal ^ n := by
    rw [Ideal.map_pow, hm]
  constructor
  · intro ha
    rw [← hmap] at ha
    rcases (Ideal.mem_map_iff_of_surjective
      (e : target.valuationSubring →+* target.valuationSubring) e.surjective).1 ha with
      ⟨b, hb, hba⟩
    have : b = a := e.injective hba
    simpa [this] using hb
  · intro ha
    rw [← hmap]
    exact Ideal.mem_map_of_mem
      (e : target.valuationSubring →+* target.valuationSubring) ha

/-- States the theorem `valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff`. -/
theorem valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (s : ℝ) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a ∈
          realRamificationIdeal target s ↔
      a ∈ realRamificationIdeal target s := by
  exact valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff
    (base := base) (target := target) huniq σ
      (realRamificationExponent s) a

/-- The real lower-ramification definition: the real-index lower ramification
group.  On the natural range `s >= -1`, membership is exactly the condition that
all integral displacements have normalized additive value at least `s + 1`,
expressed intrinsically as membership in `m ^ ceil(s + 1)`. -/
def lowerRamificationGroup
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (s : ℝ) : Subgroup Gal(L/K) where
  carrier :=
    {σ | ∀ a : target.valuationSubring,
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a - a ∈
        realRamificationIdeal target s}
  one_mem' := by
    intro a
    simp
  mul_mem' := by
    intro σ τ hσ hτ a
    have hτa :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq τ a - a ∈
          realRamificationIdeal target s :=
      hτ a
    have hmapτa :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq τ a - a) ∈
          realRamificationIdeal target s :=
      (valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff
        (base := base) (target := target) huniq σ s _).2 hτa
    have hσa :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - a ∈
          realRamificationIdeal target s :=
      hσ a
    have hdecomp :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq (σ * τ) a - a =
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ
              (valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq τ a - a) +
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a) := by
      rw [valuationSubringAutOfUniqueExtension_mul_apply, map_sub]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hmapτa hσa
  inv_mem' := by
    intro σ hσ a
    let b := valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ⁻¹ a
    have hb :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ b - b ∈
          realRamificationIdeal target s :=
      hσ b
    have hab : a - b ∈ realRamificationIdeal target s := by
      simpa [b] using hb
    have hba : b - a ∈ realRamificationIdeal target s := by
      simpa [sub_eq_add_neg, add_comm] using
        (realRamificationIdeal target s).neg_mem hab
    simpa [b] using hba

/-- States the theorem `mem_lowerRamificationGroup_iff`. -/
@[simp] theorem mem_lowerRamificationGroup_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (s : ℝ) (σ : Gal(L/K)) :
    σ ∈ lowerRamificationGroup
        (base := base) (target := target) huniq s ↔
      ∀ a : target.valuationSubring,
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - a ∈
          realRamificationIdeal target s :=
  Iff.rfl

/-- At an integral index, the real definition is exactly the usual
`m^(n+1)` displacement condition. -/
theorem mem_lowerRamificationGroup_nat_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (n : ℕ) (σ : Gal(L/K)) :
    σ ∈ lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ) ↔
      ∀ a : target.valuationSubring,
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - a ∈
          target.maximalIdeal ^ (n + 1) := by
  simp only [mem_lowerRamificationGroup_iff, realRamificationIdeal_nat]

/-- The real lower-ramification definition: every real lower ramification group is normal. -/
theorem lowerRamificationGroup_normal
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (s : ℝ) :
    (lowerRamificationGroup
      (base := base) (target := target) huniq s).Normal := by
  refine Subgroup.Normal.mk ?_
  intro σ hσ τ a
  let b := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq τ⁻¹ a
  have hb :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ b - b ∈
        realRamificationIdeal target s :=
    hσ b
  have hmap :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq τ
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ b - b) ∈
        realRamificationIdeal target s :=
    (valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff
      (base := base) (target := target) huniq τ s _).2 hb
  have hrewrite :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq (τ * σ * τ⁻¹) a - a =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq τ
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ b - b) := by
    simp [b, map_sub]
  rwa [hrewrite]

/-- Provides the instance `instNormal`. -/
instance lowerRamificationGroup.instNormal
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (s : ℝ) :
    (lowerRamificationGroup
      (base := base) (target := target) huniq s).Normal :=
  lowerRamificationGroup_normal
    (base := base) (target := target) huniq s

/-- The real lower-ramification definition: `G_{-1}` is the full Galois group. -/
@[simp] theorem lowerRamificationGroup_neg_one
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target) :
    lowerRamificationGroup
      (base := base) (target := target) huniq (-1) = ⊤ := by
  ext σ
  simp [mem_lowerRamificationGroup_iff]

end Higher
end RamificationTheory.HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_UniqueExtensionIntegralClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral closure for a unique discrete valuation extension

This file supplies the noncomplete integral-closure input used in
ramification-number theory.  For a finite Galois extension with a uniquely chosen
extension of the base discrete valuation, the Galois orbit polynomial of an
integer has coefficients in the base valuation ring.  Consequently the target
valuation ring is integral, hence finite, over the base valuation ring.

No completeness or Henselian hypothesis is used.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

open RamificationTheory.DiscreteValuationField.DVF
open ValuationTheory.DiscreteValuationField.Valuation
open scoped Polynomial

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
variable [IsGalois K L]

/-- The full Galois-orbit polynomial of an element of the target valuation
ring.  Uniqueness of the valuation extension makes every factor integral. -/
def integralOrbitPolynomial
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (a : target.valuationSubring) : Polynomial target.valuationSubring := by
  classical
  exact ∏ σ : Gal(L/K),
    (Polynomial.X - Polynomial.C
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a))

omit [IsGalois K L] in
/-- States the theorem `integralOrbitPolynomial_monic`. -/
theorem integralOrbitPolynomial_monic
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (a : target.valuationSubring) :
    (integralOrbitPolynomial
      (base := base) (target := target) huniq a).Monic := by
  classical
  apply Polynomial.monic_prod_of_monic
  intro σ _hσ
  exact Polynomial.monic_X_sub_C _

omit [IsGalois K L] in
/-- The orbit polynomial is invariant under every Galois automorphism. -/
theorem integralOrbitPolynomial_map_valuationSubringAut
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (a : target.valuationSubring) (ρ : Gal(L/K)) :
    (integralOrbitPolynomial
        (base := base) (target := target) huniq a).map
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq ρ).toRingHom =
      integralOrbitPolynomial
        (base := base) (target := target) huniq a := by
  classical
  change
    (∏ σ : Gal(L/K), (Polynomial.X - Polynomial.C
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a))).map
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq ρ).toRingHom =
    ∏ σ : Gal(L/K), (Polynomial.X - Polynomial.C
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a))
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  refine Fintype.prod_equiv (Equiv.mulLeft ρ)
    (fun σ : Gal(L/K) =>
      Polynomial.X - Polynomial.C
        ((valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq ρ).toRingHom
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a)))
    (fun σ : Gal(L/K) =>
      Polynomial.X - Polynomial.C
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a)) ?_
  intro σ
  apply congrArg (fun z : target.valuationSubring =>
    Polynomial.X - Polynomial.C z)
  exact
    (congrFun
      (RingEquiv.coe_toRingHom
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq ρ))
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a)).trans
      (valuationSubringAutOfUniqueExtension_mul_apply
        (base := base) (target := target) huniq ρ σ a).symm

/-- Every coefficient of the integral orbit polynomial descends to the base
valuation ring. -/
theorem integralOrbitPolynomial_coeff_mem_range
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (a : target.valuationSubring) (n : ℕ) :
    (integralOrbitPolynomial
        (base := base) (target := target) huniq a).coeff n ∈
      Set.range (algebraMap base.valuationSubring target.valuationSubring) := by
  let c : target.valuationSubring :=
    (integralOrbitPolynomial
      (base := base) (target := target) huniq a).coeff n
  have hfixed : ∀ σ : Gal(L/K), σ (c : L) = (c : L) := by
    intro σ
    have hmap := congrArg
      (fun p : Polynomial target.valuationSubring => p.coeff n)
      (integralOrbitPolynomial_map_valuationSubringAut
        (base := base) (target := target) huniq a σ)
    simpa [c] using congrArg Subtype.val hmap
  obtain ⟨b, hb⟩ :=
    (IsGalois.mem_range_algebraMap_iff_fixed
      (F := K) (E := L) (c : L)).2 hfixed
  have hbmem : base.valuation b ≤ 1 := by
    apply (_root_.Valuation.HasExtension.val_map_le_one_iff
      (vR := base.valuation) (vA := target.valuation) b).1
    rw [hb]
    exact c.property
  let b0 : base.valuationSubring := ⟨b, hbmem⟩
  refine ⟨b0, ?_⟩
  apply Subtype.ext
  exact hb

/-- Every target integer is integral over the base valuation ring.  The proof
uses its monic Galois-orbit polynomial and coefficient descent. -/
theorem target_valuationSubring_element_isIntegral_of_uniqueExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (a : target.valuationSubring) :
    IsIntegral base.valuationSubring a := by
  let p := integralOrbitPolynomial
    (base := base) (target := target) huniq a
  have hpmonic : p.Monic :=
    integralOrbitPolynomial_monic
      (base := base) (target := target) huniq a
  have hplifts :
      p ∈ Polynomial.lifts
        (algebraMap base.valuationSubring target.valuationSubring) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact integralOrbitPolynomial_coeff_mem_range
      (base := base) (target := target) huniq a n
  rcases Polynomial.lifts_and_natDegree_eq_and_monic hplifts hpmonic with
    ⟨q, hqmap, _hqdeg, hqmonic⟩
  refine ⟨q, hqmonic, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hqmap]
  change
    (integralOrbitPolynomial
      (base := base) (target := target) huniq a).eval a = 0
  classical
  change
    (∏ σ : Gal(L/K), (Polynomial.X - Polynomial.C
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a))).eval a = 0
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : Gal(L/K)))
  simp

/-- The target valuation ring is integral over the base valuation ring under
the standing unique-extension hypotheses of ramification-number theory. -/
theorem target_valuationSubring_isIntegral_of_uniqueExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target) :
    Algebra.IsIntegral base.valuationSubring target.valuationSubring := by
  exact ⟨fun a =>
    target_valuationSubring_element_isIntegral_of_uniqueExtension
      (base := base) (target := target) huniq a⟩

end Higher
end RamificationTheory.HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_Monogeneity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Monogeneity over a noncomplete discretely valued field

This file proves the algebraic, noncomplete form of the monogeneity argument
used in the monogenic integral-generator theorem.  The proof uses the finite integral
closure supplied by unique extension, a primitive residue element, the
representative adjustment , and Nakayama's lemma.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ResidueField
namespace Higher

open scoped Polynomial

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
variable [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Module finiteness of the valuation-ring extension implies finiteness of
the residue-field extension, without completeness. -/
theorem residueField_finiteDimensional_of_moduleFinite_dvf
    [Module.Finite base.valuationSubring target.valuationSubring] :
    FiniteDimensional base.residueField target.residueField := by
  refine FiniteDimensional.of_finrank_pos
    (K := base.residueField) (V := target.residueField) ?_
  let : target.maximalIdeal.LiesOver base.maximalIdeal :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_liesOver_of_hasExtension
      (L := L) base.valuation target.valuation
  change 0 < Module.finrank
    (base.valuationSubring ⧸ base.maximalIdeal)
    (target.valuationSubring ⧸ target.maximalIdeal)
  have h := target.maximalIdeal.inertiaDeg_pos base.valuationSubring
  rw [Ideal.inertiaDeg_eq_of_isMaximal base.maximalIdeal target.maximalIdeal] at h
  exact h

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Reduction after extension of coefficients agrees with extension after
reduction. -/
theorem base_polynomial_lift_target_reduction_eq_dvf
    {P : base.valuationSubring[X]} {fbar : base.residueField[X]}
    (hP : P.map base.residueMap = fbar) :
    (P.map (algebraMap base.valuationSubring target.valuationSubring)).map
        target.residueMap =
      fbar.map (algebraMap base.residueField target.residueField) := by
  rw [← hP]
  ext k
  rw [algebraMap_eq_map_algebraMap]
  simp only [Polynomial.coeff_map]
  exact
    (IsLocalRing.ResidueField.map_residue
      (algebraMap base.valuationSubring target.valuationSubring)
      (P.coeff k)).symm

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A reduced polynomial root is an actual value in the maximal ideal. -/
theorem polynomial_eval_mem_maximalIdeal_of_reduced_eval_eq_zero_dvf
    {P : Polynomial target.valuationSubring} {a : target.valuationSubring}
    (hroot : (P.map target.residueMap).eval (target.residueMap a) = 0) :
    P.eval a ∈ target.maximalIdeal := by
  rw [← target.residue_eq_zero_iff]
  calc
    target.residueMap (P.eval a) =
        (P.map target.residueMap).eval (target.residueMap a) := by
      exact
        (Polynomial.eval_map_apply
          (f := target.residueMap) (p := P) a).symm
    _ = 0 := hroot

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Reducing a base-polynomial evaluation agrees with evaluating the reduced
polynomial at the reduced argument. -/
theorem base_polynomial_aeval_residue_eq_dvf
    (P : base.valuationSubring[X]) (a : target.valuationSubring) :
    target.residueMap (Polynomial.aeval a P) =
      ((P.map base.residueMap).map
        (algebraMap base.residueField target.residueField)).eval
          (target.residueMap a) := by
  calc
    target.residueMap (Polynomial.aeval a P) =
        ((P.map
          (algebraMap base.valuationSubring target.valuationSubring)).map
            target.residueMap).eval (target.residueMap a) := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact
        (Polynomial.eval_map_apply
          (f := target.residueMap)
          (p := P.map
            (algebraMap base.valuationSubring target.valuationSubring))
          a).symm
    _ =
        ((P.map base.residueMap).map
          (algebraMap base.residueField target.residueField)).eval
            (target.residueMap a) := by
      rw [base_polynomial_lift_target_reduction_eq_dvf
        (base := base) (target := target)
        (P := P) (fbar := P.map base.residueMap) rfl]

end Higher
end RamificationTheory.HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_RamificationNumber
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ramification numbers for a general discretely valued field

This file gives the noncomplete version of the ramification number used in
ramification-number theory.  Under the stated unique-extension and
separable-residue hypotheses, the monogenic integral-generator theorem supplies
an integral generator.  We choose that generator internally, so downstream
statements do not carry a generator hypothesis.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher


variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- Elements whose displacement has a fixed maximal-ideal lower bound form a
base valuation-ring subalgebra. -/
def valuationSubringDisplacementSubalgebraOfUniqueExtension
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (n : ℕ) (sigma : Gal(L/K)) :
    Subalgebra base.valuationSubring target.valuationSubring where
  carrier :=
    {a | valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change
      valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma (a + b) - (a + b) ∈
        target.maximalIdeal ^ n
    change valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n at ha
    change valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma b - b ∈
        target.maximalIdeal ^ n at hb
    have hrewrite :
        valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma (a + b) - (a + b) =
          (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma a - a) +
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma b - b) := by
      simp
      ring
    rw [hrewrite]
    exact Ideal.add_mem _ ha hb
  mul_mem' := by
    intro a b ha hb
    change
      valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma (a * b) - a * b ∈
        target.maximalIdeal ^ n
    change valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n at ha
    change valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma b - b ∈
        target.maximalIdeal ^ n at hb
    have hrewrite :
        valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma (a * b) - a * b =
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma a *
              (valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq sigma b - b) +
            (valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq sigma a - a) * b := by
      simp
      ring
    rw [hrewrite]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ hb)
      (Ideal.mul_mem_right _ _ ha)
  algebraMap_mem' := by
    intro r
    change
      valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma
            (algebraMap base.valuationSubring target.valuationSubring r) -
          algebraMap base.valuationSubring target.valuationSubring r ∈
        target.maximalIdeal ^ n
    have hcomm :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma
            (algebraMap base.valuationSubring target.valuationSubring r) =
          algebraMap base.valuationSubring target.valuationSubring r := by
      apply Subtype.ext
      exact sigma.commutes (r : K)
    rw [hcomm, sub_self]
    exact Ideal.zero_mem _

/-- States the theorem `mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff`. -/
@[simp] theorem mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (n : ℕ) (sigma : Gal(L/K)) (a : target.valuationSubring) :
    a ∈ valuationSubringDisplacementSubalgebraOfUniqueExtension
        (base := base) (target := target) huniq n sigma ↔
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n :=
  Iff.rfl

/-- A displacement bound on a generator extends to every integral polynomial
expression in that generator. -/
theorem valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {a z : target.valuationSubring} {n : ℕ} {sigma : Gal(L/K)}
    (ha : valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n)
    (hz : z ∈ Algebra.adjoin base.valuationSubring
      ({a} : Set target.valuationSubring)) :
    valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma z - z ∈
      target.maximalIdeal ^ n := by
  have hle :
      Algebra.adjoin base.valuationSubring ({a} : Set target.valuationSubring) ≤
        valuationSubringDisplacementSubalgebraOfUniqueExtension
          (base := base) (target := target) huniq n sigma := by
    rw [Algebra.adjoin_le_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact ha
  exact hle hz

end Higher
end RamificationTheory.HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_UniformizerGradedHom
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# First ramification-quotient homomorphism over general DVFs

This file constructs the graded uniformizer homomorphism under the standing
hypotheses of ramification-number theory.  Completeness is not assumed.  The
injectivity statement includes the necessary separability hypothesis on the
residue extension; the unconditional printed assertion is false for fiercely
ramified extensions.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

open ValuationTheory.DiscreteValuationField.ResidueField


variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]
variable [IsGalois K L]

/-- The principal-unit filtration attached to a general DVF. -/
def dvfHigherPrincipalUnitGroup
    (target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L) (n : ℕ) :
    Subgroup target.valuationSubringˣ where
  carrier := {a | (a : target.valuationSubring) - 1 ∈ target.maximalIdeal ^ n}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have hre :
        ((a * b : target.valuationSubringˣ) : target.valuationSubring) - 1 =
          (a : target.valuationSubring) *
              ((b : target.valuationSubring) - 1) +
            ((a : target.valuationSubring) - 1) := by
      simp
      ring
    change
      ((a * b : target.valuationSubringˣ) : target.valuationSubring) - 1 ∈
        target.maximalIdeal ^ n
    rw [hre]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ hb) ha
  inv_mem' := by
    intro a ha
    have hre :
        ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) - 1 =
          -(((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) *
            ((a : target.valuationSubring) - 1)) := by
      calc
        ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) - 1 =
            ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) -
              ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) *
                (a : target.valuationSubring) := by simp
        _ = _ := by ring
    change
      ((a⁻¹ : target.valuationSubringˣ) : target.valuationSubring) - 1 ∈
        target.maximalIdeal ^ n
    rw [hre]
    exact (target.maximalIdeal ^ n).neg_mem
      (Ideal.mul_mem_left _ _ ha)

/-- States the theorem `mem_dvfHigherPrincipalUnitGroup_iff`. -/
@[simp] theorem mem_dvfHigherPrincipalUnitGroup_iff
    (target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L)
    (n : ℕ) (a : target.valuationSubringˣ) :
    a ∈ dvfHigherPrincipalUnitGroup target n ↔
      (a : target.valuationSubring) - 1 ∈ target.maximalIdeal ^ n :=
  Iff.rfl

/-- The literal target U_L^n/U_L^(n+1). -/
abbrev dvfPrincipalUnitGradedPiece
    (target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L) (n : ℕ) :=
  dvfHigherPrincipalUnitGroup target n ⧸
    (dvfHigherPrincipalUnitGroup target (n + 1)).subgroupOf
      (dvfHigherPrincipalUnitGroup target n)

/-- The literal source G_n/G_(n+1) formed from the real lower groups. -/
abbrev lowerRamificationGradedPiece
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (n : ℕ) :=
  lowerRamificationGroup
      (base := base) (target := target) huniq (n : ℝ) ⧸
    (lowerRamificationGroup
      (base := base) (target := target) huniq ((n + 1 : ℕ) : ℝ)).subgroupOf
      (lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ))

/-- The unique-extension action on target valuation-ring units. -/
abbrev dvfValuationSubringUnitAut
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (sigma : Gal(L/K)) :
    target.valuationSubringˣ →* target.valuationSubringˣ :=
  Units.map
    (valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma).toMonoidHom

omit [FiniteDimensional K L] [IsGalois K L] in
/-- States the theorem `dvfValuationSubringUnitAut_apply`. -/
@[simp] theorem dvfValuationSubringUnitAut_apply
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (sigma : Gal(L/K)) (a : target.valuationSubringˣ) :
    ((dvfValuationSubringUnitAut
      (base := base) (target := target) huniq sigma a :
        target.valuationSubringˣ) : target.valuationSubring) =
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq sigma
        (a : target.valuationSubring) :=
  rfl

end Higher
end RamificationTheory.HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Padic_NonarchimedeanLocalField
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The p-adic field as a nonarchimedean local field

This file connects Mathlib's normed and valuative structures on `ℚ_p` to
the topology-first local-field interface used by this library.
-/

noncomputable section

open scoped ValuativeRel WithZero

namespace LocalFieldTheory.Padic

variable (p : ℕ) [Fact p.Prime]

/-- The norm-induced valuation on `ℚ_p` is compatible with the canonical
p-adic valuation ordering. -/
theorem normedFieldValuation_compatible_padic :
    (NormedField.valuation : Valuation ℚ_[p] NNReal).Compatible := by
  classical
  constructor
  intro x y
  rw [(Padic.mulValuation (p := p)).vle_iff_le]
  change Padic.mulValuation x ≤ Padic.mulValuation y ↔ ‖x‖₊ ≤ ‖y‖₊
  rw [← NNReal.coe_le_coe]
  change Padic.mulValuation x ≤ Padic.mulValuation y ↔ ‖x‖ ≤ ‖y‖
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy, hx]
  rw [Padic.norm_eq_zpow_neg_valuation hx,
    Padic.norm_eq_zpow_neg_valuation hy]
  change (if x = 0 then 0 else WithZero.exp (-x.valuation)) ≤
      (if y = 0 then 0 else WithZero.exp (-y.valuation)) ↔
    (p : ℝ) ^ (-x.valuation) ≤ (p : ℝ) ^ (-y.valuation)
  rw [ite_eq_right hx, ite_eq_right hy, WithZero.exp_le_exp]
  have hpone : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  exact (zpow_right_strictMono₀ hpone).le_iff_le.symm

/-- The usual topology on `ℚ_p` is induced by its canonical valuation. -/
theorem padicIsValuativeTopology : IsValuativeTopology ℚ_[p] := by
  let v : Valuation ℚ_[p] NNReal := NormedField.valuation
  let : Valued ℚ_[p] NNReal := NormedField.toValued
  let : v.Compatible := normedFieldValuation_compatible_padic p
  apply IsValuativeTopology.of_mem_nhds_zero_iff_vle v
  intro s
  exact Valued.mem_nhds_zero

/-- Mathlib's p-adic field is a nonarchimedean local field for the
topology-first interface used by local class field theory. -/
noncomputable instance padicIsNonarchimedeanLocalField :
    IsNonarchimedeanLocalField ℚ_[p] where
  toIsValuativeTopology := padicIsValuativeTopology p
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance

end LocalFieldTheory.Padic
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_2
attribute [local instance] GlobalClassFieldTheory.Reciprocity.instNeZeroNatVal_solutions
noncomputable local instance
    rationalCyclotomicLevelFiniteDimensional_ra7f188_1
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  IsCyclotomicExtension.finiteDimensional
    {(m : ℕ)} ℚ (KummerTheory.rationalCyclotomicLevel m)
noncomputable local instance
    rationalCyclotomicLevelIsAbelianGalois_ra7f188_1
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) := by
  have : IsGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
    inferInstance
  let e :=
    IsCyclotomicExtension.Rat.galEquivZMod
      (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)
  exact
    { is_comm.comm σ τ := by
        apply e.injective
        simp only [map_mul]
        exact mul_comm _ _ }
@[reducible]
noncomputable local instance rationalFinitePlaceBaseNontriviallyNormedField
    (q : Nat.Primes) :
    NontriviallyNormedField
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  absoluteValueExtension_completionNontriviallyNormedField
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q))
    (RayClass.adicAbv_isNontrivial
      (RayClass.rationalPrime q))

noncomputable local instance rationalFinitePlaceBaseLocallyCompactSpace
    (q : Nat.Primes) :
    LocallyCompactSpace
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry
      (RayClass.rationalPrime q))

noncomputable local instance rationalFinitePlaceBaseIsUltrametricDist
    (q : Nat.Primes) :
    IsUltrametricDist
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  finitePlaceArtinCompletionIsUltrametricDist
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (RayClass.rationalPrime q))

@[reducible]
noncomputable local instance rationalFinitePlaceBaseValued
    (q : Nat.Primes) :
    Valued
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion ℝ≥0 :=
  finitePlaceArtinCompletionValued
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (RayClass.rationalPrime q))

@[reducible]
noncomputable local instance rationalFinitePlaceBaseValuativeRel
    (q : Nat.Primes) :
    ValuativeRel
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  finitePlaceLocalArtinCompletionValuativeRel
    (K := ℚ) (RayClass.rationalPrime q)

attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionRatAlgebra
noncomputable local instance
    rationalFinitePlaceBaseValuationIsNontrivial
    (q : Nat.Primes) :
    (Valued.v :
      Valuation
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation
      (K :=
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion)).IsNontrivial)

noncomputable local instance rationalFinitePlaceBaseValuationCompatible
    (q : Nat.Primes) :
    (Valued.v :
      Valuation
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _

noncomputable local instance
    rationalFinitePlaceBaseValuativeRelIsNontrivial
    (q : Nat.Primes) :
    ValuativeRel.IsNontrivial
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v :
      Valuation
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        ℝ≥0)).2 inferInstance

noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_ra7f188_1
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0
noncomputable local instance
    rationalFinitePlaceBaseIsNonarchimedeanLocalField
    (q : Nat.Primes) :
    IsNonarchimedeanLocalField
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField
    (K := ℚ) (RayClass.rationalPrime q)

/-! Named compatibility witnesses used by the ramified-prime and ray-norm
modules.  They are not installed as a duplicate module-level instance family;
the canonical instances above already provide the same data. -/

/-- The canonical nontrivially normed field structure on the completion of
`ℚ` at the rational prime `p`, exposed for principal-prime constructions. -/
@[reducible]
noncomputable def rationalPrimeFactorCompletionNontriviallyNormedField
    (p : Nat.Primes) :
    NontriviallyNormedField
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseNontriviallyNormedField p

/-- The canonical `ℝ≥0`-valued structure on the completion of `ℚ` at `p`. -/
@[reducible]
noncomputable def rationalPrimeFactorCompletionValued
    (p : Nat.Primes) :
    Valued
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion ℝ≥0 :=
  rationalFinitePlaceBaseValued p

/-- The valuative relation induced by the canonical valuation on the
completion of `ℚ` at `p`. -/
@[reducible]
noncomputable def rationalPrimeFactorCompletionValuativeRel
    (p : Nat.Primes) :
    ValuativeRel
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseValuativeRel p

/-- The rational finite-place completion used at the prime `p`. -/
abbrev RationalCyclotomicPrincipalPrimeCompletion
    (p : Nat.Primes) :=
  (HeightOneSpectrum.adicAbv ℚ
    (RayClass.rationalPrime p)).Completion

abbrev rationalCyclotomicArtinPlace (q : Nat.Primes) :
    HeightOneSpectrum (𝓞 ℚ) :=
  RayClass.rationalPrime q

abbrev rationalCyclotomicArtinBaseAbv (q : Nat.Primes) :
    AbsoluteValue ℚ ℝ :=
  HeightOneSpectrum.adicAbv ℚ (rationalCyclotomicArtinPlace q)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Padic_UnitDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

theorem padicDVRValuation_surjective
    (p : ℕ) [Fact p.Prime] :
    Function.Surjective (padicDVRValuation p) := by
  intro y
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  let π :=
    valuation_exists_uniformizer ℚ_[p]
      (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) |>.choose
  have hπ :
      padicDVRValuation p π =
        WithZero.exp (-1 : ℤ) :=
    valuation_exists_uniformizer ℚ_[p]
      (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) |>.choose_spec
  refine ⟨π ^ (- WithZero.log y), ?_⟩
  rw [map_zpow₀ (padicDVRValuation p) π (- WithZero.log y)]
  rw [hπ]
  rw [← WithZero.exp_zsmul]
  simpa using WithZero.exp_log hy

theorem padicIntEquivValuationSubring_coe
    (p : ℕ) [Fact p.Prime] (z : ℤ_[p]) :
    ((padicIntEquivValuationSubring p z :
      (padicDVRValuation p).valuationSubring) : ℚ_[p]) =
        (z : ℚ_[p]) := by
  rfl

theorem padicIntEquivValuationSubring_symm_coe
    (p : ℕ) [Fact p.Prime]
    (z : (padicDVRValuation p).valuationSubring) :
    (((padicIntEquivValuationSubring p).symm z : ℤ_[p]) : ℚ_[p]) =
      (z : ℚ_[p]) := by
  calc
    (((padicIntEquivValuationSubring p).symm z : ℤ_[p]) : ℚ_[p]) =
        ((padicIntEquivValuationSubring p
          ((padicIntEquivValuationSubring p).symm z) :
            (padicDVRValuation p).valuationSubring) : ℚ_[p]) := by
      symm
      exact padicIntEquivValuationSubring_coe p _
    _ = (z : ℚ_[p]) := by
      rw [RingEquiv.apply_symm_apply]

/-- The standard `p`-adic integers and the valuation subring of `ℚ_[p]`
are continuously multiplicatively equivalent. -/
noncomputable def padicIntValuationSubringContinuousMulEquiv
    (p : ℕ) [Fact p.Prime] :
    let v := padicDVRValuation p
    ℤ_[p] ≃ₜ* v.valuationSubring := by
  let v := padicDVRValuation p
  let e := padicIntEquivValuationSubring p
  exact
    { e.toMulEquiv with
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact isometry_subtype_coe.continuous.congr fun z =>
          padicIntEquivValuationSubring_coe p z
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact isometry_subtype_coe.continuous.congr fun z =>
          (padicIntEquivValuationSubring_symm_coe p z).symm }

end Padic
end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Concrete_Cyclotomic_ProfiniteUnitDecomposition_DenseTorsion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Density of torsion in the finite profinite-unit factor
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open LocalFieldTheory.Padic

/-- The torsion elements are dense in an arbitrary product of finite
commutative groups. -/
theorem dense_torsion_pi_of_finite
    {ι : Type*} (G : ι → Type*)
    [(i : ι) → CommGroup (G i)]
    [(i : ι) → TopologicalSpace (G i)]
    [(i : ι) → Finite (G i)] :
    Dense
      (CommGroup.torsion ((i : ι) → G i) :
        Set ((i : ι) → G i)) := by
  classical
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨x, hx⟩
  obtain ⟨S, u, hu, hSu⟩ :=
    isOpen_pi_iff.mp hU x hx
  let y : (i : ι) → G i :=
    fun i => if hi : i ∈ S then x i else 1
  refine ⟨y, hSu ?_, ?_⟩
  · intro i hi
    have hiS : i ∈ S := hi
    change (if _ : i ∈ S then x i else 1) ∈ u i
    simp only [hiS, ↓reduceDIte]
    exact (hu i hi).2
  · change IsOfFinOrder y
    let N := ∏ i ∈ S, orderOf (x i)
    have hN : 0 < N := by
      dsimp only [N]
      exact Finset.prod_pos fun i _ => orderOf_pos (x i)
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨N, hN, ?_⟩
    funext i
    by_cases hi : i ∈ S
    · rw [Pi.pow_apply]
      dsimp only [y]
      rw [dite_eq_left hi]
      exact orderOf_dvd_iff_pow_eq_one.mp
        (Finset.dvd_prod_of_mem
          (fun j => orderOf (x j)) hi)
    · simp [y, hi]

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

section Galois

variable [IsGalois K L]

/-- The archimedean Artin homomorphism associated with a specified
infinite place above the base place. -/
noncomputable def infinitePlaceArtinMonoidHomOfPlace
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    v.Completionˣ →* (L ≃ₐ[K] L) := by
  by_cases hUnramified : w.IsUnramified K
  · exact 1
  · have hRamified : w.IsRamified K :=
      hUnramified
    have hvReal : v.IsReal := by
      rw [← hw]
      exact hRamified.isReal
    let signToGalois : ℤˣ →* (L ≃ₐ[K] L) :=
      { toFun := fun u =>
          if u = 1 then 1
          else
            ramifiedInfinitePlaceConjugation
              (K := K) w hRamified
        map_one' := ite_eq_left rfl
        map_mul' := by
          intro x y
          rcases Int.units_eq_one_or x with rfl | rfl
          · simp
          rcases Int.units_eq_one_or y with rfl | rfl
          · simp
          · simp [
              ramifiedInfinitePlaceConjugation_sq
                (K := K) w hRamified] }
    let completionUnitsEquivRealUnits :
        v.Completionˣ ≃* ℝˣ :=
      Units.mapEquiv
        (InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal).toMulEquiv
    exact
      signToGalois.comp
        (LocalClassFieldTheory.realUnitsSign.comp
          completionUnitsEquivRealUnits.toMonoidHom)

/-- The actual local Artin homomorphism at an infinite place, using
the infinite place of `L` already chosen by the local-block API. -/
noncomputable def chosenInfinitePlaceArtinMonoidHom
    (v : InfinitePlace K) :
    v.Completionˣ →* (L ≃ₐ[K] L) :=
  infinitePlaceArtinMonoidHomOfPlace
    (K := K) (L := L) v
    (chosenInfinitePlaceAbove
      (L := L) v)
    (chosenInfinitePlaceAbove_comap
      (L := L) v)

end Galois

section AbelianTower

variable [IsAbelianGalois K L]

omit [NumberField K] [NumberField L] in
/-- In an abelian extension, the archimedean Artin homomorphism is
independent of the chosen infinite place above the base place. -/
theorem infinitePlaceArtinMonoidHomOfPlace_eq
    (v : InfinitePlace K)
    (w w' : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (hw' : w'.comap (algebraMap K L) = v) :
    infinitePlaceArtinMonoidHomOfPlace
        (K := K) (L := L) v w hw =
      infinitePlaceArtinMonoidHomOfPlace
        (K := K) (L := L) v w' hw' := by
  obtain ⟨g, hg⟩ :=
    InfinitePlace.exists_smul_eq_of_comap_eq
      (hw.trans hw'.symm)
  have hUnramified :
      w.IsUnramified K ↔ w'.IsUnramified K := by
    rw [InfinitePlace.isUnramified_iff,
      InfinitePlace.isUnramified_iff, hw, hw']
    rw [← hg, InfinitePlace.isReal_smul_iff]
  by_cases hwUnramified : w.IsUnramified K
  · have hw'Unramified : w'.IsUnramified K :=
      hUnramified.mp hwUnramified
    simp [infinitePlaceArtinMonoidHomOfPlace,
      hwUnramified, hw'Unramified]
  · have hw'Unramified : ¬ w'.IsUnramified K :=
      fun h => hwUnramified (hUnramified.mpr h)
    have hwRamified : w.IsRamified K := hwUnramified
    have hw'Ramified : w'.IsRamified K := hw'Unramified
    let sigma :=
      ramifiedInfinitePlaceConjugation
        (K := K) w hwRamified
    let sigma' :=
      ramifiedInfinitePlaceConjugation
        (K := K) w' hw'Ramified
    have hsigma :=
      ramifiedInfinitePlaceConjugation_isConj
        (K := K) w hwRamified
    have hsigma' :=
      ramifiedInfinitePlaceConjugation_isConj
        (K := K) w' hw'Ramified
    have hsigmaMem :
        sigma ∈
          MulAction.stabilizer (L ≃ₐ[K] L) w := by
      rw [← InfinitePlace.mk_embedding w,
        InfinitePlace.mem_stabilizer_mk_iff]
      exact Or.inr hsigma
    have hsigmaMem' :
        sigma ∈
          MulAction.stabilizer (L ≃ₐ[K] L) w' := by
      rw [← hg]
      rw [MulAction.mem_stabilizer_iff] at hsigmaMem
      rw [MulAction.mem_stabilizer_iff]
      calc
        sigma • (g • w) =
            (sigma * g) • w :=
          (mul_smul sigma g w).symm
        _ = (g * sigma) • w := by
          rw [mul_comm]
        _ = g • (sigma • w) :=
          mul_smul g sigma w
        _ = g • w := by
          rw [hsigmaMem]
    have hsigmaNe : sigma ≠ 1 :=
      (NumberField.ComplexEmbedding.isConj_ne_one_iff
        hsigma).2
        (InfinitePlace.isComplex_iff.mp
          hwRamified.isComplex)
    have hsigmaAtW' :
        NumberField.ComplexEmbedding.IsConj
          (InfinitePlace.embedding w') sigma := by
      rw [← InfinitePlace.mk_embedding w',
        InfinitePlace.mem_stabilizer_mk_iff] at hsigmaMem'
      exact hsigmaMem'.resolve_left hsigmaNe
    have hsigmaEq : sigma = sigma' :=
      hsigmaAtW'.ext hsigma'
    apply MonoidHom.ext
    intro x
    simp [infinitePlaceArtinMonoidHomOfPlace,
      hwUnramified, hw'Unramified,
      sigma, sigma', hsigmaEq]

omit [NumberField K] [NumberField L] in
/-- Archimedean Artin homomorphisms attached to specified places commute
with restriction through an abelian tower. -/
theorem infinitePlaceArtinMonoidHomOfPlace_restrict_tower
    {E : Type}
    [Field E] [NumberField E]
    [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [IsGalois K E]
    (v : InfinitePlace K)
    (wL : InfinitePlace L)
    (hwL : wL.comap (algebraMap K L) = v)
    (hwE :
      (wL.comap (algebraMap E L)).comap
          (algebraMap K E) = v) :
    (AlgEquiv.restrictNormalHom E).comp
        (infinitePlaceArtinMonoidHomOfPlace
          (K := K) (L := L) v wL hwL) =
      infinitePlaceArtinMonoidHomOfPlace
        (K := K) (L := E) v
        (wL.comap (algebraMap E L)) hwE := by
  let wE := wL.comap (algebraMap E L)
  by_cases hLUnramified : wL.IsUnramified K
  · have hEUnramified : wE.IsUnramified K :=
      hLUnramified.comap E
    simp [infinitePlaceArtinMonoidHomOfPlace,
      hLUnramified, hEUnramified, wE]
  · have hLRamified : wL.IsRamified K :=
      hLUnramified
    have hvReal : v.IsReal := by
      rw [← hwL]
      exact hLRamified.isReal
    let sigmaL :=
      ramifiedInfinitePlaceConjugation
        (K := K) wL hLRamified
    let sigmaR : E ≃ₐ[K] E :=
      AlgEquiv.restrictNormalHom E sigmaL
    have hsigmaL :=
      ramifiedInfinitePlaceConjugation_isConj
        (K := K) wL hLRamified
    let phi : E →+* ℂ :=
      (InfinitePlace.embedding wL).comp
        (algebraMap E L)
    have hphi :
        NumberField.ComplexEmbedding.IsConj
          phi sigmaR := by
      apply RingHom.ext
      intro x
      change
        star
            (InfinitePlace.embedding wL
              (algebraMap E L x)) =
          InfinitePlace.embedding wL
            (algebraMap E L (sigmaR x))
      rw [show
        algebraMap E L (sigmaR x) =
          sigmaL (algebraMap E L x) by
          dsimp [sigmaR]
          exact AlgEquiv.restrictNormal_commutes sigmaL E x]
      exact (hsigmaL.eq (algebraMap E L x)).symm
    have hmk : InfinitePlace.mk phi = wE := by
      change
        InfinitePlace.mk
            ((InfinitePlace.embedding wL).comp
              (algebraMap E L)) =
          wL.comap (algebraMap E L)
      conv_rhs => rw [← InfinitePlace.mk_embedding wL]
      rw [InfinitePlace.comap_mk]
    by_cases hEUnramified : wE.IsUnramified K
    · have hEUnramified' :
          (wL.comap (algebraMap E L)).IsUnramified K := by
        simpa only [wE] using hEUnramified
      have hsigmaR : sigmaR = 1 :=
        hphi.isUnramified_mk_iff.mp
          (hmk.symm ▸ hEUnramified)
      apply MonoidHom.ext
      intro x
      unfold infinitePlaceArtinMonoidHomOfPlace
      rw [dite_eq_right hLUnramified, dite_eq_left hEUnramified']
      simp only [MonoidHom.comp_apply]
      dsimp
      split_ifs with hsign
      · simp
      · simpa [sigmaR, sigmaL] using hsigmaR
    · have hEUnramified' :
          ¬ (wL.comap (algebraMap E L)).IsUnramified K := by
        simpa only [wE] using hEUnramified
      have hERamified : wE.IsRamified K :=
        hEUnramified
      let sigmaE :=
        ramifiedInfinitePlaceConjugation
          (K := K) wE hERamified
      have hsigmaE :=
        ramifiedInfinitePlaceConjugation_isConj
          (K := K) wE hERamified
      have hsigmaRNe : sigmaR ≠ 1 := by
        intro hsigmaR
        have :
            (InfinitePlace.mk phi).IsUnramified K :=
          hphi.isUnramified_mk_iff.mpr hsigmaR
        exact hEUnramified (hmk ▸ this)
      have hsigmaRMem :
          sigmaR ∈
            MulAction.stabilizer (E ≃ₐ[K] E) wE := by
        rw [← hmk,
          InfinitePlace.mem_stabilizer_mk_iff]
        exact Or.inr hphi
      have hsigmaRAtWE :
          NumberField.ComplexEmbedding.IsConj
            (InfinitePlace.embedding wE) sigmaR := by
        rw [← InfinitePlace.mk_embedding wE,
          InfinitePlace.mem_stabilizer_mk_iff] at hsigmaRMem
        exact hsigmaRMem.resolve_left hsigmaRNe
      have hsigmaREq : sigmaR = sigmaE :=
        hsigmaRAtWE.ext hsigmaE
      apply MonoidHom.ext
      intro x
      unfold infinitePlaceArtinMonoidHomOfPlace
      rw [dite_eq_right hLUnramified, dite_eq_right hEUnramified']
      simp only [MonoidHom.comp_apply]
      dsimp
      split_ifs with hsign
      · simp
      · simpa [sigmaR, sigmaL, sigmaE] using hsigmaREq

omit [NumberField K] [NumberField L] in
/-- Archimedean local factors commute with restriction in an abelian
number-field tower. -/
theorem chosenInfinitePlaceArtinMonoidHom_restrict_tower
    {E : Type}
    [Field E] [NumberField E]
    [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [IsAbelianGalois K E]
    (v : InfinitePlace K) :
    (AlgEquiv.restrictNormalHom E).comp
        (chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v) =
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := E) v := by
  let wL :=
    chosenInfinitePlaceAbove
      (L := L) v
  let wE := wL.comap (algebraMap E L)
  have hwL :
      wL.comap (algebraMap K L) = v :=
    chosenInfinitePlaceAbove_comap
      (L := L) v
  have hwE :
      wE.comap (algebraMap K E) = v := by
    dsimp only [wE]
    rw [← InfinitePlace.comap_comp,
      ← IsScalarTower.algebraMap_eq K E L, hwL]
  calc
    (AlgEquiv.restrictNormalHom E).comp
        (chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v) =
      infinitePlaceArtinMonoidHomOfPlace
        (K := K) (L := E) v wE hwE :=
      infinitePlaceArtinMonoidHomOfPlace_restrict_tower
        (K := K) (L := L) (E := E)
        v wL hwL hwE
    _ = chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := E) v :=
      infinitePlaceArtinMonoidHomOfPlace_eq
        (K := K) (L := E) v wE
        (chosenInfinitePlaceAbove
          (L := E) v)
        hwE
        (chosenInfinitePlaceAbove_comap
          (L := E) v)

end AbelianTower

section Galois

variable [IsGalois K L]

omit [NumberField K] [NumberField L] in
/-- The chosen archimedean Artin homomorphism is continuous. -/
theorem chosenInfinitePlaceArtinMonoidHom_continuous
    (v : InfinitePlace K) :
    Continuous
      (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v) := by
  classical
  let w :=
    chosenInfinitePlaceAbove
      (L := L) v
  by_cases hUnramified : w.IsUnramified K
  · have hUnramified' :
        (chosenInfinitePlaceAbove (L := L) v).IsUnramified K := by
      simpa only [w] using hUnramified
    unfold chosenInfinitePlaceArtinMonoidHom
    unfold infinitePlaceArtinMonoidHomOfPlace
    rw [dite_eq_left hUnramified']
    exact continuous_const
  · have hUnramified' :
        ¬ (chosenInfinitePlaceAbove (L := L) v).IsUnramified K := by
      simpa only [w] using hUnramified
    have hRamified : w.IsRamified K := hUnramified
    have hvReal : v.IsReal := by
      rw [← chosenInfinitePlaceAbove_comap (L := L) v]
      exact hRamified.isReal
    let e : v.Completionˣ ≃ₜ* ℝˣ :=
      Units.mapContinuousMulEquiv
        (RayClass.realCompletionContinuousMulEquiv v hvReal)
    let signToGalois : ℤˣ → (L ≃ₐ[K] L) :=
      fun u =>
        if u = 1 then 1
        else
          ramifiedInfinitePlaceConjugation
            (K := K)
            (chosenInfinitePlaceAbove (L := L) v)
            hUnramified'
    have hSignToGalois : Continuous signToGalois :=
      continuous_of_discreteTopology
    have hMap :
        Continuous fun x : v.Completionˣ =>
          Units.mapEquiv
            (InfinitePlace.Completion.ringEquivRealOfIsReal
              hvReal).toMulEquiv x := by
      change Continuous e
      exact e.continuous_toFun
    unfold chosenInfinitePlaceArtinMonoidHom
    unfold infinitePlaceArtinMonoidHomOfPlace
    rw [dite_eq_right hUnramified']
    change
      Continuous fun x : v.Completionˣ =>
        signToGalois
          (LocalClassFieldTheory.realUnitsSign
            (Units.mapEquiv
              (InfinitePlace.Completion.ringEquivRealOfIsReal
                hvReal).toMulEquiv x))
    exact hSignToGalois.comp
      (LocalClassFieldTheory.realUnitsSign_continuous.comp hMap)

omit [NumberField K] [NumberField L] in
/-- A positive element at a real place has trivial archimedean Artin
symbol. -/
theorem chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos
    (v : InfinitePlace K) (hvReal : v.IsReal)
    (x : v.Completionˣ)
    (hx :
      0 <
        InfinitePlace.Completion.ringEquivRealOfIsReal
          hvReal (x : v.Completion)) :
    chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v x = 1 := by
  let e : v.Completion ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal
      hvReal
  let eu : v.Completionˣ ≃* ℝˣ :=
    Units.mapEquiv e.toMulEquiv
  have hx' : 0 < (eu x : ℝ) := by
    simpa [eu, e] using hx
  have hsign :
      LocalClassFieldTheory.realUnitsSign (eu x) = 1 :=
    MonoidHom.mem_ker.mp
      ((LocalClassFieldTheory.mem_realUnitsSign_ker_iff
        (eu x)).2 hx')
  have hsign' :
      LocalClassFieldTheory.realUnitsSign
          (Units.mapEquiv
            (InfinitePlace.Completion.ringEquivRealOfIsReal
              hvReal).toMulEquiv x) = 1 := by
    simpa [eu, e] using hsign
  let w :=
    chosenInfinitePlaceAbove
      (L := L) v
  by_cases hUnramified : w.IsUnramified K
  · have hUnramified' :
        (chosenInfinitePlaceAbove (L := L) v).IsUnramified K := by
      simpa only [w] using hUnramified
    unfold chosenInfinitePlaceArtinMonoidHom
    unfold infinitePlaceArtinMonoidHomOfPlace
    rw [dite_eq_left hUnramified']
    rfl
  · have hUnramified' :
        ¬ (chosenInfinitePlaceAbove (L := L) v).IsUnramified K := by
      simpa only [w] using hUnramified
    unfold chosenInfinitePlaceArtinMonoidHom
    unfold infinitePlaceArtinMonoidHomOfPlace
    rw [dite_eq_right hUnramified']
    simp only [MonoidHom.comp_apply]
    change
      (if
          LocalClassFieldTheory.realUnitsSign
              (Units.mapEquiv
                (InfinitePlace.Completion.ringEquivRealOfIsReal
                  hvReal).toMulEquiv x) =
            1 then
        1
      else _) =
        1
    rw [hsign']
    simp

end Galois

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

/-- The cyclotomic level `4` used for the rational complexification. -/
abbrev rationalComplexificationCyclotomicOrder : ℕ+ :=
  ⟨rationalComplexificationPrime.1 ^ 2,
    pow_pos rationalComplexificationPrime.2.pos 2⟩

local instance rationalComplexificationPrimeFact_ra7f188_1 :
    Fact rationalComplexificationPrime.1.Prime :=
  ⟨rationalComplexificationPrime.2⟩
local instance rationalComplexificationPrimeSquareNeZero_ra7f188_1 :
    NeZero (rationalComplexificationPrime.1 ^ 2) :=
  ⟨pow_ne_zero 2 rationalComplexificationPrime.2.ne_zero⟩
noncomputable instance complexFourthRootField_isCyclotomic :
    IsCyclotomicExtension {4} ℚ complexFourthRootField := by
  apply
    IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      ({4} : Set ℕ) ℚ ℂ
  intro n hn _hn0
  rw [Set.mem_singleton_iff] at hn
  subst n
  exact ⟨Complex.I, complexI_isPrimitiveRoot_four⟩

noncomputable instance complexFourthRootField_finiteDimensional :
    FiniteDimensional ℚ complexFourthRootField :=
  IsCyclotomicExtension.finiteDimensional
    ({4} : Set ℕ) ℚ complexFourthRootField

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The complex-conjugation overfield at an infinite place

This module realizes the embedded field `L(i)` inside `ℂ`, constructs its
complex place, and identifies ambient complex conjugation on that field.
-/

open scoped Classical IsMulCommutative
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K]
    [Field L] [NumberField L] [Algebra K L]

variable
    [NumberField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The concrete field `L(i)` inside `ℂ`, formed using the complex
embedding belonging to the chosen place above `v`. -/
def infinitePlaceComplexificationOverfield
    (v : InfinitePlace K) :
    IntermediateField ℚ ℂ :=
  (InfinitePlace.embedding
      (chosenInfinitePlaceAbove (L := L) v)).toRatAlgHom.fieldRange ⊔
    complexFourthRootField

@[reducible]
noncomputable local instance
    infinitePlaceComplexificationOverfieldRationalAlgebra
    (v : InfinitePlace K) :
    Algebra ℚ
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (infinitePlaceComplexificationOverfield
    (K := K) (L := L) v).algebra'

/-- The chosen top-field embedding `L → L(i)`. -/
noncomputable def infinitePlaceComplexificationOverfieldEmbedding
    (v : InfinitePlace K) :
    L →ₐ[ℚ]
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v :=
  let φ :=
    (InfinitePlace.embedding
      (chosenInfinitePlaceAbove (L := L) v)).toRatAlgHom
  φ.codRestrict
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v).toSubalgebra
    (fun x =>
      (show
        φ.fieldRange ≤
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v from
        le_sup_left)
        (show φ x ∈ φ.fieldRange from
          (AlgHom.mem_fieldRange).mpr ⟨x, rfl⟩))

omit [NumberField K] [FiniteDimensional K L] in
/-- The chosen embedding into the complexification overfield agrees
with the original complex embedding after coercion to `ℂ`. -/
@[simp]
theorem infinitePlaceComplexificationOverfieldEmbedding_coe
    (v : InfinitePlace K) (x : L) :
    ((infinitePlaceComplexificationOverfieldEmbedding
        (K := K) (L := L) v x :
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) : ℂ) =
      InfinitePlace.embedding
        (chosenInfinitePlaceAbove (L := L) v) x := by
  change
    (InfinitePlace.embedding
      (chosenInfinitePlaceAbove (L := L) v)).toRatAlgHom x =
      InfinitePlace.embedding
        (chosenInfinitePlaceAbove (L := L) v) x
  rfl

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_Different
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Different and codifferent for valued finite extensions

This file specializes mathlib's Dedekind-domain different ideal to complete
DVF valuation rings.  The ideal itself remains mathlib's `differentIdeal`; the
extra API here connects it to the chosen valuation rings, the codifferent, and
the local unramified criterion.
-/

noncomputable section

universe u v w x

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace RamificationTheory
namespace DiscreteValuationField

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

omit [FiniteDimensional K L] in
/-- The fraction-field extension attached to a finite separable complete-DVF
extension is separable.  This is kept private to prevent typeclass search from
trying the very general `FractionRing.liftAlgebra` instance globally. -/
theorem fractionRing_isSeparable_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L]
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    letI : FaithfulSMul base.valuationSubring target.valuationSubring :=
      Module.IsTorsionFree.to_faithfulSMul
    letI : FaithfulSMul base.valuationSubring
        (FractionRing target.valuationSubring) := inferInstance
    letI : Algebra (FractionRing base.valuationSubring)
        (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
    Algebra.IsSeparable (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := by
  let : FaithfulSMul base.valuationSubring target.valuationSubring :=
    Module.IsTorsionFree.to_faithfulSMul
  let : FaithfulSMul base.valuationSubring
      (FractionRing target.valuationSubring) := inferInstance
  let fracAlgebra : Algebra (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
  let : SMul (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    @Algebra.toSMul _ _ _ _ fracAlgebra
  let : IsScalarTower base.valuationSubring
      (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  have H : RingHom.comp
      (algebraMap (FractionRing base.valuationSubring)
        (FractionRing target.valuationSubring))
      (FractionRing.algEquiv base.valuationSubring K).symm.toRingEquiv =
        RingHom.comp
          (FractionRing.algEquiv target.valuationSubring L).symm.toRingEquiv
          (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors base.valuationSubring)
    ext a
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply,
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply
      base.valuationSubring target.valuationSubring L,
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv _ _ H

/-- In a monogenic finite separable extension, the derivative of the minimal
polynomial belongs to the different. -/
theorem aeval_derivative_mem_differentIdeal
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L]
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    (z : target.valuationSubring)
    (hz : Algebra.adjoin K {(algebraMap target.valuationSubring L) z} = ⊤) :
    Polynomial.aeval z
        (Polynomial.derivative (minpoly base.valuationSubring z)) ∈
      differentIdeal base.valuationSubring target.valuationSubring := by
  exact _root_.aeval_derivative_mem_differentIdeal
    base.valuationSubring K L z hz

end ValuedExtension
end DiscreteValuationField
end RamificationTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_CyclotomicPrimeBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

/-- Over a characteristic-zero field, the degree of `K(μ_p)` is
strictly smaller than the prime `p`. -/
theorem primeCyclotomicBase_finrank_lt
    (p : ℕ) (hp : p.Prime) :
    Module.finrank K (PrimeCyclotomicBase K p) < p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hle :
      Module.finrank K (PrimeCyclotomicBase K p) ≤
        Nat.totient p :=
    cyclotomicField_finrank_le_totient
      K p hp.pos
  rw [Nat.totient_prime hp] at hle
  exact hle.trans_lt (Nat.sub_one_lt hp.ne_zero)

omit [NumberField L] [IsGalois K L] in
/-- The cyclotomic degree is coprime to a prime-degree extension. -/
theorem primeCyclotomicBase_finrank_coprime
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    (Module.finrank K (PrimeCyclotomicBase K p)).Coprime
      (Module.finrank K L) := by
  rw [hdegree]
  exact
    (Nat.coprime_of_lt_prime
      (ne_of_gt Module.finrank_pos)
      (primeCyclotomicBase_finrank_lt
        (K := K) p hp)
      hp).symm

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_TopologicalGlobalNormResidueAbelianization
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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
    topologicalGlobalNormResidueAbelianization_ideleClassGroupIsMulCommutative_ra7f188_1 :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
attribute [local instance] GlobalClassFieldTheory.Reciprocity.topologicalGlobalNormResidueAbelianization_galoisAbelianizationTopology
omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- The abelianization of a finite Krull Galois group carries the
discrete quotient topology. -/
theorem finiteGaloisAbelianization_discreteTopology :
    DiscreteTopology
      (Abelianization (Gal(L / K))) := by
  change
    DiscreteTopology
      (Gal(L / K) ⧸
        commutator (Gal(L / K)))
  apply QuotientGroup.discreteTopology
  exact isOpen_discrete _

local instance
    topologicalGlobalNormResidueAbelianization_galoisAbelianizationDiscreteTopology :
    DiscreteTopology (Abelianization (Gal(L / K))) :=
  finiteGaloisAbelianization_discreteTopology K L

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafNormalization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace


namespace PrimeDegreePackets


lemma rootLeafWindow_open (R : ℝ) (m : ℕ) : IsOpen (rootLeafWindow R m) := isOpen_Ioo

end PrimeDegreePackets


end
end

end OAI
end


