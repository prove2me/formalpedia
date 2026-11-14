-- Prove2me | Definitions.Def_OAIQ244Duke010
-- name    : OAIQ244Duke010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:10:31.393207+00:00
-- url     : https://prove2.me/theorems/62d25b25-73ff-4db9-9e79-220252a96968
-- title:
--   Definitions bundle OAIQ244Duke010 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 127 declarations of OpenAI's Lean: 34 definitions, 1 inductive type or structure, 5 instances and 87 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.complexFourthRootField`, `GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricRationalSeparableClosureAlgebra`, `GlobalClassFieldTheory.Reciprocity.ideleClassContinuousQuotientLift`, `GlobalClassFieldTheory.Reciprocity.quotientAddEquivOfEquivMapEq`, `GlobalClassFieldTheory.Reciprocity.rationalComplexificationPrime`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalPrimeModulus`, `GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionRatAlgebra`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeFactorizationPrimeSupport`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeFactorizationSupport`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeFactorizationSupportEmbedding`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeFactorizationSupportEraseEquiv`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeGeneratorUnit`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeOfMemFactorizationSupportErase`, `GlobalClassFieldTheory.Reciprocity.rationalPrimeUnit`, `GlobalClassFieldTheory.Reciprocity.topologicalGlobalNormResidueAbelianization_galoisAbelianizationTopology`, `InfiniteIdeleGroup.localAnnulus`, `InfiniteIdeleGroup.logFundamentalBound`, `InfiniteIdeleGroup.ringUnitToFieldUnit`, `InfiniteIdeleGroup.unitLatticeRealBasis`, `IsAdicComplete.contractingApproximation`, `LocalClassFieldTheory.SemilinearValuationCompatible`, `LocalClassFieldTheory.semilinearGaloisGroupCongr`, `LubinTate.SameUniformizer.HasLinearTerm`, `LubinTate.SameUniformizer.degreeIndexList`, `LubinTate.SameUniformizer.linearForm`, `LubinTate.padicCompletedUnramifiedWittRing`, `LubinTate.padicIntToCompletedUnramifiedWittRing`, `OAI.PrimeDegreePackets.coordinateMod`, `RamificationTheory.DiscreteValuationField.HerbrandGroupTheory.NonarchimedeanDepth`, `RelativeIdeleGroup.embeddingPolynomial`, `RelativeIdeleGroup.embeddingProductPolynomial`, `RelativeIdeleGroup.embeddingToAlgebraicClosure`, `RelativeIdeleGroup.embeddingToAlgebraicClosureEquiv`, `ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldMapOfIsEquivComap`, `ValuationTheory.DiscreteValuationField.ValuedExtension.valuationSubringMapOfIsEquivComap`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_Extension_EmbeddingNorm`, `AlgebraicNumberTheory_Idele_NormOneCompact`, `AlgebraicNumberTheory_Idele_NormTopology_ExtensionBehavior`, `AlgebraicNumberTheory_Idele_NormTopology_FiniteNormArithmetic`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification`, `GlobalClassFieldTheory_Reciprocity_CyclotomicAbstractFixedFieldArtin`, `GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleClassValuation`, `GlobalClassFieldTheory_Reciprocity_CyclotomicPrincipalIdele`, `GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedGeometricRestriction`, `GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitCore`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionAction`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionNorm`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitNormQuotient`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalAwayProduct`, `GlobalClassFieldTheory_Reciprocity_RationalPrimeFactorization`, `GlobalClassFieldTheory_Reciprocity_RationalPrincipalLocalUnit`, `GlobalClassFieldTheory_Reciprocity_TopologicalGlobalNormResidueAbelianization`, `LocalClassFieldTheory_Finite_LocalReciprocity_SemilinearNaturality`, `LubinTate_FiniteLevel_NormUniformizer`, `LubinTate_FiniteLevel_PrimitiveDisplacement`, `LubinTate_FiniteLevel_PrimitiveUniformizer`, `LubinTate_FormalModule_CoefficientEquation`, `LubinTate_FormalModule_DegreeStabilization`, `LubinTate_FormalModule_LinearTerm`, `LubinTate_FormalModule_RecursiveCorrection`, `LubinTate_FormalModule_RecursiveIntertwiner`, `LubinTate_FormalModule_Reduction`, `LubinTate_Padic_ChangedUniformizerCoefficient`, `LubinTate_Padic_ChangedUniformizerIntertwiner_DefectCorrection`, `LubinTate_Padic_CompletedPrimitiveUniformizer`, `PrimePackets_PacketMoments`, `Ramification_Herbrand_Tower`, `Ramification_HilbertRamification_Polynomial`, `Valuation_DiscreteValuationField_AddVal`, `Valuation_DiscreteValuationField_AmbientUniformizer`, `Valuation_DiscreteValuationField_ChevalleyExtension`, `Valuation_DiscreteValuationField_ValuationExtension`, `Valuation_Topology_AdicContractingFixedPoint`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke021` and `OAIQ244Duke022`.
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

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_EmbeddingNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

section EmbeddingsIntoGaloisExtension

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]

/-- Extend a `K`-embedding `L → M` to the algebraic closure of `M`. -/
def embeddingToAlgebraicClosure :
    (L →ₐ[K] M) →
      (L →ₐ[K] AlgebraicClosure M) :=
  fun f =>
    (IsScalarTower.toAlgHom K M
      (AlgebraicClosure M)).comp f

omit [Algebra L M] [IsScalarTower K L M] in
theorem embeddingToAlgebraicClosure_injective :
    Function.Injective
      (embeddingToAlgebraicClosure
        (K := K) (L := L) (M := M)) := by
  intro f g h
  ext x
  exact
    (algebraMap M (AlgebraicClosure M)).injective
      (DFunLike.congr_fun h x)

theorem embeddingToAlgebraicClosure_surjective
    [FiniteDimensional K M] [Normal K M] :
    Function.Surjective
      (embeddingToAlgebraicClosure
        (K := K) (L := L) (M := M)) := by
  intro f
  let C := AlgebraicClosure M
  let e : C →ₐ[K] C := f.liftNormal C
  let r : M →ₐ[K] M := e.restrictNormal M
  let j : L →ₐ[K] M :=
    IsScalarTower.toAlgHom K L M
  refine ⟨r.comp j, ?_⟩
  ext x
  change algebraMap M C
      (r (algebraMap L M x)) = f x
  rw [AlgHom.restrictNormal_commutes]
  change e (algebraMap L C x) = f x
  exact f.liftNormal_commutes C x

/-- Embeddings of a subextension into a finite normal overfield are the
same as embeddings into an algebraic closure. -/
noncomputable def embeddingToAlgebraicClosureEquiv
    [FiniteDimensional K M] [Normal K M] :
    (L →ₐ[K] M) ≃
      (L →ₐ[K] AlgebraicClosure M) :=
  Equiv.ofBijective embeddingToAlgebraicClosure
    ⟨embeddingToAlgebraicClosure_injective,
      embeddingToAlgebraicClosure_surjective⟩

/-- The field norm of a subextension, computed in an ambient finite
Galois extension, is the product over all embeddings into that extension. -/
theorem norm_eq_prod_embeddings_in_galoisExtension
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M] (x : L) :
    algebraMap K M (Algebra.norm K x) =
      ∏ f : L →ₐ[K] M, f x := by
  let : Algebra.IsSeparable K L :=
    Algebra.isSeparable_tower_bot_of_isSeparable K L M
  apply
    (algebraMap M
      (AlgebraicClosure M)).injective
  rw [map_prod]
  calc
    algebraMap M (AlgebraicClosure M)
        (algebraMap K M (Algebra.norm K x)) =
      algebraMap K (AlgebraicClosure M)
        (Algebra.norm K x) := by
          rw [IsScalarTower.algebraMap_apply
            K M (AlgebraicClosure M)]
    _ = ∏ f : L →ₐ[K] AlgebraicClosure M, f x :=
      Algebra.norm_eq_prod_embeddings K
        (AlgebraicClosure M) x
    _ = ∏ f : L →ₐ[K] M,
        algebraMap M (AlgebraicClosure M) (f x) := by
      exact ((embeddingToAlgebraicClosureEquiv
          (K := K) (L := L) (M := M)).prod_comp
            (fun f ↦ f x)).symm

end EmbeddingsIntoGaloisExtension

section UniversalPolynomial

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M]

/-- The linear polynomial representing a chosen `K`-embedding `L → M`. -/
def embeddingPolynomial
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (f : L →ₐ[K] M) :
    MvPolynomial ι M :=
  ∑ i, MvPolynomial.X i *
    MvPolynomial.C (f (b i))

omit [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M] in
@[simp]
theorem eval_embeddingPolynomial
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (f : L →ₐ[K] M)
    (x : L) :
    MvPolynomial.eval
        (fun i ↦ algebraMap K M (b.repr x i))
        (embeddingPolynomial b f) =
      f x := by
  rw [embeddingPolynomial, map_sum]
  simp only [map_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_C]
  calc
    ∑ i, algebraMap K M (b.repr x i) *
        f (b i) =
      ∑ i, f ((b.repr x i) • b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Algebra.smul_def]
    _ = f (∑ i, (b.repr x i) • b i) := by
      rw [map_sum]
    _ = f x := by rw [b.sum_repr]

/-- The universal product over all embeddings `L →ₐ[K] M`. -/
def embeddingProductPolynomial
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) :
    MvPolynomial ι M :=
  ∏ f : L →ₐ[K] M, embeddingPolynomial b f

omit [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K M] [IsGalois K M] in
@[simp]
theorem eval_embeddingProductPolynomial
    {ι : Type z} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (x : L) :
    MvPolynomial.eval
        (fun i ↦ algebraMap K M (b.repr x i))
        (embeddingProductPolynomial
          (M := M) b) =
      ∏ f : L →ₐ[K] M, f x := by
  simp [embeddingProductPolynomial]

end UniversalPolynomial

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormOneCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Compactness of norm-one idele classes

This module combines local compactness, the logarithmic unit lattice, and the
principal-idele norm formula to prove compactness of the norm-one subgroup of
the idele class group.
-/

open scoped Classical NumberField Pointwise RestrictedProduct NNReal
open NumberField IsDedekindDomain
open NumberField.Units.dirichletUnitTheorem

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace InfiniteIdeleGroup

/-- A compact annulus in one archimedean local multiplicative group. -/
def localAnnulus (w : InfinitePlace K) (B : ℝ) :
    Set w.Completionˣ :=
  {x | Real.exp (-B) ≤ ‖(x : w.Completion)‖ ∧
    ‖(x : w.Completion)‖ ≤ Real.exp B}

omit [NumberField K] in
theorem isCompact_localAnnulus (w : InfinitePlace K) (B : ℝ) :
    IsCompact (localAnnulus w B) := by
  have hnorm_two : ‖(2 : w.Completion)‖ = 2 := by
    calc
      ‖(2 : w.Completion)‖ =
          ‖NumberField.InfinitePlace.Completion.extensionEmbedding w
            (2 : w.Completion)‖ :=
        (Isometry.norm_map_of_map_zero
          (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w)
          (map_zero _) _).symm
      _ = 2 := by
        rw [map_ofNat]
        norm_num
  let : NontriviallyNormedField w.Completion :=
    NontriviallyNormedField.ofNormNeOne
      ⟨2, by
        intro h
        have hz : ‖(2 : w.Completion)‖ = 0 := by rw [h, norm_zero]
        rw [hnorm_two] at hz
        norm_num at hz,
       by rw [hnorm_two]; norm_num⟩
  let : ProperSpace w.Completion :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace
      w.Completion
  let A : Set w.Completion :=
    {x | Real.exp (-B) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp B}
  have hAclosed : IsClosed A := by
    change IsClosed
      ((fun x : w.Completion ↦ ‖x‖) ⁻¹'
        Set.Icc (Real.exp (-B)) (Real.exp B))
    exact isClosed_Icc.preimage continuous_norm
  have hAbounded : Bornology.IsBounded A := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨Real.exp B, fun x hx ↦ hx.2⟩
  have hAcompact : IsCompact A :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨hAclosed, hAbounded⟩
  have hArange : A ⊆ Set.range (Units.val : w.Completionˣ → w.Completion) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      subst x
      have hnonpos : Real.exp (-B) ≤ 0 := by
        simpa using hx.1
      exact (not_lt_of_ge hnonpos) (Real.exp_pos (-B))
    exact ⟨Units.mk0 x hx0, rfl⟩
  change IsCompact (Units.val ⁻¹' A)
  exact
    (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff hArange).mpr
      hAcompact

/-- Ring-of-integers units, viewed as units of the number field. -/
def ringUnitToFieldUnit :
    (𝓞 K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝓞 K) K)

/-- A real basis obtained from the full unit lattice. -/
def unitLatticeRealBasis :
    Module.Basis
      (Module.Free.ChooseBasisIndex ℤ
        (NumberField.Units.unitLattice K))
      ℝ (logSpace K) :=
  (Module.Free.chooseBasis ℤ
    (NumberField.Units.unitLattice K)).ofZLatticeBasis
      ℝ (NumberField.Units.unitLattice K)

/-- An explicit uniform logarithmic bound for representatives modulo the
ordinary unit lattice. -/
def logFundamentalBound : ℝ :=
  ∑ i, ‖unitLatticeRealBasis (K := K) i‖

theorem logFundamentalBound_nonneg :
    0 ≤ logFundamentalBound (K := K) :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

end InfiniteIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_ValuationExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

section EquivalentBase

variable {Gamma₁ Gamma₂ GammaL : Type*}
variable [LinearOrderedCommGroupWithZero Gamma₁]
variable [LinearOrderedCommGroupWithZero Gamma₂]
variable [LinearOrderedCommGroupWithZero GammaL]

/-- Replacing the base valuation by an equivalent valuation preserves the
extension relation. -/
theorem hasExtension_of_isEquiv_base
    {v₁ : _root_.Valuation K Gamma₁}
    {v₂ : _root_.Valuation K Gamma₂}
    {wL : _root_.Valuation L GammaL}
    (h : v₁.IsEquiv v₂) [v₂.HasExtension wL] :
    v₁.HasExtension wL where
  val_isEquiv_comap :=
    h.trans
      (_root_.Valuation.HasExtension.val_isEquiv_comap
        (vR := v₂) (vA := wL))

end EquivalentBase

section ComapAlongCompatibleEmbedding

variable {M : Type y} [Field M] [Algebra K M]
variable {GammaK GammaM : Type*}
variable [LinearOrderedCommGroupWithZero GammaK]
variable [LinearOrderedCommGroupWithZero GammaM]

/-- If an ambient valuation extends the base valuation, then its pullback
along any field embedding compatible with the two base embeddings also
extends the base valuation. -/
theorem hasExtension_comap_of_algebraMap_compatible
    {vK : _root_.Valuation K GammaK}
    {vM : _root_.Valuation M GammaM}
    (ι : L →+* M)
    (hι :
      ι.comp (algebraMap K L) =
        algebraMap K M)
    [vK.HasExtension vM] :
    vK.HasExtension (vM.comap ι) where
  val_isEquiv_comap := by
    rw [_root_.Valuation.isEquiv_iff_val_le_one]
    intro a
    change
      vK a ≤ 1 ↔
        vM (ι (algebraMap K L a)) ≤ 1
    rw [show ι (algebraMap K L a) = algebraMap K M a by
      exact DFunLike.congr_fun hι a]
    exact
      (_root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := vK) (vA := vM) a).symm

end ComapAlongCompatibleEmbedding

end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_ChevalleyExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ValuationTheory

/-!
# Chevalley's valuation extension theorem

Mathlib has the predicate `Valuation.HasExtension` and the induced valuation
subring/residue-field API.  This file proves the field-extension form of
Chevalley's valuation extension theorem from mathlib's maximal local subring
construction: a local subring of a field is dominated by a valuation subring.
-/

noncomputable section

universe u v w x y z

namespace DiscreteValuationField
namespace Valuation

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- If an extension valuation ring is already the actual integral closure in a
finite separable field extension over a Noetherian base valuation ring, then it
is finite over the base valuation ring.  This is the generic finite-extension
input needed before specializing uniqueness of valuation extensions to
Henselian DVFs. -/
theorem moduleFinite_valuationSubring_of_isIntegralClosure
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsNoetherianRing vK.valuationSubring]
    [IsIntegralClosure vL.valuationSubring vK.valuationSubring L] :
    Module.Finite vK.valuationSubring vL.valuationSubring := by
  let : IsFractionRing vK.valuationSubring K :=
    (_root_.Valuation.valuationSubring.integers (v := vK)).isFractionRing
  let : IsIntegrallyClosed vK.valuationSubring := by
    infer_instance
  exact IsIntegralClosure.finite vK.valuationSubring K L vL.valuationSubring

/-- The target valuation subring lies over the source valuation subring. -/
theorem valuationSubring_liesOver_of_hasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] :
    (IsLocalRing.maximalIdeal vL.valuationSubring).LiesOver
      (IsLocalRing.maximalIdeal vK.valuationSubring) :=
  inferInstance

section Tower

variable {M : Type y} [Field M]
variable [Algebra L M] [Algebra K M] [IsScalarTower K L M]
variable {ΓL : Type x} {ΓM : Type z}
variable [LinearOrderedCommGroupWithZero ΓL]
variable [LinearOrderedCommGroupWithZero ΓM]

/-- Valuation extension is transitive in a field tower. -/
theorem hasExtension_trans
    (vK : _root_.Valuation K ΓK)
    (vL : _root_.Valuation L ΓL)
    (vM : _root_.Valuation M ΓM)
    [vK.HasExtension vL] [vL.HasExtension vM] :
    vK.HasExtension vM := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext a
  simp only [Subring.mem_comap]
  rw [vM.mem_integer_iff, vK.mem_integer_iff]
  rw [IsScalarTower.algebraMap_apply K L M a]
  exact
    (_root_.Valuation.HasExtension.val_map_le_one_iff
      (vR := vL) (vA := vM) (algebraMap K L a)).trans
      (_root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := vK) (vA := vL) a)

end Tower

end Valuation
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormTopology_FiniteNormArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Finite-place arithmetic of idele norms

This file relates the finite components of the ordinary idele norm to local
orders and positive prime norms. It also proves the degree formula for the
finite positive norm under scalar extension.
-/

open scoped BigOperators NNReal NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

open Function

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

theorem finprod_over_fibers
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

/-- An integer power of a commutative-group element carries a finite sum
of exponents to the corresponding finite product. -/
theorem zpow_finset_sum
    {G : Type*} [CommGroup G]
    {ι : Type*} (g : G) (s : Finset ι) (e : ι → ℤ) :
    g ^ (∑ i ∈ s, e i) =
      ∏ i ∈ s, g ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp [hi, ih, zpow_add]

end IdeleGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormTopology_ExtensionBehavior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Scalar-extension behavior of idele norms

Scalar extension raises the finite, archimedean, and absolute idele norms to
the degree of the number-field extension. The rational relative-idele
base-change realization is included as the endpoint used by cyclotomic
reciprocity.
-/

open scoped BigOperators Classical NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

omit [NumberField L] in
theorem infinitePlaceCompletionMap_isometry
    (v₀ : InfinitePlace K)
    (W : InfinitePlace L)
    [W.1.LiesOver v₀.1] :
    Isometry
      (NumberField.LiesOver.completionMap
        (v := v₀) (w := W)) := by
  unfold NumberField.LiesOver.completionMap
  exact
    (InfinitePlace.Completion.isometryEquivCompletion W).symm.isometry.comp
      ((Isometry.isometry_mapRingHom
          (InfinitePlace.LiesOver.isometry_algebraMap W v₀)).comp
        (InfinitePlace.Completion.isometryEquivCompletion v₀).isometry)

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- The archimedean multiplicity upstairs is the base multiplicity
times the local inertia degree. -/
theorem infinitePlace_mult_eq_base_mult_mul_inertiaDeg
    (v₀ : InfinitePlace K)
    (W : InfinitePlace L)
    (hW : W ∈ v₀.placesOver L) :
    W.mult = v₀.mult * v₀.inertiaDeg W := by
  let : W.1.LiesOver v₀.1 := hW
  rcases v₀.isReal_or_isComplex with hvReal | hvComplex
  · rcases W.isReal_or_isComplex with hWReal | hWComplex
    · have hUnramified : W.IsUnramified K :=
        InfinitePlace.isUnramified_iff.mpr (Or.inl hWReal)
      rw [InfinitePlace.mult_isReal ⟨W, hWReal⟩,
        InfinitePlace.mult_isReal ⟨v₀, hvReal⟩,
        InfinitePlace.inertiaDeg_eq_one
          ⟨hW, hUnramified⟩]
    · have hComapReal :
          (W.comap (algebraMap K L)).IsReal := by
        rw [InfinitePlace.LiesOver.comap_eq W v₀]
        exact hvReal
      have hRamified : W.IsRamified K :=
        InfinitePlace.isRamified_iff.mpr
          ⟨hWComplex, hComapReal⟩
      rw [InfinitePlace.mult_isComplex ⟨W, hWComplex⟩,
        InfinitePlace.mult_isReal ⟨v₀, hvReal⟩,
        InfinitePlace.inertiaDeg_eq_two
          ⟨hW, hRamified⟩]
  · have hWComplex :
        W.IsComplex :=
      InfinitePlace.LiesOver.isComplex_of_isComplex_under
        W hvComplex
    have hComapComplex :
        (W.comap (algebraMap K L)).IsComplex := by
      rw [InfinitePlace.LiesOver.comap_eq W v₀]
      exact hvComplex
    have hUnramified : W.IsUnramified K :=
      InfinitePlace.isUnramified_iff.mpr
        (Or.inr hComapComplex)
    rw [InfinitePlace.mult_isComplex ⟨W, hWComplex⟩,
      InfinitePlace.mult_isComplex ⟨v₀, hvComplex⟩,
      InfinitePlace.inertiaDeg_eq_one
        ⟨hW, hUnramified⟩]


end IdeleGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalPrimeFactorization
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

local instance localInst_re2c093_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
/-- A finite set containing every prime occurring in the numerator or
denominator of `x`, as well as the distinguished prime `p`. -/
def rationalPrimeFactorizationSupport
    (x : ℚˣ) (p : Nat.Primes) : Finset ℕ :=
  (Finset.range
    (max (max (x : ℚ).num.natAbs (x : ℚ).den) p.1 + 1)).filter
      Nat.Prime

theorem mem_rationalPrimeFactorizationSupport
    (x : ℚˣ) (p : Nat.Primes) :
    p.1 ∈ rationalPrimeFactorizationSupport x p := by
  rw [rationalPrimeFactorizationSupport, Finset.mem_filter,
    Finset.mem_range]
  exact
    ⟨Nat.lt_succ_of_le
        (le_max_right
          (max (x : ℚ).num.natAbs (x : ℚ).den) p.1),
      p.2⟩

/-- The rational `p`-adic unit part of `x`: multiply `x` by the inverse of
its `p`-power. -/
def rationalPrimeUnit (x : ℚˣ) (p : Nat.Primes) : ℚˣ :=
  (Units.mk0 (p.1 : ℚ) (by exact_mod_cast p.2.ne_zero)) ^
      (-padicValRat p.1 (x : ℚ)) * x

@[simp]
theorem rationalPrimeUnit_val (x : ℚˣ) (p : Nat.Primes) :
    (rationalPrimeUnit x p : ℚ) =
      (p.1 : ℚ) ^ (-padicValRat p.1 (x : ℚ)) * (x : ℚ) := by
  simp [rationalPrimeUnit]

/-- The ordinary prime factorization of a nonzero rational number, over the
finite support chosen by `rationalPrimeFactorizationSupport`. -/
theorem rational_factorization_over_support
    (x : ℚˣ) (p : Nat.Primes) :
    (x : ℚ) =
      (((x : ℚ).num.sign : ℤ) : ℚ) *
        ∏ q ∈ rationalPrimeFactorizationSupport x p,
          (q : ℚ) ^ padicValRat q (x : ℚ) := by
  let r : ℚ := x
  let B : ℕ := max (max r.num.natAbs r.den) p.1 + 1
  let s : Finset ℕ := (Finset.range B).filter Nat.Prime
  have hsupport :
      rationalPrimeFactorizationSupport x p = s := by
    rfl
  have hnum0 : r.num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr
      (Rat.num_ne_zero.mpr x.ne_zero)
  have hden0 : r.den ≠ 0 :=
    r.den_ne_zero
  have hnum_lt : r.num.natAbs < B := by
    exact
      Nat.lt_succ_of_le
        (le_trans
          (le_max_left r.num.natAbs r.den)
          (le_max_left (max r.num.natAbs r.den) p.1))
  have hden_lt : r.den < B := by
    exact
      Nat.lt_succ_of_le
        (le_trans
          (le_max_right r.num.natAbs r.den)
          (le_max_left (max r.num.natAbs r.den) p.1))
  have hnumNat :=
    Nat.prod_pow_prime_padicValNat
      r.num.natAbs hnum0 B hnum_lt
  have hdenNat :=
    Nat.prod_pow_prime_padicValNat
      r.den hden0 B hden_lt
  have hnum :
      (∏ q ∈ s,
        (q : ℚ) ^ padicValNat q r.num.natAbs) =
          (r.num.natAbs : ℚ) := by
    norm_cast
  have hden :
      (∏ q ∈ s,
        (q : ℚ) ^ padicValNat q r.den) =
          (r.den : ℚ) := by
    norm_cast
  have hsign :
      (r.num : ℚ) =
        (((r.num.sign : ℤ) : ℚ)) * (r.num.natAbs : ℚ) := by
    have hsignInt :
        r.num.sign * (r.num.natAbs : ℤ) = r.num :=
      Int.sign_mul_natAbs r.num
    calc
      (r.num : ℚ) =
          ((r.num.sign * (r.num.natAbs : ℤ) : ℤ) : ℚ) :=
        congrArg (fun z : ℤ => (z : ℚ)) hsignInt.symm
      _ =
          (((r.num.sign : ℤ) : ℚ)) * (r.num.natAbs : ℚ) := by
        norm_num
  have hprod :
      (∏ q ∈ s, (q : ℚ) ^ padicValRat q r) =
        (r.num.natAbs : ℚ) / (r.den : ℚ) := by
    calc
      (∏ q ∈ s, (q : ℚ) ^ padicValRat q r) =
          ∏ q ∈ s,
            (q : ℚ) ^ padicValNat q r.num.natAbs /
              (q : ℚ) ^ padicValNat q r.den := by
        apply Finset.prod_congr rfl
        intro q hq
        have hqprime : q.Prime :=
          (Finset.mem_filter.mp hq).2
        rw [padicValRat_def, padicValInt,
          zpow_sub₀ (by exact_mod_cast hqprime.ne_zero),
          zpow_natCast, zpow_natCast]
      _ =
          (∏ q ∈ s,
              (q : ℚ) ^ padicValNat q r.num.natAbs) /
            ∏ q ∈ s,
              (q : ℚ) ^ padicValNat q r.den := by
        rw [Finset.prod_div_distrib]
      _ = (r.num.natAbs : ℚ) / (r.den : ℚ) := by
        rw [hnum, hden]
  rw [hsupport]
  calc
    (x : ℚ) = (r.num : ℚ) / (r.den : ℚ) := by
      simpa only [r] using r.num_div_den.symm
    _ =
        (((r.num.sign : ℤ) : ℚ)) *
          ((r.num.natAbs : ℚ) / (r.den : ℚ)) := by
      rw [hsign, mul_div_assoc]
    _ =
        (((r.num.sign : ℤ) : ℚ)) *
          ∏ q ∈ s, (q : ℚ) ^ padicValRat q r := by
      rw [hprod]
    _ =
        ((((x : ℚ).num.sign : ℤ) : ℚ)) *
          ∏ q ∈ s, (q : ℚ) ^ padicValRat q (x : ℚ) := by
      rfl

/-- Every member of the rational factorization support is prime. -/
theorem prime_of_mem_rationalPrimeFactorizationSupport
    (x : ℚˣ) (p : Nat.Primes) {q : ℕ}
    (hq : q ∈ rationalPrimeFactorizationSupport x p) :
    q.Prime :=
  (Finset.mem_filter.mp hq).2

/-- The canonical embedding of the natural-number factorization support
into the type of natural primes. -/
def rationalPrimeFactorizationSupportEmbedding
    (x : ℚˣ) (p : Nat.Primes) :
    ↥(rationalPrimeFactorizationSupport x p) ↪ Nat.Primes where
  toFun q :=
    ⟨q.1,
      prime_of_mem_rationalPrimeFactorizationSupport
        x p q.2⟩
  inj' q r h := by
    apply Subtype.ext
    exact
      congrArg (fun z : Nat.Primes => (z : ℕ)) h

/-- The factorization support as an actual finite set of `Nat.Primes`. -/
def rationalPrimeFactorizationPrimeSupport
    (x : ℚˣ) (p : Nat.Primes) : Finset Nat.Primes :=
  Finset.univ.map
    (rationalPrimeFactorizationSupportEmbedding x p)

/-- Membership in the prime-valued support is exactly membership of the
underlying natural number in the original support. -/
@[simp]
theorem mem_rationalPrimeFactorizationPrimeSupport_iff
    (x : ℚˣ) (p : Nat.Primes) (q : Nat.Primes) :
    q ∈ rationalPrimeFactorizationPrimeSupport x p ↔
      q.1 ∈ rationalPrimeFactorizationSupport x p := by
  constructor
  · intro hq
    obtain ⟨r, -, hr⟩ :=
      Finset.mem_map.mp hq
    rw [← hr]
    exact r.2
  · intro hq
    apply Finset.mem_map.mpr
    refine
      ⟨⟨q.1, hq⟩,
        Finset.mem_univ _,
        ?_⟩
    apply Subtype.ext
    rfl

/-- The distinguished prime belongs to the prime-valued support. -/
@[simp]
theorem mem_rationalPrimeFactorizationPrimeSupport
    (x : ℚˣ) (p : Nat.Primes) :
    p ∈ rationalPrimeFactorizationPrimeSupport x p :=
  (mem_rationalPrimeFactorizationPrimeSupport_iff x p p).2
    (mem_rationalPrimeFactorizationSupport x p)

/-- Erasing `p` commutes with passing from natural-number support to
prime-valued support. -/
@[simp]
theorem mem_rationalPrimeFactorizationPrimeSupport_erase_iff
    (x : ℚˣ) (p q : Nat.Primes) :
    q ∈ (rationalPrimeFactorizationPrimeSupport x p).erase p ↔
      q.1 ∈ (rationalPrimeFactorizationSupport x p).erase p.1 := by
  rw [Finset.mem_erase, Finset.mem_erase]
  constructor
  · rintro ⟨hqp, hq⟩
    exact
      ⟨fun hval => hqp (Subtype.ext hval),
        (mem_rationalPrimeFactorizationPrimeSupport_iff
          x p q).1 hq⟩
  · rintro ⟨hval, hq⟩
    exact
      ⟨fun hqp => hval (congrArg Subtype.val hqp),
        (mem_rationalPrimeFactorizationPrimeSupport_iff
          x p q).2 hq⟩

/-- The canonical prime associated with an element of the erased natural
support. -/
def rationalPrimeOfMemFactorizationSupportErase
    (x : ℚˣ) (p : Nat.Primes)
    (q : ↥((rationalPrimeFactorizationSupport x p).erase p.1)) :
    Nat.Primes :=
  ⟨q.1,
    prime_of_mem_rationalPrimeFactorizationSupport
      x p (Finset.mem_of_mem_erase q.2)⟩

/-- The erased natural support and the erased prime-valued support have
canonically equivalent element types. -/
def rationalPrimeFactorizationSupportEraseEquiv
    (x : ℚˣ) (p : Nat.Primes) :
    ↥((rationalPrimeFactorizationSupport x p).erase p.1) ≃
      ↥((rationalPrimeFactorizationPrimeSupport x p).erase p) where
  toFun q :=
    ⟨rationalPrimeOfMemFactorizationSupportErase x p q,
      (mem_rationalPrimeFactorizationPrimeSupport_erase_iff
        x p _).2 q.2⟩
  invFun q :=
    ⟨q.1.1,
      (mem_rationalPrimeFactorizationPrimeSupport_erase_iff
        x p q.1).1 q.2⟩
  left_inv q := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- A prime in the support with `p` erased is coprime to `p`. -/
theorem coprime_of_mem_rationalPrimeFactorizationSupport_erase
    (x : ℚˣ) (p : Nat.Primes) {q : ℕ}
    (hq :
      q ∈ (rationalPrimeFactorizationSupport x p).erase p.1) :
    p.1.Coprime q := by
  have hqprime :
      q.Prime :=
    prime_of_mem_rationalPrimeFactorizationSupport x p
      (Finset.mem_of_mem_erase hq)
  exact
    (Nat.coprime_primes p.2 hqprime).2
      (Finset.ne_of_mem_erase hq).symm

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_AddVal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Normalized additive valuations on discrete valuation rings

This file supplies general-purpose facts about Mathlib's normalized additive
valuation on a discrete valuation ring which are independent of any chosen
valued-field presentation.
-/

noncomputable section

universe u

namespace IsDiscreteValuationRing

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Membership in a power of the maximal ideal is detected by the normalized
additive valuation. -/
theorem mem_maximalIdeal_pow_iff_addVal_ge (a : R) (n : ℕ) :
    a ∈ IsLocalRing.maximalIdeal R ^ n ↔ (n : ℕ∞) ≤ addVal R a := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ← addVal_le_iff_dvd, hϖ.addVal_pow]

/-- A ring automorphism of a discrete valuation ring preserves its normalized
additive valuation. -/
@[simp] theorem addVal_ringEquiv (e : R ≃+* R) (a : R) :
    addVal R (e a) = addVal R a := by
  by_cases ha : a = 0
  · subst a
    simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, ha_decomp⟩ := eq_unit_mul_pow_irreducible ha hϖ
  have hmapϖ : Irreducible (e ϖ) := hϖ.map e
  have hmap_decomp :
      e a = (Units.map e.toMonoidHom u : R) * (e ϖ) ^ n := by
    rw [ha_decomp, map_mul, map_pow]
    rfl
  rw [addVal_def (e a) (Units.map e.toMonoidHom u) hmapϖ n hmap_decomp,
    addVal_def a u hϖ n ha_decomp]

end IsDiscreteValuationRing

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_CoefficientEquation
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Coefficient equations for a fixed uniformizer

For a positive degree, the scalar factor 1 - π ^ r is a unit whenever π
is a uniformizer. Consequently the corresponding scalar coefficient equation
has a unique solution in the valuation ring.
-/

noncomputable section

universe u v

namespace LubinTate
namespace SameUniformizer

variable {K : Type u} [Field K]

/-- Left multiplication by a unit has a unique preimage for every
right-hand side. -/
theorem existsUnique_mul_eq_of_isUnit
    {R : Type*} [CommRing R] {a : R} (ha : IsUnit a) (b : R) :
    ∃! x : R, a * x = b := by
  rcases ha with ⟨u, rfl⟩
  refine ⟨(↑(u⁻¹) : R) * b, by simp, ?_⟩
  intro y hy
  calc
    y = ((↑(u⁻¹) : R) * (u : R)) * y := by simp
    _ = (↑(u⁻¹) : R) * ((u : R) * y) := by rw [mul_assoc]
    _ = (↑(u⁻¹) : R) * b := by rw [hy]

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_PrimitiveUniformizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} [Field K]

theorem polynomial_eval₂_mem_ideal_of_coeff_mem
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (I : Ideal S) (P : Polynomial R) (z : S)
    (hcoeff : ∀ i, f (P.coeff i) ∈ I) :
    P.eval₂ f z ∈ I := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_right (z ^ i) I (hcoeff i)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_NormUniformizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Norm of a primitive standard Lubin--Tate point

The minimal polynomial of the chosen primitive level generator is the
standard Eisenstein polynomial, whose constant coefficient is the base
uniformizer.  The power-basis norm formula therefore gives
`N(-lambda) = pi`.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace LubinTate

variable {K : Type u} [Field K]

theorem algebraNorm_neg
    {R S : Type*} [Field R] [Field S] [Algebra R S] (x : S) :
    Algebra.norm R (-x) =
      (-1) ^ Module.finrank R S * Algebra.norm R x := by
  rw [show -x = algebraMap R S (-1) * x by simp]
  rw [map_mul, Algebra.norm_algebraMap]

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalPrincipalLocalUnit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The ramified local unit of a rational principal idele

For a nonzero rational number `x` and a rational prime `p`, removing the
`p`-power from `x` produces an actual `p`-adic unit.  This file identifies
that unit simultaneously in the height-one completion used by global
reciprocity, in the standard field `ℚ_[p]`, and in the valuation subring
used by the multiplicative Lubin--Tate construction.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance instFactPrimeValNat_solutions_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_SemilinearNaturality
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Semilinear naturality of finite local reciprocity

The actual finite local Artin map is natural when both the base local field
and the finite abelian extension are replaced by compatible field
equivalences.  The proof realizes the base equivalence as a degree-one
vertical extension and applies the genuine norm--restriction theorem.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel

/-- A base-field equivalence preserves the chosen valuations.  Keeping the
transported `Algebra` structure behind this opaque predicate prevents every
consumer of semilinear Artin naturality from storing a dependent `letI` in
its public theorem type. -/
def SemilinearValuationCompatible
    (K K' : Type)
    [Field K] [ValuativeRel K]
    [Field K'] [ValuativeRel K']
    (eK : K ≃+* K') : Prop :=
  letI : Algebra K K' := eK.toRingHom.toAlgebra
  (ValuativeRel.valuation K).HasExtension
    (ValuativeRel.valuation K')

/-- Conjugation of relative Galois groups by compatible equivalences of the
base and extension fields.  Compatibility is semilinear: `eL` restricts to
`eK` on the base field. -/
noncomputable def semilinearGaloisGroupCongr
    (K K' L L' : Type)
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomm : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x)) :
    Gal(L / K) ≃* Gal(L' / K') := by
  let conjugate (σ : Gal(L / K)) :
      Gal(L' / K') :=
    AlgEquiv.ofRingEquiv
      (f := eL.symm.trans (σ.toRingEquiv.trans eL))
      (fun x => by
        change
          eL (σ (eL.symm (algebraMap K' L' x))) =
            algebraMap K' L' x
        have hpre :
            eL.symm (algebraMap K' L' x) =
              algebraMap K L (eK.symm x) := by
          apply eL.injective
          rw [eL.apply_symm_apply, hcomm, eK.apply_symm_apply]
        rw [hpre, σ.commutes, hcomm, eK.apply_symm_apply])
  let unconjugate (τ : Gal(L' / K')) :
      Gal(L / K) :=
    AlgEquiv.ofRingEquiv
      (f := eL.trans (τ.toRingEquiv.trans eL.symm))
      (fun x => by
        change
          eL.symm (τ (eL (algebraMap K L x))) =
            algebraMap K L x
        rw [hcomm, τ.commutes, ← hcomm,
          eL.symm_apply_apply])
  refine
    { toFun := conjugate
      invFun := unconjugate
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · intro σ
    apply AlgEquiv.ext
    intro x
    simp [conjugate, unconjugate]
  · intro τ
    apply AlgEquiv.ext
    intro x
    simp [conjugate, unconjugate]
  · intro σ τ
    apply AlgEquiv.ext
    intro x
    simp [conjugate, AlgEquiv.mul_apply]

/-- Semilinear conjugation intertwines the two actions through the target
field equivalence. -/
@[simp]
theorem semilinearGaloisGroupCongr_apply_equiv
    (K K' L L' : Type)
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomm : ∀ x : K,
      eL (algebraMap K L x) =
        algebraMap K' L' (eK x))
    (σ : Gal(L / K)) (x : L) :
    semilinearGaloisGroupCongr K K' L L' eK eL hcomm σ (eL x) =
      eL (σ x) := by
  change eL (σ (eL.symm (eL x))) = eL (σ x)
  rw [eL.symm_apply_apply]

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_LinearTerm
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Prescribed linear terms for multivariable power series

A multivariable power series has a prescribed linear term when its difference
from the corresponding linear form has total order at least two.
-/

noncomputable section

namespace LubinTate
namespace SameUniformizer

variable {R : Type*} [CommRing R]
variable {σ : Type*} [Fintype σ]

/-- The multivariable linear form `sum_i L_i X_i`. -/
noncomputable def linearForm (L : σ → R) : MvPowerSeries σ R :=
  ∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i

/-- States the theorem `constantCoeff_linearForm`. -/
@[simp]
theorem constantCoeff_linearForm (L : σ → R) :
    MvPowerSeries.constantCoeff (linearForm L) = 0 := by
  simp [linearForm]

/-- A series has prescribed linear term `L` when its difference from
`sum_i L_i X_i` has total order at least two. -/
def HasLinearTerm (H : MvPowerSeries σ R) (L : σ → R) : Prop :=
  (2 : ℕ∞) ≤ (H - linearForm L).order

namespace HasLinearTerm

variable {H : MvPowerSeries σ R} {L : σ → R}

/-- A series with a prescribed linear term has zero constant
coefficient. -/
theorem constantCoeff_eq_zero (h : HasLinearTerm H L) :
    MvPowerSeries.constantCoeff H = 0 := by
  have horder : (1 : ℕ∞) ≤ (H - linearForm L).order :=
    (by norm_num : (1 : ℕ∞) ≤ 2).trans h
  have hconstant :=
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp horder
  simpa using hconstant

/-- Consequently the series can genuinely be substituted into a
one-variable power series. -/
theorem hasSubst (h : HasLinearTerm H L) :
    PowerSeries.HasSubst H :=
  PowerSeries.HasSubst.of_constantCoeff_zero h.constantCoeff_eq_zero

end HasLinearTerm

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_Reduction
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Reduction of a Lubin--Tate intertwining defect

After reduction to the finite residue field, both series become the Frobenius
power series. The two sides of the intertwining equation then agree, so every
coefficient of the defect is divisible by the chosen uniformizer.
-/

noncomputable section

universe u v w

namespace LubinTate
namespace SameUniformizer

/-- Multivariable finite-field Frobenius: replacing each variable by its
`q`th power is the same as taking the `q`th power of the whole series. -/
theorem mvPowerSeries_expand_natCard
    {k : Type u} [Field k] [Finite k]
    {σ : Type w} [Finite σ] (f : MvPowerSeries σ k) :
    MvPowerSeries.expand (Nat.card k) (Nat.ne_of_gt Nat.card_pos) f =
      f ^ Nat.card k := by
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases FiniteField.card k p with ⟨⟨n, npos⟩, ⟨hpprime, hn⟩⟩
  let : Fact p.Prime := ⟨hpprime⟩
  have hncard : Fintype.card k = p ^ n := by
    simpa using hn
  have hn' : Nat.card k = p ^ n := by
    simpa only [Nat.card_eq_fintype_card] using hncard
  have hpow :
      MvPowerSeries.expand (p ^ n) (pow_ne_zero n hpprime.ne_zero) f =
        f ^ (p ^ n) := by
    rw [← MvPowerSeries.map_iterateFrobenius_expand,
      iterateFrobenius_eq_pow, FiniteField.frobenius_pow hncard,
      RingHom.one_def, MvPowerSeries.map_id]
    · rfl
    · exact hpprime.ne_zero
  simpa only [hn'] using hpow

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_DegreeStabilization
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Finite-degree stabilization for Lubin--Tate intertwining defects

The coefficient of an intertwining defect in total degree at most `m`
depends only on the coefficients of the proposed intertwiner in total degree
at most `m`.  This is the finite-degree continuity statement needed to pass
from recursively corrected finite approximations to one full multivariable
power series.

The proof uses total-degree truncation.  On the left side of the
intertwining equation, truncation commutes with substituting a series with
zero constant coefficient into the fixed Lubin--Tate series.  On the right
side, truncation of multivariable substitution depends only on the same
truncation of the outer series.
-/

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u v w

namespace LubinTate
namespace SameUniformizer

/-- Equality of total-degree truncations through degree `m` is equivalent to
coefficientwise equality in every total degree at most `m`. -/
theorem truncTotal_succ_eq_iff_coeff_eq_degree_le
    {R : Type*} [CommSemiring R]
    {τ : Type*} [Finite τ]
    {H H' : MvPowerSeries τ R} (m : ℕ) :
    H.truncTotal (m + 1) = H'.truncTotal (m + 1) ↔
      ∀ d : τ →₀ ℕ, d.degree ≤ m →
        MvPowerSeries.coeff d H = MvPowerSeries.coeff d H' := by
  constructor
  · intro h d hd
    have hd' : d.degree < m + 1 := Nat.lt_succ_iff.mpr hd
    calc
      MvPowerSeries.coeff d H =
          (H.truncTotal (m + 1)).coeff d :=
        (MvPowerSeries.coeff_truncTotal H hd').symm
      _ = (H'.truncTotal (m + 1)).coeff d := by rw [h]
      _ = MvPowerSeries.coeff d H' :=
        MvPowerSeries.coeff_truncTotal H' hd'
  · intro h
    ext d
    by_cases hd : d.degree < m + 1
    · rw [MvPowerSeries.coeff_truncTotal H hd,
        MvPowerSeries.coeff_truncTotal H' hd]
      exact h d (Nat.lt_succ_iff.mp hd)
    · rw [MvPowerSeries.coeff_truncTotal_eq_zero H (not_lt.mp hd),
        MvPowerSeries.coeff_truncTotal_eq_zero H' (not_lt.mp hd)]

variable {K : Type u} [Field K]
variable {σ : Type w} [Fintype σ]

theorem degree_le_order_monomial_stabilization
    {R : Type*} [CommRing R] {τ : Type*}
    (d : τ →₀ ℕ) (c : R) :
    (d.degree : ℕ∞) ≤ (MvPowerSeries.monomial d c).order := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  · rw [MvPowerSeries.order_monomial_of_ne_zero hc]

theorem natCast_le_order_pow_of_one_le_order_stabilization
    {R : Type*} [CommRing R] {τ : Type*}
    (f : MvPowerSeries τ R) (n : ℕ)
    (hf : (1 : ℕ∞) ≤ f.order) :
    (n : ℕ∞) ≤ (f ^ n).order := by
  calc
    (n : ℕ∞) = n • (1 : ℕ∞) := by simp
    _ ≤ n • f.order := nsmul_le_nsmul_right hf n
    _ ≤ (f ^ n).order := MvPowerSeries.le_order_pow n

theorem le_order_finset_sum_stabilization
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι} {f : ι → MvPowerSeries τ R} {m : ℕ∞}
    (h : ∀ i ∈ s, m ≤ (f i).order) :
    m ≤ (∑ i ∈ s, f i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact
        (le_min
          (h i (Finset.mem_insert_self i s))
          (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).trans
        MvPowerSeries.min_order_le_add

theorem natCast_sum_le_order_finset_prod_pow_stabilization
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι} (f : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order) :
    ((∑ i ∈ s, n i : ℕ) : ℕ∞) ≤
      (∏ i ∈ s, (f i) ^ n i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      calc
        ((n i + ∑ j ∈ s, n j : ℕ) : ℕ∞) =
            (n i : ℕ∞) + ((∑ j ∈ s, n j : ℕ) : ℕ∞) := by
          norm_cast
        _ ≤ ((f i) ^ n i).order +
            (∏ j ∈ s, (f j) ^ n j).order :=
          add_le_add
            (natCast_le_order_pow_of_one_le_order_stabilization
              (f i) (n i) (hf i (Finset.mem_insert_self i s)))
            (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
        _ ≤ ((f i) ^ n i * ∏ j ∈ s, (f j) ^ n j).order :=
          MvPowerSeries.le_order_mul

theorem order_sub_add_pred_le_order_pow_sub_pow_stabilization
    {R : Type*} [CommRing R] {τ : Type*}
    (f g : MvPowerSeries τ R)
    (hf : (1 : ℕ∞) ≤ f.order)
    (hg : (1 : ℕ∞) ≤ g.order)
    (n : ℕ) :
    (f - g).order + ((n - 1 : ℕ) : ℕ∞) ≤
      (f ^ n - g ^ n).order := by
  let q :=
    ∑ i ∈ Finset.range n, f ^ i * g ^ (n - 1 - i)
  have hq : ((n - 1 : ℕ) : ℕ∞) ≤ q.order := by
    apply le_order_finset_sum_stabilization
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    calc
      ((n - 1 : ℕ) : ℕ∞) =
          (i : ℕ∞) + ((n - 1 - i : ℕ) : ℕ∞) := by
        norm_cast
        omega
      _ ≤ (f ^ i).order + (g ^ (n - 1 - i)).order :=
        add_le_add
          (natCast_le_order_pow_of_one_le_order_stabilization f i hf)
          (natCast_le_order_pow_of_one_le_order_stabilization
            g (n - 1 - i) hg)
      _ ≤ (f ^ i * g ^ (n - 1 - i)).order :=
        MvPowerSeries.le_order_mul
  have hfactor :
      (f - g) * q = f ^ n - g ^ n := by
    exact (Commute.all f g).mul_geom_sum₂ n
  calc
    (f - g).order + ((n - 1 : ℕ) : ℕ∞) ≤
        (f - g).order + q.order :=
      add_le_add_right hq _
    _ ≤ ((f - g) * q).order :=
      MvPowerSeries.le_order_mul
    _ = (f ^ n - g ^ n).order :=
      congrArg (fun h : MvPowerSeries τ R => h.order) hfactor

theorem natCast_sum_add_one_le_order_prod_pow_sub_prod_pow_stabilization
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι}
    (f g : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (hn : ∀ i ∈ s, n i ≠ 0)
    (hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order)
    (hg : ∀ i ∈ s, (1 : ℕ∞) ≤ (g i).order)
    (hfg : ∀ i ∈ s, (2 : ℕ∞) ≤ (f i - g i).order) :
    (((∑ i ∈ s, n i) + 1 : ℕ) : ℕ∞) ≤
      ((∏ i ∈ s, (f i) ^ n i) -
        ∏ i ∈ s, (g i) ^ n i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hni : n i ≠ 0 :=
        hn i (Finset.mem_insert_self i s)
      have hpowDifference :
          ((n i + 1 : ℕ) : ℕ∞) ≤
            ((f i) ^ n i - (g i) ^ n i).order := by
        calc
          ((n i + 1 : ℕ) : ℕ∞) =
              (2 : ℕ∞) + ((n i - 1 : ℕ) : ℕ∞) := by
            norm_cast
            omega
          _ ≤ (f i - g i).order +
              ((n i - 1 : ℕ) : ℕ∞) :=
            add_le_add_left
              (hfg i (Finset.mem_insert_self i s)) _
          _ ≤ ((f i) ^ n i - (g i) ^ n i).order :=
            order_sub_add_pred_le_order_pow_sub_pow_stabilization
              (f i) (g i)
              (hf i (Finset.mem_insert_self i s))
              (hg i (Finset.mem_insert_self i s))
              (n i)
      have hprodF :
          ((∑ j ∈ s, n j : ℕ) : ℕ∞) ≤
            (∏ j ∈ s, (f j) ^ n j).order :=
        natCast_sum_le_order_finset_prod_pow_stabilization f n
          (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hpowG :
          (n i : ℕ∞) ≤ ((g i) ^ n i).order :=
        natCast_le_order_pow_of_one_le_order_stabilization
          (g i) (n i) (hg i (Finset.mem_insert_self i s))
      have hprodDifference :
          (((∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            ((∏ j ∈ s, (f j) ^ n j) -
              ∏ j ∈ s, (g j) ^ n j).order :=
        ih
          (fun j hj => hn j (Finset.mem_insert_of_mem hj))
          (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
          (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
      have hleft :
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            (((f i) ^ n i - (g i) ^ n i) *
              ∏ j ∈ s, (f j) ^ n j).order := by
        calc
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) =
              ((n i + 1 : ℕ) : ℕ∞) +
                ((∑ j ∈ s, n j : ℕ) : ℕ∞) := by
            norm_cast
            omega
          _ ≤ ((f i) ^ n i - (g i) ^ n i).order +
              (∏ j ∈ s, (f j) ^ n j).order :=
            add_le_add hpowDifference hprodF
          _ ≤ (((f i) ^ n i - (g i) ^ n i) *
              ∏ j ∈ s, (f j) ^ n j).order :=
            MvPowerSeries.le_order_mul
      have hright :
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            ((g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j)).order := by
        calc
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) =
              (n i : ℕ∞) +
                (((∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) := by
            norm_cast
          _ ≤ ((g i) ^ n i).order +
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j).order :=
            add_le_add hpowG hprodDifference
          _ ≤ ((g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j)).order :=
            MvPowerSeries.le_order_mul
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        Finset.prod_insert hi]
      rw [show
        (f i) ^ n i * (∏ j ∈ s, (f j) ^ n j) -
            (g i) ^ n i * (∏ j ∈ s, (g j) ^ n j) =
          ((f i) ^ n i - (g i) ^ n i) *
              (∏ j ∈ s, (f j) ^ n j) +
            (g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j) by ring]
      exact
        (le_min hleft hright).trans
          MvPowerSeries.min_order_le_add

theorem constantCoeff_monomial_eq_zero_stabilization
    {R : Type*} [CommRing R] {τ : Type*}
    {d : τ →₀ ℕ} (hd : d ≠ 0) (c : R) :
    MvPowerSeries.constantCoeff (MvPowerSeries.monomial d c) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_monomial_ne]
  exact Ne.symm hd

theorem coeff_pow_add_monomial_sub_pow_of_degree_le
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (q d : τ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (hd : 1 ≤ d.degree) (c : R) (n : ℕ) :
    MvPowerSeries.coeff q
        ((H + MvPowerSeries.monomial d c) ^ n - H ^ n) =
      if n = 1 then (if q = d then c else 0) else 0 := by
  classical
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    simp at hd
  by_cases hn : n = 1
  · subst n
    simp [MvPowerSeries.coeff_monomial]
  · rcases n with _ | n
    · simp
    · have hn0 : n ≠ 0 := by
        intro h
        apply hn
        omega
      let M := MvPowerSeries.monomial d c
      let A := H + M
      have hMconstant :
          MvPowerSeries.constantCoeff M = 0 :=
        constantCoeff_monomial_eq_zero_stabilization hd0 c
      have hAconstant :
          MvPowerSeries.constantCoeff A = 0 := by
        simp [A, hH, hMconstant]
      have hHorder : (1 : ℕ∞) ≤ H.order :=
        MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hH
      have hAorder : (1 : ℕ∞) ≤ A.order :=
        MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hAconstant
      have hpow :
          M.order + (n : ℕ∞) ≤
            (A ^ (n + 1) - H ^ (n + 1)).order := by
        simpa [A, M, add_sub_cancel_left] using
          order_sub_add_pred_le_order_pow_sub_pow_stabilization
            A H hAorder hHorder (n + 1)
      have hdegree : (d.degree : ℕ∞) ≤ M.order :=
        degree_le_order_monomial_stabilization d c
      have hn' : (1 : ℕ∞) ≤ (n : ℕ∞) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have horder :
          ((d.degree + 1 : ℕ) : ℕ∞) ≤
            (A ^ (n + 1) - H ^ (n + 1)).order := by
        calc
          ((d.degree + 1 : ℕ) : ℕ∞) =
              (d.degree : ℕ∞) + 1 := by norm_cast
          _ ≤ M.order + (n : ℕ∞) :=
            add_le_add hdegree hn'
          _ ≤ (A ^ (n + 1) - H ^ (n + 1)).order :=
            hpow
      have hlt :
          (q.degree : ℕ∞) <
            (A ^ (n + 1) - H ^ (n + 1)).order :=
        by
          have hqNat : q.degree < d.degree + 1 :=
            Nat.lt_succ_of_le hq
          have hqCast :
              (q.degree : ℕ∞) <
                ((d.degree + 1 : ℕ) : ℕ∞) := by
            exact_mod_cast hqNat
          exact hqCast.trans_le horder
      have hzero := MvPowerSeries.coeff_of_lt_order hlt
      simpa [A, M, hn, hn0] using hzero

theorem coeff_pow_add_monomial_of_degree_le
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (q d : τ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (hd : 1 ≤ d.degree) (c : R) (n : ℕ) :
    MvPowerSeries.coeff q
        ((H + MvPowerSeries.monomial d c) ^ n) =
      MvPowerSeries.coeff q (H ^ n) +
        if n = 1 then (if q = d then c else 0) else 0 := by
  have h :=
    coeff_pow_add_monomial_sub_pow_of_degree_le
      hH q d hq hd c n
  rw [map_sub, sub_eq_iff_eq_add] at h
  simpa [add_comm] using h

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_RecursiveCorrection
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Recursive monomial corrections for Lubin--Tate intertwiners

The coefficient selected in `RecursiveCoefficient` is inserted as a single
monomial.  This file proves that the insertion preserves the prescribed linear
term and cancels the defect coefficient in precisely that total degree.
-/

noncomputable section

open scoped BigOperators

universe u v w

namespace LubinTate
namespace SameUniformizer

variable {K : Type u} [Field K]
variable {σ : Type w} [Fintype σ]

theorem degree_le_order_monomial
    {R : Type*} [CommRing R] {τ : Type*}
    (d : τ →₀ ℕ) (c : R) :
    (d.degree : ℕ∞) ≤ (MvPowerSeries.monomial d c).order := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  · rw [MvPowerSeries.order_monomial_of_ne_zero hc]

theorem natCast_le_order_pow_of_one_le_order
    {R : Type*} [CommRing R] {τ : Type*}
    (f : MvPowerSeries τ R) (n : ℕ)
    (hf : (1 : ℕ∞) ≤ f.order) :
    (n : ℕ∞) ≤ (f ^ n).order := by
  calc
    (n : ℕ∞) = n • (1 : ℕ∞) := by simp
    _ ≤ n • f.order := nsmul_le_nsmul_right hf n
    _ ≤ (f ^ n).order := MvPowerSeries.le_order_pow n

theorem le_order_finset_sum
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι} {f : ι → MvPowerSeries τ R} {m : ℕ∞}
    (h : ∀ i ∈ s, m ≤ (f i).order) :
    m ≤ (∑ i ∈ s, f i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact
        (le_min
          (h i (Finset.mem_insert_self i s))
          (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).trans
        MvPowerSeries.min_order_le_add

theorem natCast_sum_le_order_finset_prod_pow
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι} (f : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order) :
    ((∑ i ∈ s, n i : ℕ) : ℕ∞) ≤
      (∏ i ∈ s, (f i) ^ n i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      calc
        ((n i + ∑ j ∈ s, n j : ℕ) : ℕ∞) =
            (n i : ℕ∞) + ((∑ j ∈ s, n j : ℕ) : ℕ∞) := by
          norm_cast
        _ ≤ ((f i) ^ n i).order +
            (∏ j ∈ s, (f j) ^ n j).order :=
          add_le_add
            (natCast_le_order_pow_of_one_le_order
              (f i) (n i) (hf i (Finset.mem_insert_self i s)))
            (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
        _ ≤ ((f i) ^ n i * ∏ j ∈ s, (f j) ^ n j).order :=
          MvPowerSeries.le_order_mul

theorem order_sub_add_pred_le_order_pow_sub_pow
    {R : Type*} [CommRing R] {τ : Type*}
    (f g : MvPowerSeries τ R)
    (hf : (1 : ℕ∞) ≤ f.order)
    (hg : (1 : ℕ∞) ≤ g.order)
    (n : ℕ) :
    (f - g).order + ((n - 1 : ℕ) : ℕ∞) ≤
      (f ^ n - g ^ n).order := by
  let q :=
    ∑ i ∈ Finset.range n, f ^ i * g ^ (n - 1 - i)
  have hq : ((n - 1 : ℕ) : ℕ∞) ≤ q.order := by
    apply le_order_finset_sum
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    calc
      ((n - 1 : ℕ) : ℕ∞) =
          (i : ℕ∞) + ((n - 1 - i : ℕ) : ℕ∞) := by
        norm_cast
        omega
      _ ≤ (f ^ i).order + (g ^ (n - 1 - i)).order :=
        add_le_add
          (natCast_le_order_pow_of_one_le_order f i hf)
          (natCast_le_order_pow_of_one_le_order
            g (n - 1 - i) hg)
      _ ≤ (f ^ i * g ^ (n - 1 - i)).order :=
        MvPowerSeries.le_order_mul
  have hfactor :
      (f - g) * q = f ^ n - g ^ n := by
    exact (Commute.all f g).mul_geom_sum₂ n
  calc
    (f - g).order + ((n - 1 : ℕ) : ℕ∞) ≤
        (f - g).order + q.order :=
      add_le_add (le_refl _) hq
    _ ≤ ((f - g) * q).order :=
      MvPowerSeries.le_order_mul
    _ = (f ^ n - g ^ n).order :=
      congrArg (fun h : MvPowerSeries τ R => h.order) hfactor

theorem natCast_sum_add_one_le_order_prod_pow_sub_prod_pow
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι}
    (f g : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (hn : ∀ i ∈ s, n i ≠ 0)
    (hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order)
    (hg : ∀ i ∈ s, (1 : ℕ∞) ≤ (g i).order)
    (hfg : ∀ i ∈ s, (2 : ℕ∞) ≤ (f i - g i).order) :
    (((∑ i ∈ s, n i) + 1 : ℕ) : ℕ∞) ≤
      ((∏ i ∈ s, (f i) ^ n i) -
        ∏ i ∈ s, (g i) ^ n i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hni : n i ≠ 0 :=
        hn i (Finset.mem_insert_self i s)
      have hpowDifference :
          ((n i + 1 : ℕ) : ℕ∞) ≤
            ((f i) ^ n i - (g i) ^ n i).order := by
        calc
          ((n i + 1 : ℕ) : ℕ∞) =
              (2 : ℕ∞) + ((n i - 1 : ℕ) : ℕ∞) := by
            norm_cast
            omega
          _ ≤ (f i - g i).order +
              ((n i - 1 : ℕ) : ℕ∞) :=
            add_le_add
              (hfg i (Finset.mem_insert_self i s)) (le_refl _)
          _ ≤ ((f i) ^ n i - (g i) ^ n i).order :=
            order_sub_add_pred_le_order_pow_sub_pow
              (f i) (g i)
              (hf i (Finset.mem_insert_self i s))
              (hg i (Finset.mem_insert_self i s))
              (n i)
      have hprodF :
          ((∑ j ∈ s, n j : ℕ) : ℕ∞) ≤
            (∏ j ∈ s, (f j) ^ n j).order :=
        natCast_sum_le_order_finset_prod_pow f n
          (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hpowG :
          (n i : ℕ∞) ≤ ((g i) ^ n i).order :=
        natCast_le_order_pow_of_one_le_order
          (g i) (n i) (hg i (Finset.mem_insert_self i s))
      have hprodDifference :
          (((∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            ((∏ j ∈ s, (f j) ^ n j) -
              ∏ j ∈ s, (g j) ^ n j).order :=
        ih
          (fun j hj => hn j (Finset.mem_insert_of_mem hj))
          (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
          (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
      have hleft :
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            (((f i) ^ n i - (g i) ^ n i) *
              ∏ j ∈ s, (f j) ^ n j).order := by
        calc
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) =
              ((n i + 1 : ℕ) : ℕ∞) +
                ((∑ j ∈ s, n j : ℕ) : ℕ∞) := by
            norm_cast
            omega
          _ ≤ ((f i) ^ n i - (g i) ^ n i).order +
              (∏ j ∈ s, (f j) ^ n j).order :=
            add_le_add hpowDifference hprodF
          _ ≤ (((f i) ^ n i - (g i) ^ n i) *
              ∏ j ∈ s, (f j) ^ n j).order :=
            MvPowerSeries.le_order_mul
      have hright :
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            ((g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j)).order := by
        calc
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) =
              (n i : ℕ∞) +
                (((∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) := by
            norm_cast
          _ ≤ ((g i) ^ n i).order +
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j).order :=
            add_le_add hpowG hprodDifference
          _ ≤ ((g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j)).order :=
            MvPowerSeries.le_order_mul
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        Finset.prod_insert hi]
      rw [show
        (f i) ^ n i * (∏ j ∈ s, (f j) ^ n j) -
            (g i) ^ n i * (∏ j ∈ s, (g j) ^ n j) =
          ((f i) ^ n i - (g i) ^ n i) *
              (∏ j ∈ s, (f j) ^ n j) +
            (g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j) by ring]
      exact
        (le_min hleft hright).trans
          MvPowerSeries.min_order_le_add

theorem constantCoeff_monomial_eq_zero
    {R : Type*} [CommRing R] {τ : Type*}
    {d : τ →₀ ℕ} (hd : d ≠ 0) (c : R) :
    MvPowerSeries.constantCoeff (MvPowerSeries.monomial d c) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_monomial_ne]
  exact Ne.symm hd

theorem coeff_pow_add_monomial_sub_pow
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (d : τ →₀ ℕ) (hd : 2 ≤ d.degree) (c : R) (n : ℕ) :
    MvPowerSeries.coeff d
        ((H + MvPowerSeries.monomial d c) ^ n - H ^ n) =
      if n = 1 then c else 0 := by
  classical
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    simp at hd
  by_cases hn : n = 1
  · subst n
    simp [MvPowerSeries.coeff_monomial_same]
  · rcases n with _ | n
    · simp
    · have hn0 : n ≠ 0 := by
        intro h
        apply hn
        omega
      let M := MvPowerSeries.monomial d c
      let A := H + M
      have hMconstant :
          MvPowerSeries.constantCoeff M = 0 :=
        constantCoeff_monomial_eq_zero hd0 c
      have hAconstant :
          MvPowerSeries.constantCoeff A = 0 := by
        simp [A, hH, hMconstant]
      have hHorder : (1 : ℕ∞) ≤ H.order :=
        MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hH
      have hAorder : (1 : ℕ∞) ≤ A.order :=
        MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hAconstant
      have hpow :
          M.order + (n : ℕ∞) ≤
            (A ^ (n + 1) - H ^ (n + 1)).order := by
        simpa [A, M, add_sub_cancel_left] using
          order_sub_add_pred_le_order_pow_sub_pow
            A H hAorder hHorder (n + 1)
      have hdegree : (d.degree : ℕ∞) ≤ M.order :=
        degree_le_order_monomial d c
      have hn' : (1 : ℕ∞) ≤ (n : ℕ∞) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have horder :
          ((d.degree + 1 : ℕ) : ℕ∞) ≤
            (A ^ (n + 1) - H ^ (n + 1)).order := by
        calc
          ((d.degree + 1 : ℕ) : ℕ∞) =
              (d.degree : ℕ∞) + 1 := by norm_cast
          _ ≤ M.order + (n : ℕ∞) :=
            add_le_add hdegree hn'
          _ ≤ (A ^ (n + 1) - H ^ (n + 1)).order :=
            hpow
      have hlt :
          (d.degree : ℕ∞) <
            (A ^ (n + 1) - H ^ (n + 1)).order :=
        by
          have hdegree_lt :
              (d.degree : ℕ∞) < ((d.degree + 1 : ℕ) : ℕ∞) := by
            exact_mod_cast Nat.lt_succ_self d.degree
          exact hdegree_lt.trans_le horder
      have hzero := MvPowerSeries.coeff_of_lt_order hlt
      simpa [A, M, hn0] using hzero

theorem coeff_pow_add_monomial
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (d : τ →₀ ℕ) (hd : 2 ≤ d.degree) (c : R) (n : ℕ) :
    MvPowerSeries.coeff d
        ((H + MvPowerSeries.monomial d c) ^ n) =
      MvPowerSeries.coeff d (H ^ n) +
        if n = 1 then c else 0 := by
  have h :=
    coeff_pow_add_monomial_sub_pow hH d hd c n
  rw [map_sub, sub_eq_iff_eq_add] at h
  simpa [add_comm] using h

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_RecursiveIntertwiner
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Finite-degree approximations to Lubin--Tate intertwiners

For a fixed total degree there are only finitely many monomials.  This file
orders those monomials, applies the coefficient correction from
`RecursiveCorrection` one at a time, and then iterates the resulting
degreewise correction.

The construction is genuinely recursive: stage `n + 1` corrects every
monomial of total degree `n + 2`.  Corrections in that degree leave all lower
coefficients unchanged.  The stabilized coefficient series and its
intertwining equation are established below after the finite-degree
construction.
-/

noncomputable section

universe u v w

namespace LubinTate
namespace SameUniformizer

variable {K : Type u} [Field K]
variable {sigma : Type w} [Fintype sigma]

/-- The finite list of all monomials of a fixed total degree. -/
noncomputable def degreeIndexList (m : ℕ) :
    List {d : sigma →₀ ℕ // d.degree = m} :=
  letI : Fintype {d : sigma →₀ ℕ // d.degree = m} :=
    (Finsupp.finite_of_degree_eq m).fintype
  Finset.univ.toList

theorem degreeIndexList_nodup (m : ℕ) :
    (degreeIndexList (sigma := sigma) m).Nodup := by
  classical
  simp [degreeIndexList, Finset.nodup_toList]

theorem mem_degreeIndexList
    (m : ℕ) (d : {d : sigma →₀ ℕ // d.degree = m}) :
    d ∈ degreeIndexList (sigma := sigma) m := by
  classical
  simp [degreeIndexList]

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_Polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Hilbert ramification theory: polynomial sources

This file contains the generic polynomial congruence lemma used by the
completion-free formalization of ramification-number theory.
-/

namespace RamificationTheory.HilbertRamification
namespace Higher

/-- If two evaluation points are congruent modulo an ideal, then evaluating
any polynomial at them gives congruent results modulo the same ideal. -/
theorem polynomial_eval₂_sub_mem_of_sub_mem
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal S) {x y : S} (hxy : x - y ∈ I)
    (P : Polynomial R) :
    P.eval₂ f x - P.eval₂ f y ∈ I := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Polynomial.eval₂_add, Polynomial.eval₂_add]
      have hsum : (P.eval₂ f x - P.eval₂ f y) +
          (Q.eval₂ f x - Q.eval₂ f y) ∈ I :=
        Ideal.add_mem I hP hQ
      convert hsum using 1
      all_goals try with_reducible_and_instances rfl
      ring
  | monomial n a =>
      rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial]
      have hpow : x ^ n - y ^ n ∈ I := by
        rcases sub_dvd_pow_sub_pow x y n with ⟨c, hc⟩
        rw [hc]
        exact Ideal.mul_mem_right c I hxy
      have hrewrite : f a * x ^ n - f a * y ^ n =
          f a * (x ^ n - y ^ n) := by
        ring
      rw [hrewrite]
      exact Ideal.mul_mem_left I (f a) hpow

end Higher
end RamificationTheory.HilbertRamification
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_PrimitiveDisplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField

variable {K : Type u} [Field K]

section FormalFactors

theorem coeff_subst_X_zero
    {R : Type*} [CommRing R]
    (f : MvPowerSeries (Fin 2) R) (d : Fin 2 →₀ ℕ)
    (hd : d 1 = 0) :
    PowerSeries.coeff (d 0)
        (MvPowerSeries.subst
          ![(PowerSeries.X : PowerSeries R), 0] f) =
      MvPowerSeries.coeff d f := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst,
    finsum_eq_single _ d]
  · simp [hd, PowerSeries.coeff_X_pow]
  · intro e hed
    by_cases he : e 1 = 0
    · have he0 : e 0 ≠ d 0 := by
        intro he0
        apply hed
        ext i
        fin_cases i
        · exact he0
        · exact he.trans hd.symm
      simp [he, PowerSeries.coeff_X_pow, he0.symm]
    · simp [he]
  · exact MvPowerSeries.HasSubst.X_zero

end FormalFactors

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_Herbrand_Tower
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Finite-group sources for Herbrand's theorem

This file isolates the part of the Herbrand quotient theorem which is
independent of valuations.  A discrete nonarchimedean depth has the two
properties of `i(σ) = v(σ(a) - a)` used in the ramification-depth proof: multiplication
does not decrease the minimum depth, and it is exactly the minimum when the
two depths differ.

For a finite group modulo a normal subgroup, every nontrivial quotient fibre
has a representative of maximal (finite) depth.  The main result below proves
the identity

`i(σ τ) = min (i(σ), i(τ))`

for such a representative `σ` and every `τ` in the normal subgroup.  The
remaining valued-field input for the Herbrand quotient theorem is the quotient-depth identity: the depth
on the quotient is the normalized sum of the depths in this fibre.  That
input is deliberately not packaged here as a hypothesis or data field.
-/

noncomputable section

universe u

namespace RamificationTheory.DiscreteValuationField
namespace HerbrandGroupTheory

variable {G : Type u} [Group G]

/-- The purely group-theoretic laws of the discrete depth used in the proof
of Herbrand's theorem.  The value `⊤` occurs exactly at the identity. -/
structure NonarchimedeanDepth (G : Type u) [Group G] where
  /-- The discrete nonarchimedean depth of each group element. -/
  depth : G → WithTop ℕ
  /-- An element has infinite depth exactly when it is the identity. -/
  depth_eq_top_iff : ∀ σ, depth σ = ⊤ ↔ σ = 1
  /-- The depth of a product is at least the minimum depth of its factors. -/
  depth_mul_ge_min : ∀ σ τ, min (depth σ) (depth τ) ≤ depth (σ * τ)
  /-- Factors of unequal depth give a product whose depth is their minimum. -/
  depth_mul_eq_min_of_ne :
    ∀ {σ τ}, depth σ ≠ depth τ → depth (σ * τ) = min (depth σ) (depth τ)
  /-- Depth is invariant under conjugation. -/
  depth_conj : ∀ γ σ, depth (γ * σ * γ⁻¹) = depth σ

namespace NonarchimedeanDepth

variable (D : NonarchimedeanDepth G)

/-- States the theorem `depth_one`. -/
@[simp] theorem depth_one : D.depth 1 = ⊤ :=
  (D.depth_eq_top_iff 1).2 rfl

end NonarchimedeanDepth
end HerbrandGroupTheory
end RamificationTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Topology_AdicContractingFixedPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Fixed points of adically contracting additive maps

An additive endomorphism which sends `I ^ n` into `I ^ (n + 1)` is
topologically nilpotent for the `I`-adic topology.  Completeness therefore
solves the affine fixed-point equation

`x = b + T x`

uniquely.  The proof uses the successive approximations
`x₀ = 0`, `xₙ₊₁ = b + T xₙ` and mathlib's `IsPrecomplete.prec`.
-/

namespace IsAdicComplete

variable {R : Type*} [CommRing R]

def contractingApproximation
    (T : R →+ R) (b : R) : ℕ → R
  | 0 => 0
  | n + 1 => b + T (contractingApproximation T b n)

theorem contractingApproximation_succ
    (T : R →+ R) (b : R) (n : ℕ) :
    contractingApproximation T b (n + 1) =
      b + T (contractingApproximation T b n) :=
  rfl

theorem ideal_smul_top_eq_self (J : Ideal R) :
    J • (⊤ : Submodule R R) = (J : Submodule R R) := by
  rw [Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id,
    Submodule.restrictScalars_self]

theorem map_smodEq_pow_succ
    (I : Ideal R) (T : R →+ R)
    (hT : ∀ (n : ℕ) {x : R}, x ∈ I ^ n → T x ∈ I ^ (n + 1))
    (n : ℕ) {x y : R}
    (hxy : x ≡ y [SMOD (I ^ n : Ideal R)]) :
    T x ≡ T y [SMOD (I ^ (n + 1) : Ideal R)] := by
  rw [SModEq.sub_mem, ← T.map_sub]
  exact hT n ((SModEq.sub_mem).1 hxy)

theorem contractingApproximation_sub_mem_pow
    (I : Ideal R) (T : R →+ R)
    (hT : ∀ (n : ℕ) {x : R}, x ∈ I ^ n → T x ∈ I ^ (n + 1))
    (b : R) :
    ∀ n, contractingApproximation T b n -
      contractingApproximation T b (n + 1) ∈ I ^ n := by
  intro n
  induction n with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      exact (Submodule.mem_top :
        contractingApproximation T b 0 -
          contractingApproximation T b (0 + 1) ∈ (⊤ : Ideal R))
  | succ n ih =>
      simpa only [contractingApproximation_succ,
        add_sub_add_left_eq_sub, ← T.map_sub] using hT n ih

theorem contractingApproximation_limit_is_fixed
    (I : Ideal R) [IsHausdorff I R]
    (T : R →+ R)
    (hT : ∀ (n : ℕ) {x : R}, x ∈ I ^ n → T x ∈ I ^ (n + 1))
    (b a : R)
    (ha : ∀ n, contractingApproximation T b n ≡
      a [SMOD (I ^ n : Ideal R)]) :
    a = b + T a := by
  apply (IsHausdorff.eq_iff_smodEq (I := I)).2
  intro n
  rw [ideal_smul_top_eq_self]
  have hpow :
      (I ^ (n + 1) : Ideal R) ≤ I ^ n :=
    Ideal.pow_le_pow_right (Nat.le_succ n)
  have haleft :
      a ≡ contractingApproximation T b (n + 1)
        [SMOD (I ^ n : Ideal R)] :=
    SModEq.mono hpow (ha (n + 1)).symm
  have hTcongr :
      T (contractingApproximation T b n) ≡ T a
        [SMOD (I ^ (n + 1) : Ideal R)] :=
    map_smodEq_pow_succ I T hT n (ha n)
  have haright :
      contractingApproximation T b (n + 1) ≡ b + T a
        [SMOD (I ^ n : Ideal R)] := by
    apply SModEq.mono hpow
    simpa only [contractingApproximation_succ] using
      SModEq.add
        (SModEq.rfl :
          b ≡ b [SMOD (I ^ (n + 1) : Ideal R)])
        hTcongr
  exact haleft.trans haright

theorem eq_of_eq_add_of_maps_pow_succ
    (I : Ideal R) [IsHausdorff I R]
    (T : R →+ R)
    (hT : ∀ (n : ℕ) {x : R}, x ∈ I ^ n → T x ∈ I ^ (n + 1))
    (b : R) {x y : R}
    (hx : x = b + T x) (hy : y = b + T y) :
    x = y := by
  have hsub : ∀ n, x - y ∈ I ^ n := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, Ideal.one_eq_top]
        exact (Submodule.mem_top : x - y ∈ (⊤ : Ideal R))
    | succ n ih =>
        rw [hx, hy, add_sub_add_left_eq_sub, ← T.map_sub]
        exact hT n ih
  apply (IsHausdorff.eq_iff_smodEq (I := I)).2
  intro n
  rw [ideal_smul_top_eq_self, SModEq.sub_mem]
  exact hsub n

/-- An additive endomorphism which raises the `I`-adic filtration by one
has a unique affine fixed point on an `I`-adically complete ring. -/
theorem existsUnique_eq_add_of_maps_pow_succ
    (I : Ideal R) [IsAdicComplete I R]
    (T : R →+ R)
    (hT : ∀ (n : ℕ) {x : R}, x ∈ I ^ n → T x ∈ I ^ (n + 1))
    (b : R) :
    ∃! x : R, x = b + T x := by
  let x : ℕ → R := contractingApproximation T b
  have hcauchy : AdicCompletion.IsAdicCauchy I R x :=
    (AdicCompletion.isAdicCauchy_iff I R x).2 (by
      intro n
      rw [ideal_smul_top_eq_self, SModEq.sub_mem]
      simpa only [x] using contractingApproximation_sub_mem_pow I T hT b n)
  obtain ⟨a, ha⟩ :=
    (inferInstance : IsPrecomplete I R).prec hcauchy
  have ha' :
      ∀ n, x n ≡ a [SMOD (I ^ n : Ideal R)] := by
    intro n
    simpa only [ideal_smul_top_eq_self] using ha n
  have hfix : a = b + T a :=
    contractingApproximation_limit_is_fixed I T hT b a (by
      simpa only [x] using ha')
  refine ⟨a, hfix, ?_⟩
  intro y hy
  exact eq_of_eq_add_of_maps_pow_succ I T hT b hy hfix

end IsAdicComplete
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The coefficient source for the p-adic changed-uniformizer intertwiner

Let `k` be an algebraic closure of `ZMod p`.  The Witt ring `W(k)` is the
integer ring of the completed maximal-unramified coefficient field used in
the changed-uniformizer construction. Mathlib's `WittVector.frobeniusRotation` supplies the
actual unit `ε ∈ W(k)ˣ` satisfying

`φ(ε) = ε u`

for every p-adic integer unit `u`.  This is precisely the linear-coefficient
equation for the semilinear changed-uniformizer intertwiner.

No second p-adic integer ring or Frobenius is introduced here: the base map
uses mathlib's equivalence `W(ZMod p) ≃+* ℤ_[p]`, and `φ` is
`WittVector.frobenius`.
-/

noncomputable section

namespace LubinTate

/-- The canonical Witt integer ring over an algebraic closure of the
residue field.  This is the coefficient ring used for the mixed-characteristic
completed-unramified descent. -/
abbrev padicCompletedUnramifiedWittRing (p : ℕ) [Fact p.Prime] :=
  WittVector p (AlgebraicClosure (ZMod p))

/-- The canonical inclusion `ℤ_[p] → W(AlgebraicClosure (ZMod p))`. -/
noncomputable def padicIntToCompletedUnramifiedWittRing
    (p : ℕ) [Fact p.Prime] :
    ℤ_[p] →+* padicCompletedUnramifiedWittRing p :=
  (WittVector.map
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).comp
    (WittVector.equiv p).symm.toRingHom

/-- Witt Frobenius fixes the canonical p-adic integer coefficients. -/
theorem padicIntToCompletedUnramifiedWittRing_frobenius
    (p : ℕ) [Fact p.Prime] (z : ℤ_[p]) :
    WittVector.frobenius
        (padicIntToCompletedUnramifiedWittRing p z) =
      padicIntToCompletedUnramifiedWittRing p z := by
  apply WittVector.ext
  intro n
  simp only [padicIntToCompletedUnramifiedWittRing,
    RingHom.comp_apply, WittVector.coeff_frobenius_charP,
    WittVector.map_coeff]
  rw [← map_pow, ZMod.pow_card]

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerIntertwiner_DefectCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Changed-uniformizer defect correction

This module computes how a degreewise correction changes the semilinear substitution defect and constructs the unique coefficient that kills that defect.
-/

noncomputable section

namespace LubinTate

open SameUniformizer

/-- Two one-variable power series have the same total truncation through
degree `m` when their coefficients agree through degree `m`. -/
theorem powerSeries_truncTotal_succ_eq_of_coeff_eq_le
    {R : Type*} [CommRing R]
    {H H' : PowerSeries R} (m : ℕ)
    (hcoeff : ∀ q : ℕ, q ≤ m →
      PowerSeries.coeff q H = PowerSeries.coeff q H') :
    H.truncTotal (m + 1) = H'.truncTotal (m + 1) := by
  ext d
  by_cases hd : d.degree < m + 1
  · rw [MvPowerSeries.coeff_truncTotal H hd,
      MvPowerSeries.coeff_truncTotal H' hd]
    have hdegree : d.degree = d () :=
      Finset.sum_eq_single () (by simp) (by simp)
    simpa only [PowerSeries.coeff_def (R := R) (s := d) rfl] using
      hcoeff (d ()) (by omega)
  · rw [MvPowerSeries.coeff_truncTotal_eq_zero H (not_lt.mp hd),
      MvPowerSeries.coeff_truncTotal_eq_zero H' (not_lt.mp hd)]

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedPrimitiveUniformizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The completed p-adic primitive point is a uniformizer

The primitive multiplicative Lubin--Tate polynomial remains Eisenstein over
the completed-unramified valuation ring.  This file uses that actual
Eisenstein equation and the fundamental ramification identity to prove that
the chosen completed primitive point has normalized additive valuation one.
Consequently it is a genuine uniformizer of the completed level.
-/

noncomputable section

open scoped Polynomial Topology

namespace LubinTate

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

theorem completedPolynomial_eval₂_mem_ideal_of_coeff_mem
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (I : Ideal S) (P : Polynomial R) (z : S)
    (hcoeff : ∀ i, f (P.coeff i) ∈ I) :
    P.eval₂ f z ∈ I := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_right (z ^ i) I (hcoeff i)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_AmbientUniformizer
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Uniformizers detected in an ambient complete discrete valuation field

An embedding into an ambient complete DVF can make a uniformizer easier to
recognize.  For a finite separable extension, uniqueness of the extended
valuation transports that recognition back to the chosen valuation.
-/

namespace ValuationTheory

noncomputable section

universe u v w x y z

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- An embedding into an ambient valued field restricts to valuation rings
whenever the chosen source valuation is equivalent to the pulled-back
ambient valuation. -/
noncomputable def valuationSubringMapOfIsEquivComap
    {M : Type y} [Field M]
    {GammaL : Type x} {GammaM : Type z}
    [LinearOrderedCommGroupWithZero GammaL]
    [LinearOrderedCommGroupWithZero GammaM]
    (vL : _root_.Valuation L GammaL)
    (vM : _root_.Valuation M GammaM)
    (ι : L →+* M)
    (hEquiv : vL.IsEquiv (vM.comap ι)) :
    vL.valuationSubring →+* vM.valuationSubring where
  toFun a :=
    ⟨ι (a : L), by
      have ha :
          vL (a : L) ≤ vL 1 :=
        by
          rw [map_one]
          exact a.property
      have hcomap :=
        (hEquiv.le_iff_le
          (x := (a : L)) (y := (1 : L))).1 ha
      change vM (ι (a : L)) ≤ 1
      simpa only [_root_.Valuation.comap_apply, map_one] using hcomap⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' a b := by
    apply Subtype.ext
    simp

/-- The valuation-ring map induced by an equivalent ambient pullback acts
through the original field embedding. -/
@[simp]
theorem valuationSubringMapOfIsEquivComap_apply
    {M : Type y} [Field M]
    {GammaL : Type x} {GammaM : Type z}
    [LinearOrderedCommGroupWithZero GammaL]
    [LinearOrderedCommGroupWithZero GammaM]
    (vL : _root_.Valuation L GammaL)
    (vM : _root_.Valuation M GammaM)
    (ι : L →+* M)
    (hEquiv : vL.IsEquiv (vM.comap ι))
    (a : vL.valuationSubring) :
    ((valuationSubringMapOfIsEquivComap vL vM ι hEquiv a :
      vM.valuationSubring) : M) =
      ι (a : L) :=
  rfl

/-- The valuation-ring map induced by an equivalent ambient pullback is a
local homomorphism. -/
theorem valuationSubringMapOfIsEquivComap_isLocalHom
    {M : Type y} [Field M]
    {GammaL : Type x} {GammaM : Type z}
    [LinearOrderedCommGroupWithZero GammaL]
    [LinearOrderedCommGroupWithZero GammaM]
    (vL : _root_.Valuation L GammaL)
    (vM : _root_.Valuation M GammaM)
    (ι : L →+* M)
    (hEquiv : vL.IsEquiv (vM.comap ι)) :
    IsLocalHom
      (valuationSubringMapOfIsEquivComap vL vM ι hEquiv) := by
  let f := valuationSubringMapOfIsEquivComap vL vM ι hEquiv
  apply ((IsLocalRing.local_hom_TFAE f).out (2-1) (1-1)).mp
  rintro _ ⟨a, ha, rfl⟩
  have haVal : vL (a : L) < 1 :=
    (_root_.Valuation.mem_maximalIdeal_iff (v := vL)).1 ha
  have hlt :=
    (hEquiv.lt_iff_lt
      (x := (a : L)) (y := (1 : L))).1
      (by
        rw [map_one]
        exact haVal)
  exact (_root_.Valuation.mem_maximalIdeal_iff (v := vM)).2 <| by
    simpa only [f, valuationSubringMapOfIsEquivComap_apply,
      _root_.Valuation.comap_apply, map_one] using hlt

/-- The induced injection from the chosen residue field into the ambient
residue field. -/
noncomputable def residueFieldMapOfIsEquivComap
    {M : Type y} [Field M]
    {GammaL : Type x} {GammaM : Type z}
    [LinearOrderedCommGroupWithZero GammaL]
    [LinearOrderedCommGroupWithZero GammaM]
    (vL : _root_.Valuation L GammaL)
    (vM : _root_.Valuation M GammaM)
    (ι : L →+* M)
    (hEquiv : vL.IsEquiv (vM.comap ι)) :
    IsLocalRing.ResidueField vL.valuationSubring →+*
      IsLocalRing.ResidueField vM.valuationSubring := by
  letI :
      IsLocalHom
        (valuationSubringMapOfIsEquivComap vL vM ι hEquiv) :=
    valuationSubringMapOfIsEquivComap_isLocalHom vL vM ι hEquiv
  exact
    IsLocalRing.ResidueField.map
      (valuationSubringMapOfIsEquivComap vL vM ι hEquiv)

/-- Reduction modulo the maximal ideal commutes with compatible
automorphisms of the source and ambient valuation rings.  This is the
residue-field naturality needed when a finite valued subfield is realized
inside a larger complete discrete valuation field. -/
theorem residueFieldMapOfIsEquivComap_mapEquiv
    {M : Type y} [Field M]
    {GammaL : Type x} {GammaM : Type z}
    [LinearOrderedCommGroupWithZero GammaL]
    [LinearOrderedCommGroupWithZero GammaM]
    (vL : _root_.Valuation L GammaL)
    (vM : _root_.Valuation M GammaM)
    (ι : L →+* M)
    (hEquiv : vL.IsEquiv (vM.comap ι))
    (σL : vL.valuationSubring ≃+* vL.valuationSubring)
    (σM : vM.valuationSubring ≃+* vM.valuationSubring)
    (hcompat :
      ∀ a : vL.valuationSubring,
        valuationSubringMapOfIsEquivComap vL vM ι hEquiv (σL a) =
          σM
            (valuationSubringMapOfIsEquivComap
              vL vM ι hEquiv a))
    (a : IsLocalRing.ResidueField vL.valuationSubring) :
    residueFieldMapOfIsEquivComap vL vM ι hEquiv
        (IsLocalRing.ResidueField.mapEquiv σL a) =
      IsLocalRing.ResidueField.mapEquiv σM
        (residueFieldMapOfIsEquivComap vL vM ι hEquiv a) := by
  let :
      IsLocalHom
        (valuationSubringMapOfIsEquivComap vL vM ι hEquiv) :=
    valuationSubringMapOfIsEquivComap_isLocalHom vL vM ι hEquiv
  let : IsLocalHom σL.toRingHom :=
    IsLocalHom.of_surjective σL.toRingHom σL.surjective
  let : IsLocalHom σM.toRingHom :=
    IsLocalHom.of_surjective σM.toRingHom σM.surjective
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  change
    IsLocalRing.ResidueField.map
        (valuationSubringMapOfIsEquivComap vL vM ι hEquiv)
        (IsLocalRing.ResidueField.map σL.toRingHom
          (IsLocalRing.residue vL.valuationSubring b)) =
      IsLocalRing.ResidueField.map σM.toRingHom
        (IsLocalRing.ResidueField.map
          (valuationSubringMapOfIsEquivComap vL vM ι hEquiv)
          (IsLocalRing.residue vL.valuationSubring b))
  simp only [IsLocalRing.ResidueField.map_residue]
  exact congrArg
    (IsLocalRing.residue vM.valuationSubring)
    (hcompat b)

end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
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

-- Specializing the generic finite-place comparison to `ℚ` must retain its
-- `Algebra.id` owner rather than selecting the competing rational-field
-- instance introduced after specialization.
@[reducible] noncomputable local instance
    rationalFinitePlaceCompletionRatAlgebra
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (HeightOneSpectrum.adicAbv ℚ v).Completion := by
  letI : Algebra ℚ ℚ := Algebra.id ℚ
  let hWith : Algebra ℚ
      (WithAbs (HeightOneSpectrum.adicAbv ℚ v)) :=
    WithAbs.instAlgebra _
  let hUniform : UniformContinuousConstSMul ℚ
      (WithAbs (HeightOneSpectrum.adicAbv ℚ v)) :=
    WithAbs.instUniformContinuousConstSMulReal _
  exact
    @UniformSpace.Completion.algebra
      (WithAbs (HeightOneSpectrum.adicAbv ℚ v)) _ _ _ _
      ℚ _ hWith hUniform

open LocalClassFieldTheory
open LubinTate

/-! Named compatibility witnesses used by the ramified-prime and ray-norm
modules.  They are not installed as a duplicate module-level instance family;
the canonical instances above already provide the same data. -/

local instance instFactPrimeValNat_solutions_2_re2c093_1 (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩
local instance instNeZeroNatVal_solutions_re2c093_1 (m : ℕ+) : NeZero (m : ℕ) :=
  ⟨m.ne_zero⟩
/-- The positive conductor of the `n`-th ramified cyclotomic level at
`p`. -/
def rationalCyclotomicPrincipalPrimeModulus
    (p : Nat.Primes) (n : ℕ) : ℕ+ :=
  ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩

/-- The rational prime `q`, regarded as a unit of `ℚ`. -/
def rationalPrimeGeneratorUnit (q : Nat.Primes) : ℚˣ :=
  Units.mk0 (q.1 : ℚ) (by exact_mod_cast q.2.ne_zero)

/-- The underlying rational number of the prime generator unit is `q`. -/
@[simp]
theorem rationalPrimeGeneratorUnit_coe (q : Nat.Primes) :
    (rationalPrimeGeneratorUnit q : ℚ) = q.1 :=
  rfl

section RationalCyclotomicPrincipalPrime

/-! ## Ramified prime-power transport

This section reuses the canonical finite-place Artin tower above.  In
particular, it introduces no parallel completion/localization instance tower. -/

/-! ## The ramified principal finite-place factor -/

local instance instFactPrimeValNat_solutions_2_re2c093_2 (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩
local instance instNeZeroNatVal_solutions_re2c093_2 (m : ℕ+) : NeZero (m : ℕ) :=
  ⟨m.ne_zero⟩
theorem map_primitiveRoot_eq_pow_of_eq_pow
    {M : Type} [CommRing M] [IsDomain M]
    (f : M →* M) (zeta rho : M) (order exponent : ℕ)
    [NeZero order]
    (hzeta : IsPrimitiveRoot zeta order)
    (hrho : IsPrimitiveRoot rho order)
    (hf : f zeta = zeta ^ exponent) :
    f rho = rho ^ exponent := by
  obtain ⟨j, -, hj⟩ :=
    hzeta.eq_pow_of_pow_eq_one hrho.pow_eq_one
  calc
    f rho = f (zeta ^ j) := congrArg f hj.symm
    _ = (f zeta) ^ j := map_pow f zeta j
    _ = (zeta ^ exponent) ^ j := congrArg (fun z => z ^ j) hf
    _ = zeta ^ (exponent * j) := (pow_mul zeta exponent j).symm
    _ = zeta ^ (j * exponent) :=
      congrArg (fun e : ℕ => zeta ^ e) (Nat.mul_comm exponent j)
    _ = (zeta ^ j) ^ exponent := pow_mul zeta j exponent
    _ = rho ^ exponent := congrArg (fun z => z ^ exponent) hj

end RationalCyclotomicPrincipalPrime

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalAwayProduct
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

local instance instFactPrimeValNat_solutions_3_re2c093_1 (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩
local instance instNeZeroNatVal_solutions_1_re2c093_1 (m : ℕ+) : NeZero (m : ℕ) :=
  ⟨m.ne_zero⟩
/-- A rational prime distinct from `p` does not divide any power
`p ^ k`.  This includes the level-one case `k = 0`. -/
theorem rationalPrime_not_dvd_pow_of_ne
    (q p : Nat.Primes) (hqp : q ≠ p) (k : ℕ) :
    ¬ q.1 ∣ p.1 ^ k := by
  intro hdiv
  apply hqp
  apply Subtype.ext
  exact Nat.prime_eq_prime_of_dvd_pow q.2 p.2 hdiv

/-- Outside the finite rational prime-factorization support, the
`q`-adic valuation of the nonzero rational number is zero. -/
theorem
    padicValRat_eq_zero_of_not_mem_rationalPrimeFactorizationPrimeSupport
    (x : ℚˣ) (p q : Nat.Primes)
    (hq :
      q ∉ rationalPrimeFactorizationPrimeSupport x p) :
    padicValRat q.1 (x : ℚ) = 0 := by
  have hqNat :
      q.1 ∉ rationalPrimeFactorizationSupport x p := by
    intro hmem
    exact hq
      ((mem_rationalPrimeFactorizationPrimeSupport_iff
        x p q).2 hmem)
  have hqNotLt :
      ¬ q.1 <
        max (max (x : ℚ).num.natAbs (x : ℚ).den) p.1 + 1 := by
    intro hlt
    apply hqNat
    rw [rationalPrimeFactorizationSupport,
      Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt, q.2⟩
  have hbound :
      max (max (x : ℚ).num.natAbs (x : ℚ).den) p.1 + 1 ≤
        q.1 :=
    Nat.le_of_not_gt hqNotLt
  have hnumLt :
      (x : ℚ).num.natAbs < q.1 := by
    apply lt_of_lt_of_le _ hbound
    exact
      Nat.lt_succ_of_le
        (le_trans
          (le_max_left (x : ℚ).num.natAbs (x : ℚ).den)
          (le_max_left
            (max (x : ℚ).num.natAbs (x : ℚ).den) p.1))
  have hdenLt :
      (x : ℚ).den < q.1 := by
    apply lt_of_lt_of_le _ hbound
    exact
      Nat.lt_succ_of_le
        (le_trans
          (le_max_right (x : ℚ).num.natAbs (x : ℚ).den)
          (le_max_left
            (max (x : ℚ).num.natAbs (x : ℚ).den) p.1))
  have hnumPos :
      0 < (x : ℚ).num.natAbs :=
    Nat.pos_of_ne_zero
      (Int.natAbs_ne_zero.mpr
        (Rat.num_ne_zero.mpr x.ne_zero))
  have hdenPos :
      0 < (x : ℚ).den :=
    Nat.pos_of_ne_zero (x : ℚ).den_ne_zero
  have hqNum :
      ¬ q.1 ∣ (x : ℚ).num.natAbs :=
    Nat.not_dvd_of_pos_of_lt hnumPos hnumLt
  have hqDen :
      ¬ q.1 ∣ (x : ℚ).den :=
    Nat.not_dvd_of_pos_of_lt hdenPos hdenLt
  rw [padicValRat_def, padicValInt,
    padicValNat.eq_zero_of_not_dvd hqNum,
    padicValNat.eq_zero_of_not_dvd hqDen]
  norm_num

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The fixed rational separable closure, with the intermediate-field algebra
structure used by Mathlib's `IsSepClosure` construction. -/
noncomputable instance rationalSeparableClosure_isGalois :
    IsGalois ℚ (SeparableClosure ℚ) := by
  exact @IsSepClosure.isGalois
    ℚ _ (SeparableClosure ℚ) _
    ((separableClosure ℚ (AlgebraicClosure ℚ)).algebra)
    (separableClosure.isSepClosure ℚ (AlgebraicClosure ℚ))

/-- The chosen rational separable closure is normal over `ℚ`. -/
noncomputable instance rationalSeparableClosure_isNormal :
    Normal ℚ (SeparableClosure ℚ) :=
  rationalSeparableClosure_isGalois.to_normal

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicPrincipalIdele
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Principal ideles and the rational cyclotomic value

This file isolates the part of the rational principal-idele product
formula which follows from the existing archimedean reciprocity API.
Every rational idele is split into its archimedean and finite parts.
The archimedean part has Artin image of order at most two at every
finite layer; the actual Galois group of the rational `ZHat`-extension
is torsion-free, so its image in that extension is trivial.

Consequently the rational cyclotomic value of a principal idele is
exactly the value of its finite part.  At every finite cyclotomic layer
that remaining value is the genuine finite product of the chosen local
Artin maps.  Proving that product trivial requires a pointwise
compatibility theorem between the chosen finite-place Artin map and
the explicit cyclotomic action; no such compatibility is assumed here.
-/

open scoped BigOperators Classical NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance localInst_re2c093_2 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
/-- Restriction along the two sides of a commuting tower square gives the
same automorphism of the finite bottom field.  Keeping the field types
abstract makes this a stable interface for concrete inverse-limit fields. -/
theorem restrictNormalHom_eq_of_commuting_square
    (K E Z Ω : Type*)
    [Field K] [Field E] [Field Z] [Field Ω]
    [Algebra K E] [Algebra K Z] [Algebra K Ω]
    [Algebra E Z] [Algebra E Ω] [Algebra Z Ω]
    [IsScalarTower K E Z] [IsScalarTower K E Ω]
    [IsScalarTower K Z Ω] [IsScalarTower E Z Ω]
    [Normal K E]
    (τ : Z ≃ₐ[K] Z) (σ : Ω ≃ₐ[K] Ω)
    (hcommutes : ∀ z : Z,
      algebraMap Z Ω (τ z) = σ (algebraMap Z Ω z)) :
    AlgEquiv.restrictNormalHom E τ =
      AlgEquiv.restrictNormalHom E σ := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E Ω).injective
  calc
    algebraMap E Ω ((AlgEquiv.restrictNormalHom E τ) x) =
        algebraMap Z Ω
          (algebraMap E Z ((AlgEquiv.restrictNormalHom E τ) x)) :=
      IsScalarTower.algebraMap_apply E Z Ω _
    _ = algebraMap Z Ω (τ (algebraMap E Z x)) :=
      congrArg (algebraMap Z Ω)
        (AlgEquiv.restrictNormal_commutes τ E x)
    _ = σ (algebraMap Z Ω (algebraMap E Z x)) :=
      hcommutes _
    _ = σ (algebraMap E Ω x) :=
      congrArg σ (IsScalarTower.algebraMap_apply E Z Ω x).symm
    _ = algebraMap E Ω ((AlgEquiv.restrictNormalHom E σ) x) :=
      (AlgEquiv.restrictNormal_commutes σ E x).symm

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The rational prime used to realize the quadratic complexification
as the fourth-root cyclotomic field. -/
def rationalComplexificationPrime : Nat.Primes :=
  ⟨2, Nat.prime_two⟩

local instance rationalComplexificationPrimeFact_re2c093_1 :
    Fact rationalComplexificationPrime.1.Prime :=
  ⟨rationalComplexificationPrime.2⟩
local instance rationalComplexificationPrimeSquareNeZero_re2c093_1 :
    NeZero (rationalComplexificationPrime.1 ^ 2) :=
  ⟨pow_ne_zero 2 rationalComplexificationPrime.2.ne_zero⟩
/-- The concrete fourth-root cyclotomic field inside `ℂ`.

It is defined by adjoining all fourth roots of unity, so it is
independent of a choice between `I` and `-I` and is visibly preserved
by complex conjugation. -/
def complexFourthRootField :
    IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ
    {z : ℂ |
      ∃ n ∈ ({4} : Set ℕ), n ≠ 0 ∧ z ^ n = 1}

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitCore
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The rational absolute idele-class direct limit

Finite Galois relative idele class groups over `ℚ`, their scalar-extension
maps, and the induced absolute Galois representation.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

universe u

/-- The rational algebra structure on the chosen separable closure is
the one induced by its realization inside the algebraic closure. -/
@[reducible]
noncomputable instance rationalSeparableClosureAlgebra :
    Algebra ℚ (SeparableClosure ℚ) :=
  letI : Algebra ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.instAlgebra ℚ
  IntermediateField.algebra' (R' := ℚ)
    (separableClosure ℚ (AlgebraicClosure ℚ))

/-- A rational intermediate field uses its actual inclusion into the
chosen separable closure as its algebra structure. -/
@[reducible]
noncomputable instance rationalIntermediateFieldAlgebra
    (E : IntermediateField ℚ (SeparableClosure ℚ)) :
    Algebra ℚ E :=
  IntermediateField.algebra' (R' := ℚ) E

/-- Every finite-dimensional rational intermediate field is a number
field. -/
noncomputable instance rationalIntermediateFieldNumberField
    (E : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ E] :
    NumberField E :=
  NumberField.of_module_finite ℚ E

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicIdeleClassValuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# The cyclotomic valuation on idele classes

The cyclotomic idele value is trivial on principal ideles, so it descends
to the ordinary idele class group.  Its restriction to the compact
norm-one idele class group still has dense image in `ZHat`; compactness
therefore upgrades density to surjectivity.

For a number field `K`, the defining normalization gives the exact
identity

`f_K v_K(c) = v_ℚ(N_{K/ℚ} c)`.

Surjectivity of `v_K` then identifies the image of the actual
idele-class norm with `f_K ZHat`.  For the actual fixed field attached
to a finite abstract field, the already constructed cyclotomic
base-change theorem identifies `f_K` with the residue degree.  This
supplies the norm-range field of the concrete henselian valuation data.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- Lift a continuous multiplicative map through a quotient group once its
defining normal subgroup is contained in the kernel.  Keeping the quotient-map
argument here avoids repeating the same large continuity elaboration for the
rational and number-field cyclotomic values. -/
noncomputable def ideleClassContinuousQuotientLift
    {A B : Type*} [Group A] [TopologicalSpace A]
    [Group B] [TopologicalSpace B]
    (N : Subgroup A) [N.Normal] (f : A →ₜ* B)
    (hN : N ≤ f.toMonoidHom.ker) : (A ⧸ N) →ₜ* B := by
  let φ : (A ⧸ N) →* B := QuotientGroup.lift N f.toMonoidHom hN
  have hcomp :
      Continuous (fun a : A => φ (QuotientGroup.mk' N a)) := by
    refine f.continuous_toFun.congr (fun a => ?_)
    change f.toMonoidHom a = φ (QuotientGroup.mk' N a)
    exact (QuotientGroup.lift_mk N hN a).symm
  exact
    { toMonoidHom := φ
      continuous_toFun :=
        (QuotientGroup.isQuotientMap_mk
          (G := A) (N := N)).continuous_iff.2 hcomp }

@[simp]
theorem ideleClassContinuousQuotientLift_mk
    {A B : Type*} [Group A] [TopologicalSpace A]
    [Group B] [TopologicalSpace B]
    (N : Subgroup A) [N.Normal] (f : A →ₜ* B)
    (hN : N ≤ f.toMonoidHom.ker) (a : A) :
    ideleClassContinuousQuotientLift N f hN
        (QuotientGroup.mk' N a) =
      f a := by
  change QuotientGroup.lift N f.toMonoidHom hN
      (QuotientGroup.mk' N a) = f a
  exact QuotientGroup.lift_mk N hN a

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

section FiniteCoordinateHelpers

/-- Opaque three-step equality composition used to keep large dependent
finite-level coordinates out of endpoint proof normalization. -/
theorem cyclotomicAbstractFixedFieldArtin_eqTransThree
    {α : Type} {a b c d : α}
    (hab : a = b) (hbc : b = c) (hcd : c = d) :
    a = d :=
  hab.trans (hbc.trans hcd)

end FiniteCoordinateHelpers

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionAction
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Galois actions on rational fixed-field idele classes

Naturality of the fixed-field comparison for automorphisms and the
finite-extension Galois action.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open LocalClassFieldTheory

theorem addEquiv_trans_symm_trans_symm_trans_apply_eq_p0
    {V A B C D : Type*}
    [Add V] [Add A] [Add B] [Add C] [Add D]
    (eV : V ≃+ D) (eB : B ≃+ D)
    (eA : A ≃+ B) (eC : A ≃+ C)
    {y : V} {z : A} {w : C}
    (h : eV y = eB (eA z))
    (ht : eC z = w) :
    (((eV.trans eB.symm).trans eA.symm).trans eC) y = w := by
  change eC (eA.symm (eB.symm (eV y))) = w
  rw [h, eB.symm_apply_apply, eA.symm_apply_apply]
  exact ht

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionNorm
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Norms on rational fixed-field idele classes

Compatibility of fixed-field inclusion and relative norm with the actual
idele-class extension attached to the abstract subgroup tower.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open LocalClassFieldTheory

theorem fourStepAddEquiv_apply_eq
    {V A B C D : Type*}
    [Add V] [Add A] [Add B] [Add C] [Add D]
    (eV : V ≃+ D) (eB : B ≃+ D)
    (eA : A ≃+ B) (eC : A ≃+ C)
    {y : V} {z : A} {w : C}
    (h : eV y = eB (eA z))
    (ht : eC z = w) :
    (((eV.trans eB.symm).trans eA.symm).trans eC) y = w := by
  change eC (eA.symm (eB.symm (eV y))) = w
  rw [h, eB.symm_apply_apply, eA.symm_apply_apply]
  exact ht

theorem repOfMulDistribMulAction_rho_toMul
    {G A : Type*} [Group G] [CommGroup A]
    [MulDistribMulAction G A]
    (g : G) (a : Additive A) :
    Additive.toMul
        ((Rep.ofMulDistribMulAction G A).ρ g a) =
      g • Additive.toMul a :=
  rfl

theorem fintype_prod_comp_equiv
    {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [CommMonoid A]
    (e : ι ≃ κ) (f : κ → A) :
    (∏ i, f (e i)) = ∏ k, f k :=
  Fintype.prod_equiv e
    (fun i => f (e i)) f (fun _ => rfl)

theorem eq_of_common_ofMul_image
    {A B : Type*}
    (f : A → B) (hf : Function.Injective f)
    {u : Additive B} {a b : A}
    (ha : u = Additive.ofMul (f a))
    (hb : u = Additive.ofMul (f b)) :
    a = b := by
  have h := congrArg Additive.toMul (ha.symm.trans hb)
  change f a = f b at h
  exact hf h

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitNormQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Finite norm quotients for rational fixed fields

The abstract finite norm subgroup and quotient are identified with the
ordinary idele-class norm range and quotient of the actual fixed-field extension.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open LocalClassFieldTheory

theorem rationalNormQuotientNumberFieldOfFiniteDimensional
    (F : Type*) [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] :
    NumberField F :=
  NumberField.of_module_finite ℚ F

theorem addEquiv_trans_symm_trans_symm_trans_apply_eq_p1
    {V A B C D : Type*}
    [Add V] [Add A] [Add B] [Add C] [Add D]
    (eV : V ≃+ D) (eB : B ≃+ D)
    (eA : A ≃+ B) (eC : A ≃+ C)
    {y : V} {z : A} {w : C}
    (h : eV y = eB (eA z))
    (ht : eC z = w) :
    (((eV.trans eB.symm).trans eA.symm).trans eC) y = w := by
  change eC (eA.symm (eB.symm (eV y))) = w
  rw [h, eB.symm_apply_apply, eA.symm_apply_apply]
  exact ht

def quotientAddEquivOfEquivMapEq
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (S : AddSubgroup A) (T : AddSubgroup B)
    (e : B ≃+ A)
    (hmap : S.map e.symm.toAddMonoidHom = T) :
    (A ⧸ S) ≃+ (B ⧸ T) := by
  have hforward :
      S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro x hx
    change e.symm x ∈ T
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hinverse :
      T ≤ AddSubgroup.comap e.toAddMonoidHom S := by
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
  let f : (A ⧸ S) →+ (B ⧸ T) :=
    QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
  let g : (B ⧸ T) →+ (A ⧸ S) :=
    QuotientAddGroup.map T S e.toAddMonoidHom hinverse
  exact
    { toFun := f
      invFun := g
      left_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change (↑(e (e.symm x)) : A ⧸ S) = ↑x
        rw [e.apply_symm_apply]
      right_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change (↑(e.symm (e x)) : B ⧸ T) = ↑x
        rw [e.symm_apply_apply]
      map_add' := f.map_add }

theorem map_addRange_eq_monoidRange_toAddSubgroup_of_equiv
    {U A G H : Type*}
    [AddCommGroup U] [AddCommGroup A] [CommGroup G] [CommGroup H]
    (f : U →+ A) (g : G →* H)
    (eU : Additive G ≃+ U) (eA : Additive H ≃+ A)
    (hcompat : ∀ c : Additive G,
      eA.symm (f (eU c)) =
        Additive.ofMul (g (Additive.toMul c))) :
    f.range.map eA.symm.toAddMonoidHom = g.range.toAddSubgroup := by
  ext y
  constructor
  · intro hy
    obtain ⟨n, ⟨u, hu⟩, hny⟩ := hy
    let c : Additive G := eU.symm u
    refine ⟨Additive.toMul c, ?_⟩
    apply Additive.ofMul.injective
    exact
      (hcompat c).symm.trans
        ((congrArg (fun z => eA.symm (f z))
            (eU.apply_symm_apply u)).trans
          ((congrArg eA.symm hu).trans hny))
  · intro hy
    obtain ⟨d, hd⟩ := hy
    let c : Additive G := Additive.ofMul d
    let u : U := eU c
    exact
      ⟨f u, ⟨u, rfl⟩,
        (hcompat c).trans (congrArg Additive.ofMul hd)⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedGeometricRestriction
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Geometric restriction from the cyclotomic unramified field

An abstractly unramified finite abelian subextension is contained in the
actual cyclotomic maximal-unramified fixed field.  This file realizes that
containment as an algebra tower and proves that the finite restriction
defined on quotient presentations is literally restriction of field
automorphisms.

The field-range form of the finite layer is also bundled in the finite
Galois inverse system.  Consequently the geometric restriction of the
infinite global Artin map is the ordinary finite global Artin map.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open LocalClassFieldTheory

@[reducible]
noncomputable local instance
    cyclotomicUnramifiedGeometricRationalSeparableClosureAlgebra :
    Algebra ℚ (SeparableClosure ℚ) :=
  DivisionRing.toRatAlgebra

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_TopologicalGlobalNormResidueAbelianization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- `Abelianization` is an opaque quotient alias, so install its native
quotient topology explicitly before asking for topological properties. -/
local instance
    topologicalGlobalNormResidueAbelianization_galoisAbelianizationTopology :
    TopologicalSpace (Abelianization (Gal(L / K))) := by
  change
    TopologicalSpace
      (Gal(L / K) ⧸ commutator (Gal(L / K)))
  infer_instance

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv
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
namespace PrimeDegreePackets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open scoped Matrix
open Matrix



def coordinateMod (n m : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ZMod m) where
  toFun v i := v i
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp [zsmul_eq_mul]

open TopologicalSpace
open scoped Topology

end PrimeDegreePackets
end
end

end OAI
end


