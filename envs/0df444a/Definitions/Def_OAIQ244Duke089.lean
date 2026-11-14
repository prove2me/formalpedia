-- Prove2me | Definitions.Def_OAIQ244Duke089
-- name    : OAIQ244Duke089
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T00:38:20.955202+00:00
-- url     : https://prove2.me/theorems/770e8732-f381-4de9-9fde-25fff2e8c83a
-- title:
--   Definitions bundle OAIQ244Duke089 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 197 declarations of OpenAI's Lean: 49 definitions, 15 instances and 133 theorems. The definitions and types are `LubinTate.padicChangedCompletedPrimitivePolynomial`, `LubinTate.padicChangedCompletedPrimitivePolynomialInteger`, `LubinTate.padicChangedUniformizerLevelEmbedding`, `LubinTate.padicChangedUniformizerLevelEquivCompletedFixedField`, `LubinTate.padicChangedUniformizerLevelToCompletedFixedField`, `LubinTate.padicChangedUniformizerThetaPowerBasis`, `LubinTate.padicCompletedActionTargetWithIdeal`, `LubinTate.padicCompletedChangedFixedFieldToStandardChangedCompositum`, `LubinTate.padicCompletedChangedUniformizerArtinCandidate`, `LubinTate.padicCompletedChangedUniformizerArtinCandidateAlgHom`, `LubinTate.padicCompletedChangedUniformizerFixedField`, `LubinTate.padicCompletedChangedUniformizerFixedFieldAlgebra`, `LubinTate.padicCompletedChangedUniformizerFixedFieldModule`, `LubinTate.padicCompletedChangedUniformizerFrobeniusAlgEquiv`, `LubinTate.padicCompletedChangedUniformizerFrobeniusSubgroup`, `LubinTate.padicCompletedChangedUniformizerPrimeElement`, `LubinTate.padicCompletedChangedUniformizerRelativeArtinCandidate`, `LubinTate.padicCompletedFrobeniusEvaluationTargetWithIdeal`, `LubinTate.padicCompletedFrobeniusEvaluationWittUniformSpace`, `LubinTate.padicCompletedLevelFrobeniusAlgebra`, `LubinTate.padicCompletedLevelOriginalAlgebra`, `LubinTate.padicCompletedLevelResidueFieldEquiv`, `LubinTate.padicCompletedPrimitivePowerBasis`, `LubinTate.padicCompletedPrimitiveUniformizerTargetWithIdeal`, `LubinTate.padicCompletedStandardChangedCompositum`, `LubinTate.padicCompletedStandardLevelField`, `LubinTate.padicCompletedStandardPrimitivePointUnitAction`, `LubinTate.padicCompletedThetaFixedTargetWithIdeal`, `LubinTate.padicCompletedUnitFrobeniusIntegerEquiv`, `LubinTate.padicCompletedUnitFrobeniusLift`, `LubinTate.padicCompletedUnitFrobeniusLiftAlgHom`, `LubinTate.padicCompletedUnitFrobeniusLiftEquiv`, `LubinTate.padicCompletedUnitParameterRoot`, `LubinTate.padicCompletedUnitParameterRootSet`, `LubinTate.padicCompletedUnramifiedFrobeniusIntegerEquiv`, `LubinTate.padicStandardLevelEmbedding`, `LubinTate.padicStandardLevelEquivCompletedStandardLevelField`, `LubinTate.padicStandardLevelIntegerEmbedding`, `LubinTate.padicStandardLevelToCompletedChangedCompositum`, `LubinTate.padicStandardLevelTransportCoefficientTopologicalSpace` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_CyclotomicPrincipalIdele`, `GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange`, `GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalProduct`, `LubinTate_Padic_ChangedUniformizerIntertwiner_IntertwinerConstruction`, `LubinTate_Padic_ChangedUniformizerIntertwiner_ScalarCompatibility`, `LubinTate_Padic_CompletedChangedStandardCompositum`, `LubinTate_Padic_CompletedChangedStandardResidue`, `LubinTate_Padic_CompletedChangedUniformizerFixedField`, `LubinTate_Padic_CompletedChangedUniformizerPrimitive`, `LubinTate_Padic_CompletedChangedUniformizerThetaFixed`, `LubinTate_Padic_CompletedFrobeniusEvaluation`, `LubinTate_Padic_CompletedFrobeniusLift`, `LubinTate_Padic_CompletedPrimitiveAction`, `LubinTate_Padic_CompletedPrimitiveUniformizer`, `LubinTate_Padic_CompletedResidueFrobenius`, `LubinTate_Padic_CompletedStandardLevelTransport`, `LubinTate_Padic_MultiplicativeEvaluation_Core`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke084` and `OAIQ244Duke085` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke093` and `OAIQ244Duke117`.
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
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
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
import Definitions.Def_OAIQ244Duke084
import Definitions.Def_OAIQ244Duke085

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicZHatBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- The Galois group of the actual `ZHat`-extension of `ℚ` is
torsion-free.  This is the property that removes every archimedean
order-two Artin factor in the normalized reciprocity construction. -/
noncomputable instance rationalCyclotomicZHatFieldGal_isMulTorsionFree :
    IsMulTorsionFree
      (rationalCyclotomicZHatField ≃ₐ[ℚ]
        rationalCyclotomicZHatField) :=
  Function.Injective.isMulTorsionFree
    rationalCyclotomicZHatFieldGalEquivZHat.toMonoidHom
    rationalCyclotomicZHatFieldGalEquivZHat.injective

variable (K : Type*) [Field K] [NumberField K]

noncomputable instance
    numberFieldCyclotomicZHatIntersection_finiteDimensional :
    FiniteDimensional ℚ
      (numberFieldCyclotomicZHatIntersection K) := by
  let f :
      numberFieldCyclotomicZHatIntersection K →ₐ[ℚ]
        numberFieldInRationalSeparableClosure K :=
    (IntermediateField.inclusion
      (show
        numberFieldCyclotomicZHatIntersection K ≤
          numberFieldInRationalSeparableClosure K from
        inf_le_left))
  exact FiniteDimensional.of_injective f.toLinearMap f.injective

noncomputable instance
    numberFieldCyclotomicZHatFiniteCompositum_numberField
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  NumberField.of_module_finite ℚ
    (numberFieldCyclotomicZHatFiniteCompositum K E)

noncomputable instance
    rationalCyclotomicZHatFiniteLayerCompositum_algebra
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra E
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  (rationalCyclotomicZHatFiniteLayerCompositumEmbedding K E).toRingHom.toAlgebra

/-- The scalar action on the finite compositum induced by its actual
finite-layer embedding.  Declaring it directly avoids asking instance search
to rediscover the action through an unrelated intermediate-field algebra. -/
noncomputable instance
    rationalCyclotomicZHatFiniteLayerCompositum_smul
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul E
      (numberFieldCyclotomicZHatFiniteCompositum K E) :=
  (rationalCyclotomicZHatFiniteLayerCompositum_algebra K E).toSMul

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfiniteGlobalArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.cyclicPrimeDegreeIntermediate_isGalois
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

/-!
## Assembly in the finite-Galois inverse limit

The following construction is the global analogue of LCFT's
`residueFrobeniusToLimit`: its coordinates are the actual finite global
Artin homomorphisms, and compatibility is restriction in a finite
abelian tower.
-/

/-- Finite projection with both finite-layer structures supplied explicitly.
This is useful when a concrete tower already has named canonical witnesses
and must not resynthesize them while checking the projected Artin endpoint. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_structures
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K Ω)
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois K E) :
    letI : NumberField E := hE
    letI : IsAbelianGalois K E := hAbelian
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom
        (K := K) (L := E) a := by
  let : NumberField E := hE
  let : IsAbelianGalois K E := hAbelian
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_numberField
      K Ω a E hE

/-- Finite projection stated for a plain intermediate field with its finite
Galois structures supplied separately.  This avoids packaging a concrete
dependent field into `FiniteGaloisIntermediateField` at every call site. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_of_intermediateField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) (E : IntermediateField K Ω)
    [FiniteDimensional K E] [IsGalois K E]
    (hE : NumberField E)
    (hAbelian : IsAbelianGalois K E) :
    letI : NumberField E := hE
    letI : IsAbelianGalois K E := hAbelian
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  let G : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := E
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let : NumberField E := hE
  let : IsAbelianGalois K E := hAbelian
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_structures
      K Ω a G hE hAbelian

/-- Finite projection for a plain intermediate field when its structures are
already installed as ambient instances. -/
theorem restrictNormalHom_infiniteGlobalArtinMonoidHom_intermediateField
    (K Ω : Type) [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAbelianGalois K Ω]
    (a : IdeleGroup K) (E : IntermediateField K Ω)
    [FiniteDimensional K E] [NumberField E] [IsAbelianGalois K E] :
    AlgEquiv.restrictNormalHom E
        (infiniteGlobalArtinMonoidHom K Ω a) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom_of_intermediateField
      K Ω a E (inferInstance : NumberField E)
        (inferInstance : IsAbelianGalois K E)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicPrincipalIdele
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

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
open NumberField IsDedekindDomain ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

-- Keep the prime-power presentation explicit for canonical instance synthesis.
-- Both structures are the existing canonical cyclotomic-level instances.
local instance rationalCyclotomicPrimePowerNumberField
    (p : Nat.Primes) (k : ℕ) :
    NumberField
      (KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

local instance rationalCyclotomicPrimePowerIsGalois
    (p : Nat.Primes) (k : ℕ) :
    IsGalois ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_isGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

local instance rationalCyclotomicPrimePowerIsAbelianGalois
    (p : Nat.Primes) (k : ℕ) :
  IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  IsAbelianGalois.of_algHom
    (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩).val

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerIntertwiner_IntertwinerConstruction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.LubinTate.standardLubinTateUnitParameter_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Changed-uniformizer intertwiner construction

This module builds compatible finite-degree approximations, assembles the changed-uniformizer intertwiner, proves its functional equation, and establishes uniqueness.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

/-- The completed changed standard series after the actual intertwiner is
the Frobenius transform of the intertwiner after the multiplicative
series. This is the first changed-uniformizer identity. -/
theorem padicChangedUniformizerIntertwiner_functionalEquation
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.subst
        (padicChangedUniformizerIntertwiner p u)
        (PowerSeries.map
          (padicValuationSubringToCompletedUnramifiedWittRing p)
          (standardLubinTateSeries
            (standardLubinTateChangedUniformizer_isUniformizer
              (padicMultiplicativeLubinTateSeries_isUniformizer p) u)).toPowerSeries) =
      PowerSeries.subst
        (PowerSeries.map
          (padicValuationSubringToCompletedUnramifiedWittRing p)
          (padicMultiplicativeLubinTateSeries p).toPowerSeries)
        (PowerSeries.map WittVector.frobenius
          (padicChangedUniformizerIntertwiner p u)) := by
  change
    PowerSeries.subst
        (padicChangedUniformizerIntertwiner p u)
        (padicCompletedChangedStandardSeries p u) =
      PowerSeries.subst
        (padicCompletedMultiplicativeSeries p)
        (PowerSeries.map WittVector.frobenius
          (padicChangedUniformizerIntertwiner p u))
  rw [← sub_eq_zero]
  apply PowerSeries.ext
  intro m
  rw [map_sub, map_zero]
  have hrewrite :
      PowerSeries.coeff m
            (PowerSeries.subst
              (padicChangedUniformizerIntertwiner p u)
              (padicCompletedChangedStandardSeries p u)) -
          PowerSeries.coeff m
            (PowerSeries.subst
              (padicCompletedMultiplicativeSeries p)
              (PowerSeries.map WittVector.frobenius
                (padicChangedUniformizerIntertwiner p u))) =
        -PowerSeries.coeff m
          (padicChangedUniformizerDefect p u
            (padicChangedUniformizerIntertwiner p u)) := by
    unfold padicChangedUniformizerDefect
    rw [map_sub]
    ring
  rw [hrewrite]
  cases m with
  | zero =>
      rw [padicChangedUniformizerDefect_coeff_zero, neg_zero]
  | succ m =>
      cases m with
      | zero =>
          rw [padicChangedUniformizerDefect_coeff_one, neg_zero]
      | succ n =>
          rw [show n + 1 + 1 = n + 2 by omega,
            padicChangedUniformizerDefect_coeff_succ_succ, neg_zero]

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerIntertwiner_ScalarCompatibility
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedLevelField_padicScalarTower _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.LubinTate.standardLubinTateUnitParameter_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.zHatUnitsDecomposition_freeCoordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.padicCompletedChangedStandardScalarEndomorphismValue_one _root_.LubinTate.padicCompletedLevelPadicIntegerCoefficientHom_coe _root_.LubinTate.padicCompletedLevelPowerSeriesEval_C _root_.LubinTate.padicCompletedLevelPowerSeriesEval_X _root_.LubinTate.padicCompletedLevelPowerSeriesEval_coe _root_.LubinTate.padicCompletedLevelWittCoefficientHom_apply _root_.LubinTate.padicCompletedMultiplicativeScalarEndomorphismValue_one _root_.LubinTate.padicCompletedPrimitiveRootInteger_coe _root_.LubinTate.padicCompletedStandardScalarEndomorphismValue_one _root_.LubinTate.padicCompletedStandardScalarEndomorphism_one _root_.LubinTate.padicStandardToMultiplicativeIntertwiner_coeff_one _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.LubinTate.padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Changed-uniformizer scalar compatibility

This module proves that the changed-uniformizer intertwiner commutes with every scalar endomorphism and identifies its coefficientwise Frobenius twist.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

/-- The semilinear changed-uniformizer comparison intertwines every scalar
endomorphism.  This is the formal-series compatibility used in the
cyclotomic action formula for the Lubin--Tate character. -/
theorem padicChangedUniformizerIntertwiner_endomorphism
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) :
    PowerSeries.subst
        (padicCompletedMultiplicativeScalarEndomorphism p a)
        (padicChangedUniformizerIntertwiner p u) =
      PowerSeries.subst
        (padicChangedUniformizerIntertwiner p u)
        (padicCompletedChangedStandardScalarEndomorphism p u a) := by
  let H := padicChangedUniformizerIntertwiner p u
  let M := padicCompletedMultiplicativeScalarEndomorphism p a
  let S := padicCompletedChangedStandardScalarEndomorphism p u a
  let E := padicCompletedMultiplicativeSeries p
  let Ebar := padicCompletedChangedStandardSeries p u
  let Phi := PowerSeries.map WittVector.frobenius H
  let epsilon : padicCompletedUnramifiedWittRing p :=
    (padicChangedUniformizerLinearCoefficient p u :
      padicCompletedUnramifiedWittRing p)
  let alpha : padicCompletedUnramifiedWittRing p :=
    padicValuationSubringToCompletedUnramifiedWittRing p a
  let A := PowerSeries.subst M H
  let B := PowerSeries.subst H S
  have hHconstant : PowerSeries.constantCoeff H = 0 := by
    simpa only [H] using
      padicChangedUniformizerIntertwiner_constantCoeff p u
  have hHlinear :
      HasLinearTerm H (fun _ : Unit => epsilon) := by
    apply powerSeries_hasLinearTerm_of_constantCoeff_coeff_one
      H epsilon hHconstant
    simpa only [H, epsilon] using
      padicChangedUniformizerIntertwiner_coeff_one p u
  have hMlinear :
      HasLinearTerm M (fun _ : Unit => alpha) := by
    simpa only [M, alpha] using
      padicCompletedMultiplicativeScalarEndomorphism_hasLinearTerm p a
  have hSlinear :
      HasLinearTerm S (fun _ : Unit => alpha) := by
    simpa only [S, alpha] using
      padicCompletedChangedStandardScalarEndomorphism_hasLinearTerm p u a
  have hHsubst : PowerSeries.HasSubst H :=
    hHlinear.hasSubst
  have hMsubst : PowerSeries.HasSubst M :=
    hMlinear.hasSubst
  have hSsubst : PowerSeries.HasSubst S :=
    hSlinear.hasSubst
  have hEsubst : PowerSeries.HasSubst E :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simpa only [E] using
        padicCompletedMultiplicativeSeries_constantCoeff p)
  have hEbarSubst : PowerSeries.HasSubst Ebar :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simpa only [Ebar] using
        padicCompletedChangedStandardSeries_constantCoeff p u)
  have hPhiSubst : PowerSeries.HasSubst Phi :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simpa only [Phi] using
        padicChangedUniformizerFrobenius_constantCoeff_eq_zero
          p H hHconstant)
  have hHfunctional :
      PowerSeries.subst H Ebar =
        PowerSeries.subst E Phi := by
    simpa only [H, Ebar, E, Phi,
      padicCompletedChangedStandardSeries,
      padicCompletedMultiplicativeSeries] using
      padicChangedUniformizerIntertwiner_functionalEquation p u
  have hMcommutes :
      PowerSeries.subst M E =
        PowerSeries.subst E M := by
    simpa only [M, E] using
      padicCompletedMultiplicativeScalarEndomorphism_commutes p a
  have hScommutes :
      PowerSeries.subst S Ebar =
        PowerSeries.subst Ebar S := by
    simpa only [S, Ebar] using
      padicCompletedChangedStandardScalarEndomorphism_commutes p u a
  have hmapA :
      PowerSeries.map WittVector.frobenius A =
        PowerSeries.subst M Phi := by
    simp only [A, Phi]
    change MvPowerSeries.map _ _ = _
    rw [PowerSeries.map_subst hMsubst]
    change
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) = _
    rw [padicCompletedMultiplicativeScalarEndomorphism_frobenius]
  have hmapB :
      PowerSeries.map WittVector.frobenius B =
        PowerSeries.subst Phi S := by
    simp only [B, Phi]
    change MvPowerSeries.map _ _ = _
    rw [PowerSeries.map_subst hHsubst]
    change
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) = _
    rw [padicCompletedChangedStandardScalarEndomorphism_frobenius]
  have hAfunctional :
      PowerSeries.subst A Ebar =
        PowerSeries.subst E
          (PowerSeries.map WittVector.frobenius A) := by
    calc
      PowerSeries.subst A Ebar =
          PowerSeries.subst M
            (PowerSeries.subst H Ebar) := by
        simpa only [A] using
          (PowerSeries.subst_comp_subst_apply
            hHsubst hMsubst Ebar).symm
      _ = PowerSeries.subst M
            (PowerSeries.subst E Phi) := by
        rw [hHfunctional]
      _ = PowerSeries.subst
            (PowerSeries.subst M E) Phi :=
        PowerSeries.subst_comp_subst_apply
          hEsubst hMsubst Phi
      _ = PowerSeries.subst
            (PowerSeries.subst E M) Phi := by
        rw [hMcommutes]
      _ = PowerSeries.subst E
            (PowerSeries.subst M Phi) :=
        (PowerSeries.subst_comp_subst_apply
          hMsubst hEsubst Phi).symm
      _ = PowerSeries.subst E
            (PowerSeries.map WittVector.frobenius A) := by
        rw [hmapA]
  have hBfunctional :
      PowerSeries.subst B Ebar =
        PowerSeries.subst E
          (PowerSeries.map WittVector.frobenius B) := by
    calc
      PowerSeries.subst B Ebar =
          PowerSeries.subst H
            (PowerSeries.subst S Ebar) := by
        simpa only [B] using
          (PowerSeries.subst_comp_subst_apply
            hSsubst hHsubst Ebar).symm
      _ = PowerSeries.subst H
            (PowerSeries.subst Ebar S) := by
        rw [hScommutes]
      _ = PowerSeries.subst
            (PowerSeries.subst H Ebar) S :=
        PowerSeries.subst_comp_subst_apply
          hEbarSubst hHsubst S
      _ = PowerSeries.subst
            (PowerSeries.subst E Phi) S := by
        rw [hHfunctional]
      _ = PowerSeries.subst E
            (PowerSeries.subst Phi S) :=
        (PowerSeries.subst_comp_subst_apply
          hPhiSubst hEsubst S).symm
      _ = PowerSeries.subst E
            (PowerSeries.map WittVector.frobenius B) := by
        rw [hmapB]
  have hAlinearRaw :=
    hHlinear.subst
      (G := fun _ : Unit => M)
      (M := fun _ : Unit => fun _ : Unit => alpha)
      (fun _ => hMlinear)
  have hAlinear :
      HasLinearTerm A
        (fun _ : Unit => epsilon * alpha) := by
    simpa [A, PowerSeries.subst_def] using hAlinearRaw
  have hBlinearRaw :=
    hSlinear.subst
      (G := fun _ : Unit => H)
      (M := fun _ : Unit => fun _ : Unit => epsilon)
      (fun _ => hHlinear)
  have hBlinear :
      HasLinearTerm B
        (fun _ : Unit => alpha * epsilon) := by
    simpa [B, PowerSeries.subst_def] using hBlinearRaw
  have hlinear :
      PowerSeries.coeff 1 A =
        PowerSeries.coeff 1 B := by
    calc
      PowerSeries.coeff 1 A =
          epsilon * alpha :=
        hAlinear.coeff_single ()
      _ = alpha * epsilon := mul_comm _ _
      _ = PowerSeries.coeff 1 B :=
        (hBlinear.coeff_single ()).symm
  exact
    padicChangedUniformizerIntertwiner_unique p u
      hAlinear.constantCoeff_eq_zero
      hBlinear.constantCoeff_eq_zero
      hlinear hAfunctional hBfunctional

/-- Witt-vector Frobenius on the coefficients of the changed-uniformizer
intertwiner is substitution by the multiplicative endomorphism attached to
the unit changing the uniformizer. -/
theorem padicChangedUniformizerIntertwiner_frobenius
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.map WittVector.frobenius
        (padicChangedUniformizerIntertwiner p u) =
      PowerSeries.subst
        (padicCompletedMultiplicativeScalarEndomorphism p
          (u : (padicLocalField p).valuationSubring))
        (padicChangedUniformizerIntertwiner p u) := by
  let H := padicChangedUniformizerIntertwiner p u
  let U :=
    padicCompletedMultiplicativeScalarEndomorphism p
      (u : (padicLocalField p).valuationSubring)
  let E := padicCompletedMultiplicativeSeries p
  let Ebar := padicCompletedChangedStandardSeries p u
  let Phi := PowerSeries.map WittVector.frobenius H
  let Phi2 := PowerSeries.map WittVector.frobenius Phi
  let epsilon : padicCompletedUnramifiedWittRing p :=
    (padicChangedUniformizerLinearCoefficient p u :
      padicCompletedUnramifiedWittRing p)
  let alpha : padicCompletedUnramifiedWittRing p :=
    (padicValuationUnitToCompletedUnramifiedWittUnit p u :
      padicCompletedUnramifiedWittRing p)
  let A := PowerSeries.subst U H
  have hHconstant : PowerSeries.constantCoeff H = 0 := by
    simpa only [H] using
      padicChangedUniformizerIntertwiner_constantCoeff p u
  have hHlinear :
      HasLinearTerm H (fun _ : Unit => epsilon) := by
    apply powerSeries_hasLinearTerm_of_constantCoeff_coeff_one
      H epsilon hHconstant
    simpa only [H, epsilon] using
      padicChangedUniformizerIntertwiner_coeff_one p u
  have hUlinear :
      HasLinearTerm U (fun _ : Unit => alpha) := by
    have h :=
      padicCompletedMultiplicativeScalarEndomorphism_hasLinearTerm p
        (u : (padicLocalField p).valuationSubring)
    change HasLinearTerm U
      (fun _ : Unit =>
        padicValuationSubringToCompletedUnramifiedWittRing p
          (u : (padicLocalField p).valuationSubring))
    simpa only [U] using h
  have hHsubst : PowerSeries.HasSubst H :=
    hHlinear.hasSubst
  have hUsubst : PowerSeries.HasSubst U :=
    hUlinear.hasSubst
  have hEsubst : PowerSeries.HasSubst E :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simpa only [E] using
        padicCompletedMultiplicativeSeries_constantCoeff p)
  have hHfunctional :
      PowerSeries.subst H Ebar =
        PowerSeries.subst E Phi := by
    simpa only [H, Ebar, E, Phi,
      padicCompletedChangedStandardSeries,
      padicCompletedMultiplicativeSeries] using
      padicChangedUniformizerIntertwiner_functionalEquation p u
  have hUcommutes :
      PowerSeries.subst U E =
        PowerSeries.subst E U := by
    simpa only [U, E] using
      padicCompletedMultiplicativeScalarEndomorphism_commutes p
        (u : (padicLocalField p).valuationSubring)
  have hmapA :
      PowerSeries.map WittVector.frobenius A =
        PowerSeries.subst U Phi := by
    simp only [A, Phi]
    change MvPowerSeries.map _ _ = _
    rw [PowerSeries.map_subst hUsubst]
    change
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) = _
    rw [padicCompletedMultiplicativeScalarEndomorphism_frobenius]
  have hPhiFunctional :
      PowerSeries.subst Phi Ebar =
        PowerSeries.subst E Phi2 := by
    have h :=
      congrArg (PowerSeries.map WittVector.frobenius) hHfunctional
    change MvPowerSeries.map _ _ = MvPowerSeries.map _ _ at h
    rw [PowerSeries.map_subst hHsubst,
      PowerSeries.map_subst hEsubst] at h
    change
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) =
        PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) at h
    rw [
      padicCompletedChangedStandardSeries_frobenius,
      padicCompletedMultiplicativeSeries_frobenius] at h
    simpa only [Phi, Phi2] using h
  have hAfunctional :
      PowerSeries.subst A Ebar =
        PowerSeries.subst E
          (PowerSeries.map WittVector.frobenius A) := by
    calc
      PowerSeries.subst A Ebar =
          PowerSeries.subst U
            (PowerSeries.subst H Ebar) := by
        simpa only [A] using
          (PowerSeries.subst_comp_subst_apply
            hHsubst hUsubst Ebar).symm
      _ = PowerSeries.subst U
            (PowerSeries.subst E Phi) := by
        rw [hHfunctional]
      _ = PowerSeries.subst
            (PowerSeries.subst U E) Phi :=
        PowerSeries.subst_comp_subst_apply
          hEsubst hUsubst Phi
      _ = PowerSeries.subst
            (PowerSeries.subst E U) Phi := by
        rw [hUcommutes]
      _ = PowerSeries.subst E
            (PowerSeries.subst U Phi) :=
        (PowerSeries.subst_comp_subst_apply
          hUsubst hEsubst Phi).symm
      _ = PowerSeries.subst E
            (PowerSeries.map WittVector.frobenius A) := by
        rw [hmapA]
  have hAlinearRaw :=
    hHlinear.subst
      (G := fun _ : Unit => U)
      (M := fun _ : Unit => fun _ : Unit => alpha)
      (fun _ => hUlinear)
  have hAlinear :
      HasLinearTerm A
        (fun _ : Unit => epsilon * alpha) := by
    simpa [A, PowerSeries.subst_def] using hAlinearRaw
  have hPhiConstant : PowerSeries.constantCoeff Phi = 0 := by
    simpa only [Phi] using
      padicChangedUniformizerFrobenius_constantCoeff_eq_zero
        p H hHconstant
  have hPhiLinear :
      PowerSeries.coeff 1 Phi = epsilon * alpha := by
    change
      WittVector.frobenius
          (PowerSeries.coeff 1 H) =
        epsilon * alpha
    rw [show PowerSeries.coeff 1 H = epsilon by
      simpa only [H, epsilon] using
        padicChangedUniformizerIntertwiner_coeff_one p u]
    simpa only [epsilon, alpha] using
      padicChangedUniformizerLinearCoefficient_frobenius p u
  have hPhiFunctional' :
      PowerSeries.subst Phi Ebar =
        PowerSeries.subst E
          (PowerSeries.map WittVector.frobenius Phi) := by
    simpa only [Phi2] using hPhiFunctional
  have hAfunctional' :
      PowerSeries.subst A Ebar =
        PowerSeries.subst E
          (PowerSeries.map WittVector.frobenius A) :=
    hAfunctional
  exact
    padicChangedUniformizerIntertwiner_unique p u
      hPhiConstant
      hAlinear.constantCoeff_eq_zero
      (hPhiLinear.trans (hAlinear.coeff_single ()).symm)
      hPhiFunctional' hAfunctional'

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_MultiplicativeEvaluation_Core
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.zHatUnitsDecomposition_freeCoordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Changed-uniformizer evaluation on completed p-adic levels

This endpoint evaluates the genuine changed-uniformizer intertwiner at the
completed multiplicative primitive point.  It proves the exact scalar,
Frobenius, root, and level-embedding identities used by the completed
Lubin--Tate tower.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

attribute [local instance]
  padicCompletedMultiplicativeTargetWithIdeal
  padicCompletedMultiplicativeTargetCompleteSpace
  padicCompletedMultiplicativeTargetT2Space

/-- Genuine completed-level evaluation of the changed-uniformizer scalar
intertwining identity. -/
theorem padicChangedUniformizerIntertwiner_endomorphism_evaluation
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (a : (padicLocalField p).valuationSubring) (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    padicCompletedLevelPowerSeriesEval p n
        (padicCompletedMultiplicativeScalarEndomorphismValue
          p n x hx a)
        (padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
          p n x hx a)
        (padicChangedUniformizerIntertwiner p u) =
      padicCompletedChangedStandardScalarEndomorphismValue p u n
        (padicCompletedLevelPowerSeriesEval p n x hx
          (padicChangedUniformizerIntertwiner p u))
        (padicCompletedLevelPowerSeriesEval_hasEval p n x hx
          (padicChangedUniformizerIntertwiner p u)
          (padicChangedUniformizerIntertwiner_hasSubst p u))
        a := by
  let M := padicCompletedMultiplicativeScalarEndomorphism p a
  let H := padicChangedUniformizerIntertwiner p u
  let S := padicCompletedChangedStandardScalarEndomorphism p u a
  let xM :=
    padicCompletedMultiplicativeScalarEndomorphismValue p n x hx a
  let xH := padicCompletedLevelPowerSeriesEval p n x hx H
  let hxM : PowerSeries.HasEval xM :=
    padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
      p n x hx a
  let hxH : PowerSeries.HasEval xH :=
    padicCompletedLevelPowerSeriesEval_hasEval p n x hx H
      (padicChangedUniformizerIntertwiner_hasSubst p u)
  calc
    padicCompletedLevelPowerSeriesEval p n xM hxM H =
        padicCompletedLevelPowerSeriesEval p n x hx
          (PowerSeries.subst M H) := by
      exact
        (padicCompletedLevelPowerSeriesEval_subst p n x hx
          M H
          (padicCompletedMultiplicativeScalarEndomorphism_hasSubst p a)
          hxM).symm
    _ =
        padicCompletedLevelPowerSeriesEval p n x hx
          (PowerSeries.subst H S) := by
      rw [padicChangedUniformizerIntertwiner_endomorphism]
    _ =
        padicCompletedLevelPowerSeriesEval p n xH hxH S := by
      exact
        padicCompletedLevelPowerSeriesEval_subst p n x hx
          H S (padicChangedUniformizerIntertwiner_hasSubst p u) hxH

/-- The changed-uniformizer theta value is killed by the `n + 1`-fold
changed standard division-polynomial iterate. -/
theorem padicChangedUniformizerThetaValue_iterate_succ_eq_zero
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicChangedUniformizerThetaValue p u n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (standardLubinTateChangedUniformizer
            (padicLocalField p)
            (padicIntEquivValuationSubring p (p : ℤ_[p])) u)
          (n + 1)) =
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let πu : (padicLocalField p).valuationSubring :=
    standardLubinTateChangedUniformizer
      (padicLocalField p) π u
  change
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicChangedUniformizerThetaValue p u n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p) πu (n + 1)) =
      0
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  let xChanged :=
    padicCompletedMultiplicativeScalarEndomorphismValue
      p n x hx (πu ^ (n + 1))
  let hxChanged : PowerSeries.HasEval xChanged :=
    padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
      p n x hx (πu ^ (n + 1))
  have hbridge :=
    padicChangedUniformizerIntertwiner_endomorphism_evaluation
      p u (πu ^ (n + 1)) n x hx
  have hxChangedZero : xChanged = 0 := by
    change
      padicCompletedMultiplicativeScalarEndomorphismValue p n
          (padicCompletedMultiplicativePrimitivePoint p n)
          (padicCompletedMultiplicativePrimitivePoint_hasEval p n)
          ((standardLubinTateChangedUniformizer
            (padicLocalField p)
            (padicIntEquivValuationSubring p (p : ℤ_[p])) u) ^
              (n + 1)) =
        0
    exact
      padicCompletedMultiplicativePrimitivePoint_changedUniformizer_pow_succ_eq_zero
        p u n
  have hleftZero :
      padicCompletedLevelPowerSeriesEval p n xChanged hxChanged
          (padicChangedUniformizerIntertwiner p u) =
        0 := by
    calc
      _ =
          padicCompletedLevelPowerSeriesEval p n
            0 PowerSeries.HasEval.zero
            (padicChangedUniformizerIntertwiner p u) :=
        padicCompletedLevelPowerSeriesEval_congr_point p n
          hxChanged PowerSeries.HasEval.zero hxChangedZero
          (padicChangedUniformizerIntertwiner p u)
      _ = 0 :=
        padicChangedUniformizerIntertwiner_eval_zero p u n
  have hrightZero :
      padicCompletedChangedStandardScalarEndomorphismValue p u n
          (padicChangedUniformizerThetaValue p u n)
          (padicChangedUniformizerThetaValue_hasEval p u n)
          (πu ^ (n + 1)) =
        0 :=
    hbridge.symm.trans hleftZero
  have hpow :
      padicCompletedChangedStandardScalarEndomorphismValue p u n
          (padicChangedUniformizerThetaValue p u n)
          (padicChangedUniformizerThetaValue_hasEval p u n)
          (πu ^ (n + 1)) =
        Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (padicChangedUniformizerThetaValue p u n)
          (standardLubinTatePolynomialIterate
            (padicLocalField p) πu (n + 1)) := by
    simpa only [π, πu] using
      (padicCompletedChangedStandardScalarEndomorphismValue_uniformizer_pow
        p u n
        (padicChangedUniformizerThetaValue p u n)
        (padicChangedUniformizerThetaValue_hasEval p u n)
        (n + 1))
  exact hpow.symm.trans hrightZero

/-- The changed-uniformizer theta value is not killed one level early. -/
theorem padicChangedUniformizerThetaValue_iterate_ne_zero
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicChangedUniformizerThetaValue p u n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (standardLubinTateChangedUniformizer
            (padicLocalField p)
            (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n) ≠
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let πu : (padicLocalField p).valuationSubring :=
    standardLubinTateChangedUniformizer
      (padicLocalField p) π u
  change
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicChangedUniformizerThetaValue p u n)
        (standardLubinTatePolynomialIterate
          (padicLocalField p) πu n) ≠
      0
  intro hzero
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  let xChanged :=
    padicCompletedMultiplicativeScalarEndomorphismValue
      p n x hx (πu ^ n)
  let hxChanged : PowerSeries.HasEval xChanged :=
    padicCompletedMultiplicativeScalarEndomorphismValue_hasEval
      p n x hx (πu ^ n)
  have hbridge :=
    padicChangedUniformizerIntertwiner_endomorphism_evaluation
      p u (πu ^ n) n x hx
  have hpow :
      padicCompletedChangedStandardScalarEndomorphismValue p u n
          (padicChangedUniformizerThetaValue p u n)
          (padicChangedUniformizerThetaValue_hasEval p u n)
          (πu ^ n) =
        Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (padicChangedUniformizerThetaValue p u n)
          (standardLubinTatePolynomialIterate
            (padicLocalField p) πu n) := by
    simpa only [π, πu] using
      (padicCompletedChangedStandardScalarEndomorphismValue_uniformizer_pow
        p u n
        (padicChangedUniformizerThetaValue p u n)
        (padicChangedUniformizerThetaValue_hasEval p u n) n)
  have hrightZero :
      padicCompletedChangedStandardScalarEndomorphismValue p u n
          (padicChangedUniformizerThetaValue p u n)
          (padicChangedUniformizerThetaValue_hasEval p u n)
          (πu ^ n) =
        0 :=
    hpow.trans hzero
  have hleftZero :
      padicCompletedLevelPowerSeriesEval p n xChanged hxChanged
          (padicChangedUniformizerIntertwiner p u) =
        0 := by
    exact hbridge.trans hrightZero
  have hxChangedZero : xChanged = 0 := by
    apply padicChangedUniformizerIntertwiner_eval_injective
      p u n hxChanged PowerSeries.HasEval.zero
    exact hleftZero.trans
      (padicChangedUniformizerIntertwiner_eval_zero p u n).symm
  apply
    padicCompletedMultiplicativePrimitivePoint_changedUniformizer_pow_ne_zero
      p u n
  change xChanged = 0
  exact hxChangedZero

/-- The changed-uniformizer theta value is an actual root of the genuine
changed primitive Lubin--Tate polynomial in the completed level. -/
theorem padicChangedUniformizerThetaValue_isRoot
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    ((standardLubinTatePrimitivePolynomial
        (padicLocalField p)
        (standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map
      (padicCompletedLevelPadicIntegerCoefficientHom p n)).IsRoot
        (padicChangedUniformizerThetaValue p u n) := by
  let F := padicLocalField p
  let πu : (padicLocalField p).valuationSubring :=
    standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) u
  let φ := padicCompletedLevelPadicIntegerCoefficientHom p n
  let theta := padicChangedUniformizerThetaValue p u n
  have hfactor :=
    congrArg (Polynomial.eval₂ φ theta)
      (standardLubinTatePolynomialIterate_succ_factor F πu n)
  rw [Polynomial.eval₂_mul,
    padicChangedUniformizerThetaValue_iterate_succ_eq_zero p u n]
      at hfactor
  have hprimitive :
      Polynomial.eval₂ φ theta
          (standardLubinTatePrimitivePolynomial F πu n) =
        0 :=
    (mul_eq_zero.mp hfactor.symm).resolve_left
      (padicChangedUniformizerThetaValue_iterate_ne_zero p u n)
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  exact hprimitive

/-- Field-valued form of the changed primitive-root equation. -/
theorem padicChangedUniformizerThetaValue_field_isRoot
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    ((standardLubinTatePrimitivePolynomialOverField
        (padicLocalField p)
        (standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map
      (algebraMap ℚ_[p] (padicCompletedLevelField p n))).IsRoot
        ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n) := by
  let F := padicLocalField p
  let πu : (padicLocalField p).valuationSubring :=
    standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) u
  let Q := standardLubinTatePrimitivePolynomial F πu n
  let theta := padicChangedUniformizerThetaValue p u n
  have hroot := padicChangedUniformizerThetaValue_isRoot p u n
  have hinteger :
      Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          theta Q =
        0 := by
    simpa only [Polynomial.IsRoot, Polynomial.eval_map, F, πu, Q, theta]
      using hroot
  have hcoe := congrArg
    (fun z : (padicCompletedLevelCompleteDVF p n).valuationSubring =>
      (z : padicCompletedLevelField p n)) hinteger
  have hfield :
      Polynomial.eval₂
          (padicCompletedLevelPadicFieldCoefficientHom p n)
          (theta : padicCompletedLevelField p n) Q =
        0 := by
    change
      ((Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          theta Q :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) =
        0 at hcoe
    rw [padicCompletedLevelPadicIntegerPolynomialEval_coe] at hcoe
    exact hcoe
  rw [standardLubinTatePrimitivePolynomialOverField,
    Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_map]
  change
    Polynomial.eval₂
        (padicCompletedLevelPadicFieldCoefficientHom p n)
        (theta : padicCompletedLevelField p n) Q =
      0
  exact hfield

/-- The theta value annihilates the minimal polynomial of the canonical
generator of the changed finite Lubin--Tate level. -/
theorem padicChangedUniformizerThetaValue_aeval_levelMinpoly
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let hπ :=
      standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u
    Polynomial.aeval
        ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n)
        (minpoly ℚ_[p] (standardLubinTateLevelPowerBasis hπ n).gen) =
      0 := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  change
    Polynomial.aeval
        ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n)
        (minpoly ℚ_[p] (standardLubinTateLevelPowerBasis hπ n).gen) =
      0
  rw [standardLubinTateLevelPowerBasis_minpoly hπ n,
    Polynomial.aeval_def]
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using
    padicChangedUniformizerThetaValue_field_isRoot p u n

/-- The genuine embedding of the changed finite Lubin--Tate level into
the completed standard level, sending its canonical generator to theta. -/
noncomputable def padicChangedUniformizerLevelEmbedding
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let hπ :=
      standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u
    standardLubinTateLevelField hπ n →ₐ[ℚ_[p]]
      padicCompletedLevelField p n := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let theta : padicCompletedLevelField p n :=
    ((padicChangedUniformizerThetaValue p u n :
      (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)
  change
    standardLubinTateLevelField hπ n →ₐ[ℚ_[p]]
      padicCompletedLevelField p n
  exact
    (standardLubinTateLevelPowerBasis hπ n).lift theta
      (by
        simpa only [theta] using
          padicChangedUniformizerThetaValue_aeval_levelMinpoly p u n)

/-- The changed-level embedding sends the canonical power-basis generator
to the actual theta value. -/
@[simp]
theorem padicChangedUniformizerLevelEmbedding_apply_gen
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let hπ :=
      standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u
    padicChangedUniformizerLevelEmbedding p u n
        (standardLubinTateLevelPowerBasis hπ n).gen =
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let theta : padicCompletedLevelField p n :=
    ((padicChangedUniformizerThetaValue p u n :
      (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)
  change
    (standardLubinTateLevelPowerBasis hπ n).lift
        theta
        (padicChangedUniformizerThetaValue_aeval_levelMinpoly p u n)
        (standardLubinTateLevelPowerBasis hπ n).gen =
      theta
  exact
    (standardLubinTateLevelPowerBasis hπ n).lift_gen _ _

/-- Evaluating Frobenius on the coefficients of the changed-uniformizer
intertwiner is the same as first applying the multiplicative unit
endomorphism to the evaluation point and then evaluating the original
intertwiner. -/
theorem padicChangedUniformizerIntertwiner_frobenius_evaluation
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    padicCompletedLevelPowerSeriesEval p n x hx
        (PowerSeries.map WittVector.frobenius
          (padicChangedUniformizerIntertwiner p u)) =
      padicCompletedLevelPowerSeriesEval p n
        (padicCompletedLevelPowerSeriesEval p n x hx
          (padicCompletedMultiplicativeUnitEndomorphism p u))
        (padicCompletedLevelPowerSeriesEval_hasEval p n x hx
          (padicCompletedMultiplicativeUnitEndomorphism p u)
          (padicCompletedMultiplicativeUnitEndomorphism_hasSubst p u))
        (padicChangedUniformizerIntertwiner p u) := by
  let U := padicCompletedMultiplicativeUnitEndomorphism p u
  let Θ := padicChangedUniformizerIntertwiner p u
  have hseries :
      PowerSeries.map WittVector.frobenius Θ =
        PowerSeries.subst U Θ := by
    simpa only [U, Θ, padicCompletedMultiplicativeUnitEndomorphism] using
      (padicChangedUniformizerIntertwiner_frobenius p u)
  rw [hseries]
  exact
    padicCompletedLevelPowerSeriesEval_subst p n x hx U Θ
      (padicCompletedMultiplicativeUnitEndomorphism_hasSubst p u)
      (padicCompletedLevelPowerSeriesEval_hasEval p n x hx U
        (padicCompletedMultiplicativeUnitEndomorphism_hasSubst p u))

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedPrimitiveAction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.Padic.padicUnitFiniteFactor_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.zHatUnitsDecomposition_freeCoordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Primitive unit action on a completed p-adic Lubin--Tate level

The completed level is defined as the splitting field of the standard
primitive Lubin--Tate polynomial over the completed maximal-unramified
field.  This file identifies all of its roots with the genuine finite
unit-parameter quotient of the original p-adic field.

The construction first embeds the ordinary standard Lubin--Tate level into
the completed splitting field by sending its canonical primitive generator
to the chosen completed root.  The already constructed finite-level
unit-parameter automorphisms then give every completed root.  Comparing
cardinalities proves that these are all the roots, and hence that each one
generates the completed splitting field.
-/

noncomputable section

open scoped Polynomial PowerSeries

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

noncomputable local instance
    padicCompletedActionTargetWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (padicCompletedLevelCompleteDVF p n).valuationSubring where
  i := (padicCompletedLevelCompleteDVF p n).maximalIdeal

/-- The chosen completed primitive root annihilates the original standard
primitive polynomial over `ℚ_[p]`. -/
theorem padicCompletedPrimitiveRoot_aeval_standardPrimitivePolynomial
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.aeval (padicCompletedPrimitiveRoot p n)
        (standardLubinTatePrimitivePolynomialOverField
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) n) =
      0 := by
  have hroot := padicCompletedPrimitiveRoot_isRoot p n
  simpa [Polynomial.IsRoot, padicCompletedPrimitivePolynomial,
    standardLubinTatePrimitivePolynomialOverField,
    Polynomial.aeval_def, Polynomial.eval_map, Polynomial.eval₂_map,
    IsScalarTower.algebraMap_eq ℚ_[p]
      (padicCompletedUnramifiedField p) (padicCompletedLevelField p n),
    padicCompletedLevelPadicFieldCoefficientHom] using hroot

/-- The ordinary standard Lubin--Tate level embeds into the completed
splitting field by sending its canonical generator to the chosen completed
root. -/
noncomputable def padicStandardLevelEmbedding
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ :=
      padicMultiplicativeLubinTateSeries_isUniformizer p
    standardLubinTateLevelField hπ n →ₐ[ℚ_[p]]
      padicCompletedLevelField p n := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  exact
    (standardLubinTateLevelPowerBasis hπ n).lift
      (padicCompletedPrimitiveRoot p n) (by
        exact (congrArg
          (fun f : Polynomial ℚ_[p] =>
            Polynomial.aeval (padicCompletedPrimitiveRoot p n) f)
          (standardLubinTateLevelPowerBasis_minpoly
            (F := padicLocalField p)
            (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n)).trans
          (padicCompletedPrimitiveRoot_aeval_standardPrimitivePolynomial p n))

/-- The standard-level embedding has the prescribed value on the canonical
primitive generator. -/
@[simp]
theorem padicStandardLevelEmbedding_apply_gen
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ :=
      padicMultiplicativeLubinTateSeries_isUniformizer p
    padicStandardLevelEmbedding p n
        (standardLubinTateLevelPowerBasis hπ n).gen =
      padicCompletedPrimitiveRoot p n := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  simp only [padicStandardLevelEmbedding, PowerBasis.lift_gen]

/-- A finite unit parameter, realized as a root in the completed splitting
field. -/
noncomputable def padicCompletedUnitParameterRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    padicCompletedLevelField p n := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  exact
    padicStandardLevelEmbedding p n
      (standardLubinTateUnitParameterLevelRoot
        (padicLocalField p) hπ n a)

/-- The identity unit parameter gives the chosen completed primitive root. -/
@[simp]
theorem padicCompletedUnitParameterRoot_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedUnitParameterRoot p n 1 =
      padicCompletedPrimitiveRoot p n := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  exact (congrArg (padicStandardLevelEmbedding p n)
    (standardLubinTateUnitParameterLevelRoot_one (padicLocalField p)
      (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n)).trans
    (padicStandardLevelEmbedding_apply_gen p n)

/-- Distinct finite unit parameters give distinct roots in the completed
level. -/
theorem padicCompletedUnitParameterRoot_injective
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Function.Injective (padicCompletedUnitParameterRoot p n) := by
  intro a b hab
  apply
    standardLubinTateUnitParameterLevelRoot_injective
      (padicLocalField p)
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
  exact (padicStandardLevelEmbedding p n).injective hab

/-- A completed parameter root annihilates the original primitive
polynomial over `ℚ_[p]`. -/
theorem padicCompletedUnitParameterRoot_aeval_standardPrimitivePolynomial
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    Polynomial.aeval (padicCompletedUnitParameterRoot p n a)
        (standardLubinTatePrimitivePolynomialOverField
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) n) =
      0 := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  have hlevel :=
    standardLubinTateUnitParameterLevelRoot_aeval_minpoly
      (padicLocalField p) hπ n a
  have hpoly := congrArg
    (fun f : Polynomial ℚ_[p] => Polynomial.aeval
      (standardLubinTateUnitParameterLevelRoot (padicLocalField p) hπ n a) f)
    (standardLubinTateLevelPowerBasis_minpoly
      (F := padicLocalField p)
      (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n)
  have hmap := congrArg (padicStandardLevelEmbedding p n) (hpoly.symm.trans hlevel)
  simpa only [map_zero, Polynomial.aeval_algHom_apply,
    padicCompletedUnitParameterRoot] using hmap

/-- Every completed finite-parameter point is a root of the genuine
completed primitive polynomial. -/
theorem padicCompletedUnitParameterRoot_isRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    ((padicCompletedPrimitivePolynomial p n).map
      (algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n))).IsRoot
      (padicCompletedUnitParameterRoot p n a) := by
  have hroot :=
    padicCompletedUnitParameterRoot_aeval_standardPrimitivePolynomial
      p n a
  simpa [Polynomial.IsRoot, padicCompletedPrimitivePolynomial,
    standardLubinTatePrimitivePolynomialOverField,
    Polynomial.aeval_def, Polynomial.eval_map, Polynomial.eval₂_map,
    IsScalarTower.algebraMap_eq ℚ_[p]
      (padicCompletedUnramifiedField p) (padicCompletedLevelField p n),
    padicCompletedLevelPadicFieldCoefficientHom] using hroot

theorem
    padicCompletedStandardScalarEndomorphismValue_congr_point
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    {x y : (padicCompletedLevelCompleteDVF p n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy : x = y) (a : (padicLocalField p).valuationSubring) :
    padicCompletedStandardScalarEndomorphismValue p n x hx a =
      padicCompletedStandardScalarEndomorphismValue p n y hy a := by
  subst y
  rfl

/-- The direct completed standard Lubin--Tate action of a p-adic unit on
the chosen integral primitive point. -/
noncomputable def padicCompletedStandardPrimitivePointUnitAction
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  padicCompletedStandardScalarEndomorphismValue p n
    (padicCompletedPrimitiveRootInteger p n)
    (padicCompletedPrimitiveRootInteger_hasEval p n)
    (u : (padicLocalField p).valuationSubring)

/-- A direct completed standard unit translate remains a convergent
evaluation point. -/
theorem padicCompletedStandardPrimitivePointUnitAction_hasEval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.HasEval
      (padicCompletedStandardPrimitivePointUnitAction p n u) :=
  padicCompletedStandardScalarEndomorphismValue_hasEval p n
    (padicCompletedPrimitiveRootInteger p n)
    (padicCompletedPrimitiveRootInteger_hasEval p n)
    (u : (padicLocalField p).valuationSubring)

/-- The identity unit fixes the chosen completed standard primitive point. -/
@[simp]
theorem padicCompletedStandardPrimitivePointUnitAction_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedStandardPrimitivePointUnitAction p n 1 =
      padicCompletedPrimitiveRootInteger p n := by
  simp [padicCompletedStandardPrimitivePointUnitAction]

/-- A direct completed standard unit translate is killed at level
`n + 1`. -/
theorem
    padicCompletedStandardPrimitivePointUnitAction_iterate_succ_eq_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicCompletedStandardPrimitivePointUnitAction p n u)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) (n + 1)) =
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let x := padicCompletedPrimitiveRootInteger p n
  let hx := padicCompletedPrimitiveRootInteger_hasEval p n
  let y := padicCompletedStandardPrimitivePointUnitAction p n u
  let hy := padicCompletedStandardPrimitivePointUnitAction_hasEval p n u
  have hkill :
      padicCompletedStandardScalarEndomorphismValue p n x hx
          (π ^ (n + 1)) =
        0 := by
    exact
      (padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
        p n x hx (n + 1)).trans (by
          simpa only [x] using
            padicCompletedPrimitiveRootInteger_iterate_succ_eq_zero p n)
  rw [← padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
    p n y hy (n + 1)]
  calc
    padicCompletedStandardScalarEndomorphismValue p n y hy
        (π ^ (n + 1)) =
      padicCompletedStandardScalarEndomorphismValue p n x hx
        (π ^ (n + 1) *
          (u : (padicLocalField p).valuationSubring)) := by
      simpa only [y,
        padicCompletedStandardPrimitivePointUnitAction] using
        (padicCompletedStandardScalarEndomorphismValue_mul
          p n x hx (π ^ (n + 1))
            (u : (padicLocalField p).valuationSubring)).symm
    _ =
      padicCompletedStandardScalarEndomorphismValue p n x hx
        ((u : (padicLocalField p).valuationSubring) *
          π ^ (n + 1)) := by
      rw [mul_comm]
    _ =
      padicCompletedStandardScalarEndomorphismValue p n
        (padicCompletedStandardScalarEndomorphismValue p n x hx
          (π ^ (n + 1)))
        (padicCompletedStandardScalarEndomorphismValue_hasEval
          p n x hx (π ^ (n + 1)))
        (u : (padicLocalField p).valuationSubring) :=
      padicCompletedStandardScalarEndomorphismValue_mul
        p n x hx (u : (padicLocalField p).valuationSubring)
          (π ^ (n + 1))
    _ =
      padicCompletedStandardScalarEndomorphismValue p n
        0 PowerSeries.HasEval.zero
        (u : (padicLocalField p).valuationSubring) := by
      exact
        padicCompletedStandardScalarEndomorphismValue_congr_point
          p n
          (padicCompletedStandardScalarEndomorphismValue_hasEval
            p n x hx (π ^ (n + 1)))
          PowerSeries.HasEval.zero hkill
          (u : (padicLocalField p).valuationSubring)
    _ = 0 :=
      padicCompletedStandardScalarEndomorphismValue_zero p n
        (u : (padicLocalField p).valuationSubring)

/-- A direct completed standard unit translate is not killed one level
early. -/
theorem
    padicCompletedStandardPrimitivePointUnitAction_iterate_ne_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicCompletedStandardPrimitivePointUnitAction p n u)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) n) ≠
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let x := padicCompletedPrimitiveRootInteger p n
  let hx := padicCompletedPrimitiveRootInteger_hasEval p n
  let y := padicCompletedStandardPrimitivePointUnitAction p n u
  let hy := padicCompletedStandardPrimitivePointUnitAction_hasEval p n u
  intro hyzero
  have hyEvalZero :
      padicCompletedStandardScalarEndomorphismValue p n y hy (π ^ n) =
        0 := by
    exact
      (padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
        p n y hy n).trans (by
          simpa only [y] using hyzero)
  let z :=
    padicCompletedStandardScalarEndomorphismValue p n x hx (π ^ n)
  let hz : PowerSeries.HasEval z :=
    padicCompletedStandardScalarEndomorphismValue_hasEval
      p n x hx (π ^ n)
  have huzero :
      padicCompletedStandardScalarEndomorphismValue p n z hz
          (u : (padicLocalField p).valuationSubring) =
        0 := by
    calc
      _ =
          padicCompletedStandardScalarEndomorphismValue p n x hx
            ((u : (padicLocalField p).valuationSubring) * π ^ n) := by
        simpa only [z] using
          (padicCompletedStandardScalarEndomorphismValue_mul
            p n x hx (u : (padicLocalField p).valuationSubring)
              (π ^ n)).symm
      _ =
          padicCompletedStandardScalarEndomorphismValue p n x hx
            (π ^ n * (u : (padicLocalField p).valuationSubring)) := by
        rw [mul_comm]
      _ =
          padicCompletedStandardScalarEndomorphismValue p n y hy
            (π ^ n) := by
        simpa only [y,
          padicCompletedStandardPrimitivePointUnitAction] using
          padicCompletedStandardScalarEndomorphismValue_mul
            p n x hx (π ^ n)
              (u : (padicLocalField p).valuationSubring)
      _ = 0 := hyEvalZero
  have hzzero : z = 0 := by
    apply
      padicCompletedStandardScalarEndomorphismValue_unit_injective
        p n u hz PowerSeries.HasEval.zero
    rw [huzero,
      padicCompletedStandardScalarEndomorphismValue_zero]
  apply padicCompletedPrimitiveRootInteger_iterate_ne_zero p n
  rw [← padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
    p n x hx n]
  exact hzzero

/-- The direct completed standard action of every p-adic unit is a root of
the genuine completed primitive polynomial. -/
theorem padicCompletedStandardPrimitivePointUnitAction_isRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    ((padicCompletedPrimitivePolynomial p n).map
      (algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n))).IsRoot
      ((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n) := by
  let F := padicLocalField p
  let π : F.valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let y := padicCompletedStandardPrimitivePointUnitAction p n u
  have hsucc :=
    padicCompletedStandardPrimitivePointUnitAction_iterate_succ_eq_zero
      p n u
  have hn :=
    padicCompletedStandardPrimitivePointUnitAction_iterate_ne_zero
      p n u
  have hfactor :=
    congrArg
      (Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) y)
      (standardLubinTatePolynomialIterate_succ_factor F π n)
  rw [hsucc, Polynomial.eval₂_mul] at hfactor
  have hprimitive :
      Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n) y
          (standardLubinTatePrimitivePolynomial F π n) =
        0 :=
    (mul_eq_zero.mp hfactor.symm).resolve_left hn
  have hcoe := congrArg
    (fun z : (padicCompletedLevelCompleteDVF p n).valuationSubring =>
      (z : padicCompletedLevelField p n)) hprimitive
  change
    ((Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) y
        (standardLubinTatePrimitivePolynomial F π n) :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
        0 at hcoe
  rw [padicCompletedLevelPadicIntegerPolynomialEval_coe] at hcoe
  simpa [Polynomial.IsRoot, padicCompletedPrimitivePolynomial,
    standardLubinTatePrimitivePolynomialOverField,
    Polynomial.eval_map, Polynomial.eval₂_map,
    padicCompletedLevelPadicFieldCoefficientHom, F, π, y] using hcoe

/-- A finite unit parameter, regarded as an element of the full root set in
the completed splitting field. -/
noncomputable def padicCompletedUnitParameterRootSet
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    (padicCompletedPrimitivePolynomial p n).rootSet
      (padicCompletedLevelField p n) :=
  ⟨padicCompletedUnitParameterRoot p n a,
    Polynomial.mem_rootSet.mpr
      ⟨(padicCompletedPrimitivePolynomial_monic p n).ne_zero,
        by
          rw [Polynomial.aeval_def, ← Polynomial.eval_map]
          exact padicCompletedUnitParameterRoot_isRoot p n a⟩⟩

/-- The root-set realization of finite unit parameters is injective. -/
theorem padicCompletedUnitParameterRootSet_injective
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Function.Injective (padicCompletedUnitParameterRootSet p n) := by
  intro a b hab
  apply padicCompletedUnitParameterRoot_injective p n
  exact congrArg Subtype.val hab

/-- The completed primitive polynomial has exactly its degree many roots in
the completed splitting field. -/
theorem padicCompletedPrimitiveRootSet_natCard
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Nat.card
        ((padicCompletedPrimitivePolynomial p n).rootSet
          (padicCompletedLevelField p n)) =
      (p - 1) * p ^ n := by
  rw [Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree
      (padicCompletedPrimitivePolynomial_separable p n)
      (padicCompletedPrimitivePolynomial_splits p n),
    padicCompletedPrimitivePolynomial_natDegree]

/-- The finite p-adic unit-parameter quotient has the degree of the
completed primitive polynomial. -/
theorem padicStandardUnitParameter_natCard
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Nat.card (standardLubinTateUnitParameter (padicLocalField p) n) =
      (p - 1) * p ^ n := by
  have hcard :
      Nat.card (padicLocalField p).residueField = p := by
    simpa [padicLocalField] using
      padicCompleteDVF_residueField_card p
  rw [standardLubinTateUnitParameter_natCard, hcard]

/-- Finite p-adic unit parameters enumerate every root of the completed
primitive polynomial. -/
theorem padicCompletedUnitParameterRootSet_bijective
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Function.Bijective (padicCompletedUnitParameterRootSet p n) := by
  apply
    (Nat.bijective_iff_injective_and_card
      (padicCompletedUnitParameterRootSet p n)).mpr
  exact
    ⟨padicCompletedUnitParameterRootSet_injective p n,
      (padicStandardUnitParameter_natCard p n).trans
        (padicCompletedPrimitiveRootSet_natCard p n).symm⟩

/-- A parameter root is itself a power-basis generator of the ordinary
standard level. -/
noncomputable def padicStandardLevelUnitParameterPowerBasis
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    let hπ :=
      padicMultiplicativeLubinTateSeries_isUniformizer p
    PowerBasis ℚ_[p] (standardLubinTateLevelField hπ n) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  exact
    (standardLubinTateLevelPowerBasis hπ n).map
      (standardLubinTateUnitParameterAlgEquiv
        (padicLocalField p) hπ n a)

/-- The generator of the parameter power basis is the corresponding
finite-level parameter root. -/
@[simp]
theorem padicStandardLevelUnitParameterPowerBasis_gen
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    let hπ :=
      padicMultiplicativeLubinTateSeries_isUniformizer p
    (padicStandardLevelUnitParameterPowerBasis p n a).gen =
      standardLubinTateUnitParameterLevelRoot
        (padicLocalField p) hπ n a := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  simp only [padicStandardLevelUnitParameterPowerBasis,
    PowerBasis.map_gen]
  exact standardLubinTateUnitParameterAlgEquiv_apply_gen
    (padicLocalField p)
    (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n a

theorem padicPolynomialAeval_mem_completedUnramifiedAdjoin
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : padicCompletedLevelField p n) (f : Polynomial ℚ_[p]) :
    Polynomial.aeval x f ∈
      Algebra.adjoin (padicCompletedUnramifiedField p)
        ({x} : Set (padicCompletedLevelField p n)) := by
  let g :=
    f.map (algebraMap ℚ_[p] (padicCompletedUnramifiedField p))
  have hmem :=
    g.aeval_mem_adjoin_singleton (padicCompletedUnramifiedField p) x
  simpa only [Polynomial.aeval_def, Polynomial.eval₂_map,
    IsScalarTower.algebraMap_eq ℚ_[p]
      (padicCompletedUnramifiedField p) (padicCompletedLevelField p n),
    g]
    using hmem

/-- Every completed parameter root is a polynomial expression in any other
completed parameter root, with coefficients in the completed-unramified
base. -/
theorem padicCompletedUnitParameterRoot_mem_adjoin
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a b : standardLubinTateUnitParameter (padicLocalField p) n) :
    padicCompletedUnitParameterRoot p n b ∈
      Algebra.adjoin (padicCompletedUnramifiedField p)
        ({padicCompletedUnitParameterRoot p n a} :
          Set (padicCompletedLevelField p n)) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let pb := padicStandardLevelUnitParameterPowerBasis p n a
  let z :=
    standardLubinTateUnitParameterLevelRoot
      (padicLocalField p) hπ n b
  let S : Subalgebra (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) :=
    Algebra.adjoin (padicCompletedUnramifiedField p)
      ({padicCompletedUnitParameterRoot p n a} :
        Set (padicCompletedLevelField p n))
  obtain ⟨f, hf⟩ := pb.exists_eq_aeval' z
  have hgen :
      padicStandardLevelEmbedding p n pb.gen =
        padicCompletedUnitParameterRoot p n a := by
    rw [padicStandardLevelUnitParameterPowerBasis_gen]
    rfl
  have hzimage :
      padicStandardLevelEmbedding p n z =
        Polynomial.aeval (padicCompletedUnitParameterRoot p n a) f := by
    calc
      padicStandardLevelEmbedding p n z =
          padicStandardLevelEmbedding p n
            (Polynomial.aeval pb.gen f) :=
        congrArg (padicStandardLevelEmbedding p n) hf
      _ = Polynomial.aeval
          (padicStandardLevelEmbedding p n pb.gen) f :=
        (Polynomial.aeval_algHom_apply
          (padicStandardLevelEmbedding p n) pb.gen f).symm
      _ = Polynomial.aeval
          (padicCompletedUnitParameterRoot p n a) f := by
        rw [hgen]
  change padicStandardLevelEmbedding p n z ∈ S
  rw [hzimage]
  exact
    padicPolynomialAeval_mem_completedUnramifiedAdjoin
      p n (padicCompletedUnitParameterRoot p n a) f

/-- All roots of the completed primitive polynomial lie in the field
generated by any chosen parameter root. -/
theorem padicCompletedPrimitiveRootSet_subset_adjoin_parameter
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    ((padicCompletedPrimitivePolynomial p n).rootSet
        (padicCompletedLevelField p n) :
      Set (padicCompletedLevelField p n)) ⊆
      Algebra.adjoin (padicCompletedUnramifiedField p)
        ({padicCompletedUnitParameterRoot p n a} :
          Set (padicCompletedLevelField p n)) := by
  intro y hy
  let yroot :
      (padicCompletedPrimitivePolynomial p n).rootSet
        (padicCompletedLevelField p n) :=
    ⟨y, hy⟩
  obtain ⟨b, hb⟩ :=
    (padicCompletedUnitParameterRootSet_bijective p n).surjective yroot
  have hby :
      padicCompletedUnitParameterRoot p n b = y :=
    congrArg Subtype.val hb
  rw [← hby]
  exact padicCompletedUnitParameterRoot_mem_adjoin p n a b

/-- Every completed parameter root generates the completed splitting field
over the completed maximal-unramified base. -/
theorem padicCompletedUnitParameterRoot_adjoin_eq_top
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    Algebra.adjoin (padicCompletedUnramifiedField p)
        ({padicCompletedUnitParameterRoot p n a} :
          Set (padicCompletedLevelField p n)) =
      ⊤ := by
  have hall :
      Algebra.adjoin (padicCompletedUnramifiedField p)
          ((padicCompletedPrimitivePolynomial p n).rootSet
            (padicCompletedLevelField p n) :
            Set (padicCompletedLevelField p n)) ≤
        Algebra.adjoin (padicCompletedUnramifiedField p)
          ({padicCompletedUnitParameterRoot p n a} :
            Set (padicCompletedLevelField p n)) :=
    Algebra.adjoin_le
      (padicCompletedPrimitiveRootSet_subset_adjoin_parameter p n a)
  rw [padicCompletedPrimitivePolynomial_adjoin_rootSet] at hall
  exact top_unique hall

/-- Every direct completed standard unit translate generates the completed
splitting field over the completed maximal-unramified base. -/
theorem
    padicCompletedStandardPrimitivePointUnitAction_adjoin_eq_top
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    Algebra.adjoin (padicCompletedUnramifiedField p)
        ({((padicCompletedStandardPrimitivePointUnitAction p n u :
              (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n)} :
          Set (padicCompletedLevelField p n)) =
      ⊤ := by
  let y : padicCompletedLevelField p n :=
    ((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n)
  let yroot :
      (padicCompletedPrimitivePolynomial p n).rootSet
        (padicCompletedLevelField p n) :=
    ⟨y, Polynomial.mem_rootSet.mpr
      ⟨(padicCompletedPrimitivePolynomial_monic p n).ne_zero,
        by
          rw [Polynomial.aeval_def, ← Polynomial.eval_map]
          exact
            padicCompletedStandardPrimitivePointUnitAction_isRoot
              p n u⟩⟩
  obtain ⟨a, ha⟩ :=
    (padicCompletedUnitParameterRootSet_bijective p n).surjective yroot
  have hay :
      padicCompletedUnitParameterRoot p n a = y :=
    congrArg Subtype.val ha
  change
    Algebra.adjoin (padicCompletedUnramifiedField p)
        ({y} : Set (padicCompletedLevelField p n)) =
      ⊤
  rw [← hay]
  exact padicCompletedUnitParameterRoot_adjoin_eq_top p n a

/-- The chosen completed primitive root generates the completed splitting
field. -/
theorem padicCompletedPrimitiveRoot_adjoin_eq_top
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Algebra.adjoin (padicCompletedUnramifiedField p)
        ({padicCompletedPrimitiveRoot p n} :
          Set (padicCompletedLevelField p n)) =
      ⊤ := by
  simpa using
    (padicCompletedUnitParameterRoot_adjoin_eq_top p n
      (1 : standardLubinTateUnitParameter (padicLocalField p) n))

/-- The completed primitive polynomial is the minimal polynomial of the
chosen completed root. -/
theorem padicCompletedPrimitiveRoot_minpoly
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    minpoly (padicCompletedUnramifiedField p)
        (padicCompletedPrimitiveRoot p n) =
      padicCompletedPrimitivePolynomial p n := by
  have hroot :
      Polynomial.aeval (padicCompletedPrimitiveRoot p n)
          (padicCompletedPrimitivePolynomial p n) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact padicCompletedPrimitiveRoot_isRoot p n
  have hmin :=
    minpoly.eq_of_irreducible
      (padicCompletedPrimitivePolynomial_irreducible p n) hroot
  rw [(padicCompletedPrimitivePolynomial_monic p n).leadingCoeff,
    inv_one, Polynomial.C_1, mul_one] at hmin
  exact hmin.symm

/-- The chosen primitive root is integral over the completed-unramified
field. -/
theorem padicCompletedPrimitiveRoot_isIntegral_over_completedUnramified
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsIntegral (padicCompletedUnramifiedField p)
      (padicCompletedPrimitiveRoot p n) := by
  refine
    ⟨padicCompletedPrimitivePolynomial p n,
      padicCompletedPrimitivePolynomial_monic p n, ?_⟩
  have hroot := padicCompletedPrimitiveRoot_isRoot p n
  simpa [Polynomial.IsRoot, Polynomial.aeval_def,
    Polynomial.eval_map, Polynomial.eval₂_map] using hroot

/-- The power basis of the completed level generated by the chosen
primitive root. -/
noncomputable def padicCompletedPrimitivePowerBasis
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    PowerBasis (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) :=
  PowerBasis.ofAdjoinEqTop
    (padicCompletedPrimitiveRoot_isIntegral_over_completedUnramified p n)
    (padicCompletedPrimitiveRoot_adjoin_eq_top p n)

/-- The generator of the completed primitive power basis is the chosen
completed root. -/
@[simp]
theorem padicCompletedPrimitivePowerBasis_gen
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePowerBasis p n).gen =
      padicCompletedPrimitiveRoot p n :=
  PowerBasis.ofAdjoinEqTop_gen _ _

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedChangedUniformizerPrimitive
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.zHatUnitsDecomposition_freeCoordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Primitive changed-uniformizer points in the completed p-adic level

For a p-adic valuation-ring unit `u`, the primitive polynomial attached to
the changed uniformizer `u * p` remains Eisenstein after extension to the
completed-unramified Witt valuation ring.  Consequently the genuine theta
value constructed in the standard completed level has the changed
primitive polynomial as its minimal polynomial and generates the whole
completed level over the completed-unramified coefficient field.
-/

noncomputable section

open scoped Polynomial

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField

/-- The integral primitive polynomial for the changed uniformizer `u * p`
over the completed-unramified Witt valuation ring. -/
noncomputable def padicChangedCompletedPrimitivePolynomialInteger
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Polynomial
      (padicCompletedUnramifiedCompleteDVF p).valuationSubring :=
  (standardLubinTatePrimitivePolynomial
      (padicLocalField p)
      (standardLubinTateChangedUniformizer
        (padicLocalField p)
        (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map
    (padicCompletedUnramifiedIntegerMap p)

/-- The field-valued changed primitive polynomial after extension from
`ℚ_[p]` to the completed-unramified fraction field. -/
noncomputable def padicChangedCompletedPrimitivePolynomial
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Polynomial (padicCompletedUnramifiedField p) :=
  (standardLubinTatePrimitivePolynomialOverField
      (padicLocalField p)
      (standardLubinTateChangedUniformizer
        (padicLocalField p)
        (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map
    (algebraMap ℚ_[p] (padicCompletedUnramifiedField p))

/-- Passing the integral changed primitive polynomial to the fraction field
gives the field-valued changed primitive polynomial. -/
theorem padicChangedCompletedPrimitivePolynomialInteger_map
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicChangedCompletedPrimitivePolynomialInteger p u n).map
        (algebraMap
          (padicCompletedUnramifiedCompleteDVF p).valuationSubring
          (padicCompletedUnramifiedField p)) =
      padicChangedCompletedPrimitivePolynomial p u n := by
  let O := (padicLocalField p).valuationSubring
  let A := (padicCompletedUnramifiedCompleteDVF p).valuationSubring
  let E := padicCompletedUnramifiedField p
  let πu :=
    standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) u
  let Q :=
    standardLubinTatePrimitivePolynomial
      (padicLocalField p) πu n
  have hmaps :
      (algebraMap A E).comp
          (padicCompletedUnramifiedIntegerMap p) =
        (algebraMap ℚ_[p] E).comp (algebraMap O ℚ_[p]) := by
    ext z
    exact padicCompletedUnramifiedIntegerMap_coe p z
  change
    (Q.map (padicCompletedUnramifiedIntegerMap p)).map
        (algebraMap A E) =
      (Q.map (algebraMap O ℚ_[p])).map
        (algebraMap ℚ_[p] E)
  rw [Polynomial.map_map, Polynomial.map_map, hmaps]

/-- The integral changed primitive polynomial is monic. -/
theorem padicChangedCompletedPrimitivePolynomialInteger_monic
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicChangedCompletedPrimitivePolynomialInteger p u n).Monic :=
  (standardLubinTatePrimitivePolynomial_monic
    (padicLocalField p)
    (standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map _

/-- The field-valued changed primitive polynomial is monic. -/
theorem padicChangedCompletedPrimitivePolynomial_monic
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicChangedCompletedPrimitivePolynomial p u n).Monic :=
  (standardLubinTatePrimitivePolynomialOverField_monic
    (padicLocalField p)
    (standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).map _

/-- The integral changed primitive polynomial has degree
`(p - 1) * p ^ n`. -/
theorem padicChangedCompletedPrimitivePolynomialInteger_natDegree
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicChangedCompletedPrimitivePolynomialInteger p u n).natDegree =
      (p - 1) * p ^ n := by
  have hcard :
      Nat.card (padicLocalField p).residueField = p := by
    simpa [padicLocalField] using
      padicCompleteDVF_residueField_card p
  rw [padicChangedCompletedPrimitivePolynomialInteger,
    (standardLubinTatePrimitivePolynomial_monic
      (padicLocalField p)
      (standardLubinTateChangedUniformizer
        (padicLocalField p)
        (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).natDegree_map,
    standardLubinTatePrimitivePolynomial_natDegree, hcard]

/-- The changed primitive polynomial has degree `(p - 1) * p ^ n`. -/
theorem padicChangedCompletedPrimitivePolynomial_natDegree
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicChangedCompletedPrimitivePolynomial p u n).natDegree =
      (p - 1) * p ^ n := by
  have hcard :
      Nat.card (padicLocalField p).residueField = p := by
    simpa [padicLocalField] using
      padicCompleteDVF_residueField_card p
  rw [padicChangedCompletedPrimitivePolynomial,
    (standardLubinTatePrimitivePolynomialOverField_monic
      (padicLocalField p)
      (standardLubinTateChangedUniformizer
        (padicLocalField p)
        (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).natDegree_map,
    standardLubinTatePrimitivePolynomialOverField_natDegree, hcard]

/-- The image of the changed uniformizer `u * p` is a uniformizer of the
completed-unramified coefficient field. -/
theorem padicChangedCompletedUniformizer_isUniformizer
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) :
    let π :=
      padicIntEquivValuationSubring p (p : ℤ_[p])
    let πu :=
      standardLubinTateChangedUniformizer
        (padicLocalField p) π u
    (padicCompletedUnramifiedCompleteDVF p).valuation.IsUniformizer
      ((padicCompletedUnramifiedIntegerMap p πu :
        (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
          padicCompletedUnramifiedField p) := by
  let target := padicCompletedUnramifiedCompleteDVF p
  let π := padicIntEquivValuationSubring p (p : ℤ_[p])
  let πu :=
    standardLubinTateChangedUniformizer
      (padicLocalField p) π u
  let πE : target.valuationSubring :=
    padicCompletedUnramifiedIntegerMap p π
  let uE : target.valuationSubring :=
    padicCompletedUnramifiedIntegerMap p
      (u : (padicLocalField p).valuationSubring)
  have hπ :
      target.valuation.IsUniformizer
        (πE : padicCompletedUnramifiedField p) := by
    simpa only [target, π, πE] using
      padicCompletedUnramifiedIntegerMap_isUniformizer p
  have huE : IsUnit uE :=
    u.isUnit.map (padicCompletedUnramifiedIntegerMap p)
  apply hπ.of_associated
  have hmul : padicCompletedUnramifiedIntegerMap p πu = uE * πE :=
    map_mul (padicCompletedUnramifiedIntegerMap p)
      (u : (padicLocalField p).valuationSubring) π
  exact hmul.symm ▸ (associated_unit_mul_right πE uE huE)

/-- The integral changed primitive polynomial is weakly Eisenstein after
base change to the completed-unramified valuation ring. -/
theorem
    padicChangedCompletedPrimitivePolynomialInteger_isWeaklyEisensteinAt
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicChangedCompletedPrimitivePolynomialInteger p u n).IsWeaklyEisensteinAt
      (padicCompletedUnramifiedCompleteDVF p).maximalIdeal := by
  rw [← padicCompletedUnramifiedIntegerMap_map_maximalIdeal p]
  exact
    (standardLubinTatePrimitivePolynomial_isEisensteinAt
      (standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u)
      n).isWeaklyEisensteinAt.map
        (padicCompletedUnramifiedIntegerMap p)

/-- The integral changed primitive polynomial is genuinely Eisenstein over
the completed-unramified valuation ring. -/
theorem padicChangedCompletedPrimitivePolynomialInteger_isEisensteinAt
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicChangedCompletedPrimitivePolynomialInteger p u n).IsEisensteinAt
      (padicCompletedUnramifiedCompleteDVF p).maximalIdeal := by
  let target := padicCompletedUnramifiedCompleteDVF p
  let π := padicIntEquivValuationSubring p (p : ℤ_[p])
  let πu :=
    standardLubinTateChangedUniformizer
      (padicLocalField p) π u
  let πuE : target.valuationSubring :=
    padicCompletedUnramifiedIntegerMap p πu
  have hmonic :
      (padicChangedCompletedPrimitivePolynomialInteger p u n).Monic :=
    padicChangedCompletedPrimitivePolynomialInteger_monic p u n
  refine hmonic.isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal target.valuationSubring).ne_top
    ?_ ?_
  · intro i hi
    exact
      (padicChangedCompletedPrimitivePolynomialInteger_isWeaklyEisensteinAt
        p u n).mem hi
  · have hπu :
        target.valuation.IsUniformizer
          (πuE : padicCompletedUnramifiedField p) := by
      simpa only [target, π, πu, πuE] using
        padicChangedCompletedUniformizer_isUniformizer p u
    have hnotMem :
        πuE ∉ target.maximalIdeal ^ 2 :=
      target.uniformizer_not_mem_maximalIdeal_sq hπu
    simpa only [padicChangedCompletedPrimitivePolynomialInteger,
      Polynomial.coeff_map,
      standardLubinTatePrimitivePolynomial_coeff_zero,
      π, πu, πuE] using hnotMem

/-- The integral changed primitive polynomial is irreducible. -/
theorem padicChangedCompletedPrimitivePolynomialInteger_irreducible
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Irreducible
      (padicChangedCompletedPrimitivePolynomialInteger p u n) := by
  apply
    (padicChangedCompletedPrimitivePolynomialInteger_isEisensteinAt
      p u n).irreducible
      (IsLocalRing.maximalIdeal.isMaximal
        (padicCompletedUnramifiedCompleteDVF p).valuationSubring).isPrime
      (padicChangedCompletedPrimitivePolynomialInteger_monic
        p u n).isPrimitive
  rw [padicChangedCompletedPrimitivePolynomialInteger_natDegree]
  exact Nat.mul_pos
    (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
    (Nat.pow_pos (Fact.out : p.Prime).pos)

/-- The changed primitive polynomial remains irreducible over the completed
maximal-unramified fraction field. -/
theorem padicChangedCompletedPrimitivePolynomial_irreducible
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Irreducible (padicChangedCompletedPrimitivePolynomial p u n) := by
  have hmap :
      Irreducible
        ((padicChangedCompletedPrimitivePolynomialInteger p u n).map
          (algebraMap
            (padicCompletedUnramifiedCompleteDVF p).valuationSubring
            (padicCompletedUnramifiedField p))) := by
    have hmonic :=
      padicChangedCompletedPrimitivePolynomialInteger_monic p u n
    exact hmonic.irreducible_iff_irreducible_map_fraction_map.mp
        (padicChangedCompletedPrimitivePolynomialInteger_irreducible
          p u n)
  rwa [padicChangedCompletedPrimitivePolynomialInteger_map] at hmap

/-- The theta value is a root of the named changed primitive polynomial
over the completed-unramified field. -/
theorem padicChangedUniformizerThetaValue_isRoot_completedPrimitivePolynomial
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    ((padicChangedCompletedPrimitivePolynomial p u n).map
      (algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n))).IsRoot
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) := by
  simpa only [padicChangedCompletedPrimitivePolynomial,
    Polynomial.map_map,
    IsScalarTower.algebraMap_eq ℚ_[p]
      (padicCompletedUnramifiedField p) (padicCompletedLevelField p n)]
    using
    padicChangedUniformizerThetaValue_field_isRoot p u n

/-- The theta value is integral over the completed-unramified field. -/
theorem padicChangedUniformizerThetaValue_isIntegral_completedBase
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsIntegral (padicCompletedUnramifiedField p)
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) := by
  refine
    ⟨padicChangedCompletedPrimitivePolynomial p u n,
      padicChangedCompletedPrimitivePolynomial_monic p u n, ?_⟩
  rw [← Polynomial.eval_map]
  exact
    padicChangedUniformizerThetaValue_isRoot_completedPrimitivePolynomial
      p u n

/-- The minimal polynomial of the theta value over the completed-unramified
field is the genuine changed primitive polynomial. -/
theorem padicChangedUniformizerThetaValue_minpoly_completedBase
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    minpoly (padicCompletedUnramifiedField p)
        ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n) =
      padicChangedCompletedPrimitivePolynomial p u n := by
  have hroot :
      Polynomial.aeval
          ((padicChangedUniformizerThetaValue p u n :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
              padicCompletedLevelField p n)
          (padicChangedCompletedPrimitivePolynomial p u n) =
        0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact
      padicChangedUniformizerThetaValue_isRoot_completedPrimitivePolynomial
        p u n
  have hmin :=
    minpoly.eq_of_irreducible
      (padicChangedCompletedPrimitivePolynomial_irreducible p u n)
      hroot
  rw [(padicChangedCompletedPrimitivePolynomial_monic
    p u n).leadingCoeff, inv_one, Polynomial.C_1, mul_one] at hmin
  exact hmin.symm

/-- The fixed theta point generates the entire standard completed level
over the completed-unramified coefficient field. -/
theorem padicChangedUniformizerThetaValue_adjoin_completedBase_eq_top
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IntermediateField.adjoin
        (padicCompletedUnramifiedField p)
        ({((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n)} :
          Set (padicCompletedLevelField p n)) =
      ⊤ := by
  apply
    (Field.primitive_element_iff_minpoly_natDegree_eq
      (padicCompletedUnramifiedField p)
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n)).2
  rw [padicChangedUniformizerThetaValue_minpoly_completedBase,
    padicChangedCompletedPrimitivePolynomial_natDegree]
  let pb := padicCompletedPrimitivePowerBasis p n
  calc
    (p - 1) * p ^ n =
        (padicCompletedPrimitivePolynomial p n).natDegree :=
      (padicCompletedPrimitivePolynomial_natDegree p n).symm
    _ =
        (minpoly (padicCompletedUnramifiedField p) pb.gen).natDegree := by
      rw [show pb.gen = padicCompletedPrimitiveRoot p n by
        exact padicCompletedPrimitivePowerBasis_gen p n]
      rw [padicCompletedPrimitiveRoot_minpoly]
    _ = pb.dim := pb.natDegree_minpoly
    _ =
        Module.finrank (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) :=
      pb.finrank.symm

/-- The theta value supplies a power basis of the completed standard level
over the completed-unramified field. -/
noncomputable def padicChangedUniformizerThetaPowerBasis
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    PowerBasis (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) := by
  apply PowerBasis.ofAdjoinEqTop
    (padicChangedUniformizerThetaValue_isIntegral_completedBase p u n)
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (padicChangedUniformizerThetaValue_isIntegral_completedBase
        p u n).isAlgebraic,
    padicChangedUniformizerThetaValue_adjoin_completedBase_eq_top,
    IntermediateField.top_toSubalgebra]

/-- The generator of the theta power basis is the genuine evaluated theta
value. -/
@[simp]
theorem padicChangedUniformizerThetaPowerBasis_gen
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicChangedUniformizerThetaPowerBasis p u n).gen =
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) :=
  PowerBasis.ofAdjoinEqTop_gen _ _

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedFrobeniusLift
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.zHatUnitsDecomposition_freeCoordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.padicChangedUniformizerThetaPowerBasis_gen _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Frobenius lifts on completed p-adic Lubin--Tate levels

Arithmetic Frobenius on the completed maximal-unramified p-adic field fixes
the standard primitive Lubin--Tate polynomial, since that polynomial descends
to `ℚ_[p]`.  Using the completed primitive power basis, it therefore extends
to a semilinear automorphism of every completed level.  A finite unit
parameter prescribes the image of the primitive root.

The construction is an actual field automorphism.  Surjectivity follows from
the theorem that every completed unit-parameter root generates the completed
level.
-/

noncomputable section

open scoped Polynomial

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- The ordinary completed-base algebra structure on a completed level,
named so it can coexist with the Frobenius-twisted structure. -/
@[reducible]
noncomputable def padicCompletedLevelOriginalAlgebra
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Algebra (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) :=
  inferInstance

/-- The codomain algebra structure whose scalar map is arithmetic
Frobenius followed by the ordinary scalar inclusion. -/
@[reducible]
noncomputable def padicCompletedLevelFrobeniusAlgebra
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Algebra (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) :=
  RingHom.toAlgebra
    ((algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)).comp
      (padicCompletedUnramifiedFrobenius p).toAlgHom.toRingHom)

/-- Arithmetic Frobenius fixes the completed primitive polynomial because
its coefficients descend to `ℚ_[p]`. -/
theorem padicCompletedPrimitivePolynomial_frobenius
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePolynomial p n).map
        (padicCompletedUnramifiedFrobenius p).toAlgHom.toRingHom =
      padicCompletedPrimitivePolynomial p n := by
  unfold padicCompletedPrimitivePolynomial
  have hcomp :
      ((padicCompletedUnramifiedFrobenius p).toAlgHom.toRingHom).comp
          (algebraMap ℚ_[p] (padicCompletedUnramifiedField p)) =
        algebraMap ℚ_[p] (padicCompletedUnramifiedField p) := by
    apply RingHom.ext
    intro a
    exact (padicCompletedUnramifiedFrobenius p).commutes a
  rw [Polynomial.map_map, hcomp]

/-- The direct completed standard unit action annihilates the primitive
minimal polynomial for the Frobenius-twisted codomain structure. -/
theorem
    padicCompletedStandardPrimitivePointUnitAction_aeval_minpoly_frobenius
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    @Polynomial.aeval
        (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        _ _ (padicCompletedLevelFrobeniusAlgebra p n)
        (((padicCompletedStandardPrimitivePointUnitAction p n u :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n))
        (minpoly (padicCompletedUnramifiedField p)
          (padicCompletedPrimitiveRoot p n)) =
      0 := by
  rw [padicCompletedPrimitiveRoot_minpoly]
  change Polynomial.eval₂
      ((algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)).comp
        (padicCompletedUnramifiedFrobenius p).toAlgHom.toRingHom)
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n))
      (padicCompletedPrimitivePolynomial p n) = 0
  rw [← Polynomial.eval₂_map,
    padicCompletedPrimitivePolynomial_frobenius]
  rw [← Polynomial.eval_map]
  exact
    padicCompletedStandardPrimitivePointUnitAction_isRoot p n u

/-- The semilinear algebra homomorphism extending arithmetic Frobenius and
sending the primitive root to its actual completed standard unit action. -/
noncomputable def padicCompletedUnitFrobeniusLiftAlgHom
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    @AlgHom
      (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n)
      (padicCompletedLevelField p n)
      _ _ _
      (padicCompletedLevelOriginalAlgebra p n)
      (padicCompletedLevelFrobeniusAlgebra p n) :=
  @PowerBasis.lift
    (padicCompletedLevelField p n) _
    (padicCompletedUnramifiedField p) _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelField p n) _
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedPrimitivePowerBasis p n)
    (((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n)) (by
      rw [padicCompletedPrimitivePowerBasis_gen]
      exact
        padicCompletedStandardPrimitivePointUnitAction_aeval_minpoly_frobenius
          p n u)

/-- The direct unit-indexed semilinear homomorphism sends the primitive
root to the actual completed standard unit action. -/
@[simp]
theorem padicCompletedUnitFrobeniusLiftAlgHom_primitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedUnitFrobeniusLiftAlgHom p n u
        (padicCompletedPrimitiveRoot p n) =
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)) := by
  change padicCompletedUnitFrobeniusLiftAlgHom p n u
      (padicCompletedPrimitivePowerBasis p n).gen = _
  exact @PowerBasis.lift_gen
    (padicCompletedLevelField p n) _
    (padicCompletedUnramifiedField p) _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelField p n) _
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedPrimitivePowerBasis p n)
    (((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n))
    (padicCompletedStandardPrimitivePointUnitAction_aeval_minpoly_frobenius
      p n u)

/-- The underlying field homomorphism of the unit-indexed completed
Frobenius lift. -/
noncomputable def padicCompletedUnitFrobeniusLift
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedLevelField p n →+*
      padicCompletedLevelField p n :=
  @AlgHom.toRingHom
    (padicCompletedUnramifiedField p)
    (padicCompletedLevelField p n)
    (padicCompletedLevelField p n)
    _ _ _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedUnitFrobeniusLiftAlgHom p n u)

/-- The direct unit-indexed completed Frobenius lift acts on base scalars
by arithmetic Frobenius. -/
@[simp]
theorem padicCompletedUnitFrobeniusLift_algebraMap
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (b : padicCompletedUnramifiedField p) :
    padicCompletedUnitFrobeniusLift p n u
        (algebraMap (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) b) =
      algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        (padicCompletedUnramifiedFrobenius p b) := by
  change padicCompletedUnitFrobeniusLiftAlgHom p n u
      (@algebraMap
        (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        _ _ (padicCompletedLevelOriginalAlgebra p n) b) =
    @algebraMap
      (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n)
      _ _ (padicCompletedLevelFrobeniusAlgebra p n) b
  exact @AlgHom.commutes
    (padicCompletedUnramifiedField p)
    (padicCompletedLevelField p n)
    (padicCompletedLevelField p n)
    _ _ _
    (padicCompletedLevelOriginalAlgebra p n)
    (padicCompletedLevelFrobeniusAlgebra p n)
    (padicCompletedUnitFrobeniusLiftAlgHom p n u) b

/-- The direct unit-indexed completed Frobenius lift has its prescribed
action on the primitive root. -/
@[simp]
theorem padicCompletedUnitFrobeniusLift_primitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedUnitFrobeniusLift p n u
        (padicCompletedPrimitiveRoot p n) =
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)) :=
  padicCompletedUnitFrobeniusLiftAlgHom_primitiveRoot p n u

/-- The direct unit-indexed completed Frobenius lift is surjective. -/
theorem padicCompletedUnitFrobeniusLift_surjective
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    Function.Surjective (padicCompletedUnitFrobeniusLift p n u) := by
  let E := padicCompletedUnramifiedField p
  let L := padicCompletedLevelField p n
  let y : L :=
    ((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) : L)
  let σ : L →+* L := padicCompletedUnitFrobeniusLift p n u
  let R : Subring L := σ.range
  have hbase (b : E) : algebraMap E L b ∈ R := by
    refine
      ⟨algebraMap E L
        ((padicCompletedUnramifiedFrobenius p).symm b), ?_⟩
    change σ
        (algebraMap E L
          ((padicCompletedUnramifiedFrobenius p).symm b)) =
      algebraMap E L b
    rw [show σ = padicCompletedUnitFrobeniusLift p n u by rfl,
      padicCompletedUnitFrobeniusLift_algebraMap,
      (padicCompletedUnramifiedFrobenius p).apply_symm_apply]
  let S : Subalgebra E L :=
    { R with
      algebraMap_mem' := hbase }
  have hy : y ∈ S := by
    refine ⟨padicCompletedPrimitiveRoot p n, ?_⟩
    exact padicCompletedUnitFrobeniusLift_primitiveRoot p n u
  have hle : Algebra.adjoin E ({y} : Set L) ≤ S := by
    apply Algebra.adjoin_le
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact hy
  rw [show Algebra.adjoin E ({y} : Set L) = ⊤ by
        simpa only [E, L, y] using
          padicCompletedStandardPrimitivePointUnitAction_adjoin_eq_top
            p n u] at hle
  have hS : S = ⊤ := top_unique hle
  intro z
  have hz : z ∈ S := by rw [hS]; trivial
  exact hz

/-- The actual field automorphism extending arithmetic Frobenius and acting
on the primitive root by the direct completed standard unit action. -/
noncomputable def padicCompletedUnitFrobeniusLiftEquiv
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedLevelField p n ≃+*
      padicCompletedLevelField p n :=
  RingEquiv.ofBijective (padicCompletedUnitFrobeniusLift p n u)
    ⟨(padicCompletedUnitFrobeniusLift p n u).injective,
      padicCompletedUnitFrobeniusLift_surjective p n u⟩

/-- The unit-indexed Frobenius-lift equivalence acts on completed base
scalars by arithmetic Frobenius. -/
@[simp]
theorem padicCompletedUnitFrobeniusLiftEquiv_algebraMap
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (b : padicCompletedUnramifiedField p) :
    padicCompletedUnitFrobeniusLiftEquiv p n u
        (algebraMap (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) b) =
      algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        (padicCompletedUnramifiedFrobenius p b) :=
  padicCompletedUnitFrobeniusLift_algebraMap p n u b

/-- The unit-indexed Frobenius-lift equivalence acts on the primitive root
by the direct completed standard unit action. -/
@[simp]
theorem padicCompletedUnitFrobeniusLiftEquiv_primitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedUnitFrobeniusLiftEquiv p n u
        (padicCompletedPrimitiveRoot p n) =
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)) :=
  padicCompletedUnitFrobeniusLift_primitiveRoot p n u

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedFrobeniusEvaluation
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.zHatUnitsDecomposition_freeCoordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.padicChangedUniformizerThetaPowerBasis_gen _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Semilinear evaluation for completed p-adic Frobenius lifts

The completed unit-indexed Frobenius lift preserves the actual integral
closure valuation ring.  Its restriction is continuous for the maximal-
ideal adic topology and transports convergent Witt-coefficient power-series
evaluation by Witt Frobenius on coefficients.

Applying this to the standard-to-multiplicative comparison identifies the
image of the genuine completed multiplicative primitive point with its
actual multiplicative unit translate.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField

noncomputable local instance (priority := 50)
    padicCompletedFrobeniusEvaluationWittUniformSpace
    (p : ℕ) [Fact p.Prime] :
    UniformSpace (padicCompletedUnramifiedWittRing p) :=
  ⊥

noncomputable local instance
    padicCompletedFrobeniusEvaluationTargetWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (padicCompletedLevelCompleteDVF p n).valuationSubring where
  i := (padicCompletedLevelCompleteDVF p n).maximalIdeal

noncomputable local instance
    padicCompletedFrobeniusEvaluationTargetCompleteSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

noncomputable local instance
    padicCompletedFrobeniusEvaluationTargetT2Space
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

/-- Arithmetic Frobenius restricted to the valuation ring of the completed
maximal-unramified p-adic field. -/
noncomputable def padicCompletedUnramifiedFrobeniusIntegerEquiv
    (p : ℕ) [Fact p.Prime] :
    (padicCompletedUnramifiedCompleteDVF p).valuationSubring ≃+*
      (padicCompletedUnramifiedCompleteDVF p).valuationSubring where
  toFun x :=
    ⟨padicCompletedUnramifiedFrobenius p
        (x : padicCompletedUnramifiedField p), by
      change
        padicCompletedUnramifiedValuation p
            (padicCompletedUnramifiedFrobenius p
              (x : padicCompletedUnramifiedField p)) ≤ 1
      rw [padicCompletedUnramifiedFrobenius_valuation]
      exact x.property⟩
  invFun x :=
    ⟨(padicCompletedUnramifiedFrobenius p).symm
        (x : padicCompletedUnramifiedField p), by
      change
        padicCompletedUnramifiedValuation p
            ((padicCompletedUnramifiedFrobenius p).symm
              (x : padicCompletedUnramifiedField p)) ≤ 1
      rw [← padicCompletedUnramifiedFrobenius_valuation p
          ((padicCompletedUnramifiedFrobenius p).symm
            (x : padicCompletedUnramifiedField p)),
        (padicCompletedUnramifiedFrobenius p).apply_symm_apply]
      exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (padicCompletedUnramifiedFrobenius p).symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    exact (padicCompletedUnramifiedFrobenius p).apply_symm_apply x
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (padicCompletedUnramifiedFrobenius p)
      (x : padicCompletedUnramifiedField p)
      (y : padicCompletedUnramifiedField p)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (padicCompletedUnramifiedFrobenius p)
      (x : padicCompletedUnramifiedField p)
      (y : padicCompletedUnramifiedField p)

/-- Coercion of the integral Frobenius restriction agrees with arithmetic
Frobenius on the completed-unramified fraction field. -/
@[simp]
theorem padicCompletedUnramifiedFrobeniusIntegerEquiv_coe
    (p : ℕ) [Fact p.Prime]
    (x : (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
    ((padicCompletedUnramifiedFrobeniusIntegerEquiv p x :
        (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
      padicCompletedUnramifiedField p) =
      padicCompletedUnramifiedFrobenius p
        (x : padicCompletedUnramifiedField p) :=
  rfl

/-- Coercion of the inverse integral Frobenius restriction agrees with
inverse arithmetic Frobenius on the fraction field. -/
@[simp]
theorem padicCompletedUnramifiedFrobeniusIntegerEquiv_symm_coe
    (p : ℕ) [Fact p.Prime]
    (x : (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
    (((padicCompletedUnramifiedFrobeniusIntegerEquiv p).symm x :
        (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
      padicCompletedUnramifiedField p) =
      (padicCompletedUnramifiedFrobenius p).symm
        (x : padicCompletedUnramifiedField p) :=
  rfl

/-- The inverse of a unit-indexed completed Frobenius lift acts on base
scalars through inverse arithmetic Frobenius. -/
@[simp]
theorem padicCompletedUnitFrobeniusLiftEquiv_symm_algebraMap
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (b : padicCompletedUnramifiedField p) :
    (padicCompletedUnitFrobeniusLiftEquiv p n u).symm
        (algebraMap (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) b) =
      algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n)
        ((padicCompletedUnramifiedFrobenius p).symm b) := by
  apply (padicCompletedUnitFrobeniusLiftEquiv p n u).injective
  rw [(padicCompletedUnitFrobeniusLiftEquiv p n u).apply_symm_apply,
    padicCompletedUnitFrobeniusLiftEquiv_algebraMap,
    (padicCompletedUnramifiedFrobenius p).apply_symm_apply]

/-- A unit-indexed completed Frobenius lift carries every element of the
selected completed-level valuation ring back into that valuation ring. -/
theorem padicCompletedUnitFrobeniusLiftEquiv_mem_valuationSubring
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : padicCompletedLevelField p n)
    (hx :
      x ∈ (padicCompletedLevelCompleteDVF p n).valuation.valuationSubring) :
    padicCompletedUnitFrobeniusLiftEquiv p n u x ∈
      (padicCompletedLevelCompleteDVF p n).valuation.valuationSubring := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let E := padicCompletedUnramifiedField p
  let L := padicCompletedLevelField p n
  let φ :
      base.valuationSubring ≃+* base.valuationSubring :=
    padicCompletedUnramifiedFrobeniusIntegerEquiv p
  let σ : L ≃+* L :=
    padicCompletedUnitFrobeniusLiftEquiv p n u
  let : IsIntegralClosure target.valuationSubring
      base.valuationSubring L :=
    padicCompletedLevelCompleteDVF_isIntegralClosure p n
  have hxIntegral : IsIntegral base.valuationSubring x :=
    (IsIntegralClosure.isIntegral_iff
      (A := target.valuationSubring)
      (R := base.valuationSubring)
      (B := L)).2 ⟨⟨x, hx⟩, rfl⟩
  have hcomp :
      (algebraMap base.valuationSubring L).comp φ.toRingHom =
        σ.toRingHom.comp (algebraMap base.valuationSubring L) := by
    apply RingHom.ext
    intro b
    change
      algebraMap E L ((φ b : base.valuationSubring) : E) =
        σ (algebraMap E L (b : E))
    rw [show φ = padicCompletedUnramifiedFrobeniusIntegerEquiv p by rfl,
      padicCompletedUnramifiedFrobeniusIntegerEquiv_coe,
      show σ = padicCompletedUnitFrobeniusLiftEquiv p n u by rfl,
      padicCompletedUnitFrobeniusLiftEquiv_algebraMap]
  have hσIntegral : IsIntegral base.valuationSubring (σ x) :=
    IsIntegral.map_of_comp_eq φ.toRingHom σ.toRingHom hcomp hxIntegral
  rcases
      (IsIntegralClosure.isIntegral_iff
        (A := target.valuationSubring)
        (R := base.valuationSubring)
        (B := L)).1 hσIntegral with
    ⟨z, hz⟩
  change target.valuation (σ x) ≤ 1
  rw [← hz]
  exact z.property

/-- The inverse of a unit-indexed completed Frobenius lift also preserves
the selected completed-level valuation ring. -/
theorem padicCompletedUnitFrobeniusLiftEquiv_symm_mem_valuationSubring
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : padicCompletedLevelField p n)
    (hx :
      x ∈ (padicCompletedLevelCompleteDVF p n).valuation.valuationSubring) :
    (padicCompletedUnitFrobeniusLiftEquiv p n u).symm x ∈
      (padicCompletedLevelCompleteDVF p n).valuation.valuationSubring := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let E := padicCompletedUnramifiedField p
  let L := padicCompletedLevelField p n
  let φ :
      base.valuationSubring ≃+* base.valuationSubring :=
    (padicCompletedUnramifiedFrobeniusIntegerEquiv p).symm
  let σ : L ≃+* L :=
    (padicCompletedUnitFrobeniusLiftEquiv p n u).symm
  let : IsIntegralClosure target.valuationSubring
      base.valuationSubring L :=
    padicCompletedLevelCompleteDVF_isIntegralClosure p n
  have hxIntegral : IsIntegral base.valuationSubring x :=
    (IsIntegralClosure.isIntegral_iff
      (A := target.valuationSubring)
      (R := base.valuationSubring)
      (B := L)).2 ⟨⟨x, hx⟩, rfl⟩
  have hcomp :
      (algebraMap base.valuationSubring L).comp φ.toRingHom =
        σ.toRingHom.comp (algebraMap base.valuationSubring L) := by
    apply RingHom.ext
    intro b
    change
      algebraMap E L ((φ b : base.valuationSubring) : E) =
        σ (algebraMap E L (b : E))
    rw [show φ =
        (padicCompletedUnramifiedFrobeniusIntegerEquiv p).symm by rfl,
      padicCompletedUnramifiedFrobeniusIntegerEquiv_symm_coe,
      show σ =
        (padicCompletedUnitFrobeniusLiftEquiv p n u).symm by rfl,
      padicCompletedUnitFrobeniusLiftEquiv_symm_algebraMap]
  have hσIntegral : IsIntegral base.valuationSubring (σ x) :=
    IsIntegral.map_of_comp_eq φ.toRingHom σ.toRingHom hcomp hxIntegral
  rcases
      (IsIntegralClosure.isIntegral_iff
        (A := target.valuationSubring)
        (R := base.valuationSubring)
        (B := L)).1 hσIntegral with
    ⟨z, hz⟩
  change target.valuation (σ x) ≤ 1
  rw [← hz]
  exact z.property

/-- Membership in the selected completed-level valuation ring is invariant
under every unit-indexed completed Frobenius lift. -/
theorem padicCompletedUnitFrobeniusLiftEquiv_mem_valuationSubring_iff
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : padicCompletedLevelField p n) :
    x ∈ (padicCompletedLevelCompleteDVF p n).valuation.valuationSubring ↔
      padicCompletedUnitFrobeniusLiftEquiv p n u x ∈
        (padicCompletedLevelCompleteDVF p n).valuation.valuationSubring := by
  constructor
  · exact padicCompletedUnitFrobeniusLiftEquiv_mem_valuationSubring p n u x
  · intro hx
    have hback :=
      padicCompletedUnitFrobeniusLiftEquiv_symm_mem_valuationSubring
        p n u
        (padicCompletedUnitFrobeniusLiftEquiv p n u x) hx
    simpa using hback

/-- The actual valuation-ring automorphism induced by a unit-indexed
completed Frobenius lift. -/
noncomputable def padicCompletedUnitFrobeniusIntegerEquiv
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    (padicCompletedLevelCompleteDVF p n).valuationSubring ≃+*
      (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  higherPrincipalUnitGroup.valuationSubringRingEquivOfPreserves
    (padicCompletedLevelCompleteDVF p n)
    (padicCompletedUnitFrobeniusLiftEquiv p n u)
    (padicCompletedUnitFrobeniusLiftEquiv_mem_valuationSubring_iff
      p n u)

/-- Coercion of the integral completed Frobenius restriction agrees with
the ambient field automorphism. -/
@[simp]
theorem padicCompletedUnitFrobeniusIntegerEquiv_coe
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring) :
    ((padicCompletedUnitFrobeniusIntegerEquiv p n u x :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
      padicCompletedUnitFrobeniusLiftEquiv p n u
        (x : padicCompletedLevelField p n) :=
  rfl

/-- Coercion of the inverse integral completed Frobenius restriction agrees
with the inverse ambient field automorphism. -/
@[simp]
theorem padicCompletedUnitFrobeniusIntegerEquiv_symm_coe
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring) :
    (((padicCompletedUnitFrobeniusIntegerEquiv p n u).symm x :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
      (padicCompletedUnitFrobeniusLiftEquiv p n u).symm
        (x : padicCompletedLevelField p n) := by
  apply (padicCompletedUnitFrobeniusLiftEquiv p n u).injective
  rw [(padicCompletedUnitFrobeniusLiftEquiv p n u).apply_symm_apply]
  simpa using
    (padicCompletedUnitFrobeniusIntegerEquiv_coe
      p n u
      ((padicCompletedUnitFrobeniusIntegerEquiv p n u).symm x)).symm

/-- The integral completed Frobenius restriction is continuous for the
maximal-ideal adic topology. -/
theorem padicCompletedUnitFrobeniusIntegerEquiv_continuous
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    Continuous (padicCompletedUnitFrobeniusIntegerEquiv p n u) := by
  let target := padicCompletedLevelCompleteDVF p n
  let σ : padicCompletedLevelField p n ≃+*
      padicCompletedLevelField p n :=
    padicCompletedUnitFrobeniusLiftEquiv p n u
  let hpreserve :
      ∀ x : padicCompletedLevelField p n,
        x ∈ target.valuation.valuationSubring ↔
          σ x ∈ target.valuation.valuationSubring :=
    padicCompletedUnitFrobeniusLiftEquiv_mem_valuationSubring_iff p n u
  let r : target.valuationSubring ≃+* target.valuationSubring :=
    padicCompletedUnitFrobeniusIntegerEquiv p n u
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
        target σ hpreserve m x).2 hx

/-- The integral completed Frobenius restriction transports the canonical
Witt coefficient map by Witt-vector Frobenius. -/
theorem padicCompletedUnitFrobeniusIntegerEquiv_wittCoefficientHom
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (a : padicCompletedUnramifiedWittRing p) :
    padicCompletedUnitFrobeniusIntegerEquiv p n u
        (padicCompletedLevelWittCoefficientHom p n a) =
      padicCompletedLevelWittCoefficientHom p n
        (WittVector.frobenius a) := by
  apply Subtype.ext
  change
    padicCompletedUnitFrobeniusLiftEquiv p n u
        (((padicCompletedLevelWittCoefficientHom p n a :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n)) =
      (((padicCompletedLevelWittCoefficientHom p n
            (WittVector.frobenius a) :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n))
  rw [padicCompletedLevelWittCoefficientHom_apply,
    padicCompletedUnitFrobeniusLiftEquiv_algebraMap,
    padicCompletedUnramifiedFrobenius_algebraMap_witt,
    padicCompletedLevelWittCoefficientHom_apply]

theorem padicCompletedHasEval_map_continuous
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (r :
      (padicCompletedLevelCompleteDVF p n).valuationSubring →+*
        (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hr : Continuous r)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    PowerSeries.HasEval (r x) :=
  hx.map hr

/-- A convergent completed-level evaluation point remains convergent after
applying the integral completed Frobenius restriction. -/
theorem padicCompletedUnitFrobeniusIntegerEquiv_hasEval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    PowerSeries.HasEval
      (padicCompletedUnitFrobeniusIntegerEquiv p n u x) := by
  exact
    padicCompletedHasEval_map_continuous p n
      (padicCompletedUnitFrobeniusIntegerEquiv p n u).toRingHom
      (padicCompletedUnitFrobeniusIntegerEquiv_continuous p n u) x hx

/-- Convergent completed-level evaluation is semilinear for every
unit-indexed completed Frobenius lift: the point is acted on by the
integral lift and coefficients by Witt Frobenius. -/
theorem padicCompletedUnitFrobeniusIntegerEquiv_evaluation
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (f : PowerSeries (padicCompletedUnramifiedWittRing p)) :
    padicCompletedUnitFrobeniusIntegerEquiv p n u
        (padicCompletedLevelPowerSeriesEval p n x hx f) =
      padicCompletedLevelPowerSeriesEval p n
        (padicCompletedUnitFrobeniusIntegerEquiv p n u x)
        (padicCompletedUnitFrobeniusIntegerEquiv_hasEval p n u x hx)
        (PowerSeries.map WittVector.frobenius f) := by
  have hsource : HasSum
      (fun m : ℕ =>
        padicCompletedLevelWittCoefficientHom p n
            (PowerSeries.coeff m f) * x ^ m)
      (padicCompletedLevelPowerSeriesEval p n x hx f) := by
    rw [padicCompletedLevelPowerSeriesEval,
      PowerSeries.coe_eval₂Hom]
    exact PowerSeries.hasSum_eval₂
      (padicCompletedLevelWittCoefficientHom_continuous p n)
      hx f
  have hmapped := hsource.map
    (padicCompletedUnitFrobeniusIntegerEquiv p n u)
    (padicCompletedUnitFrobeniusIntegerEquiv_continuous p n u)
  have hmapped' : HasSum
      (fun m : ℕ =>
        padicCompletedLevelWittCoefficientHom p n
            (PowerSeries.coeff m
              (PowerSeries.map WittVector.frobenius f)) *
          (padicCompletedUnitFrobeniusIntegerEquiv p n u x) ^ m)
      (padicCompletedUnitFrobeniusIntegerEquiv p n u
        (padicCompletedLevelPowerSeriesEval p n x hx f)) := by
    convert hmapped using 1
    all_goals try with_reducible_and_instances rfl
    funext m
    simp only [Function.comp_apply, map_mul, map_pow,
      PowerSeries.coeff_map,
      padicCompletedUnitFrobeniusIntegerEquiv_wittCoefficientHom]
  apply HasSum.unique hmapped'
  rw [padicCompletedLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom]
  exact PowerSeries.hasSum_eval₂
    (padicCompletedLevelWittCoefficientHom_continuous p n)
    (padicCompletedUnitFrobeniusIntegerEquiv_hasEval p n u x hx)
    (PowerSeries.map WittVector.frobenius f)

/-- The integral completed Frobenius restriction sends the chosen
primitive point to its actual completed standard unit translate. -/
@[simp]
theorem padicCompletedUnitFrobeniusIntegerEquiv_primitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedUnitFrobeniusIntegerEquiv p n u
        (padicCompletedPrimitiveRootInteger p n) =
      padicCompletedStandardPrimitivePointUnitAction p n u := by
  apply Subtype.ext
  change
    padicCompletedUnitFrobeniusLiftEquiv p n u
        (padicCompletedPrimitiveRoot p n) =
      (((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n))
  exact padicCompletedUnitFrobeniusLiftEquiv_primitiveRoot p n u

/-- The integral completed Frobenius restriction sends the genuine
multiplicative primitive point to its actual multiplicative unit
translate. -/
theorem
    padicCompletedUnitFrobeniusIntegerEquiv_multiplicativePrimitivePoint
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicCompletedUnitFrobeniusIntegerEquiv p n u
        (padicCompletedMultiplicativePrimitivePoint p n) =
      padicCompletedMultiplicativePrimitivePointUnitAction p u n := by
  let lambda := padicCompletedPrimitiveRootInteger p n
  let hlambda := padicCompletedPrimitiveRootInteger_hasEval p n
  let H := padicCompletedStandardToMultiplicativeIntertwiner p
  let r :=
    padicCompletedUnitFrobeniusIntegerEquiv p n u
  have hpoint :
      r lambda =
        padicCompletedStandardPrimitivePointUnitAction p n u := by
    simpa only [r, lambda] using
      padicCompletedUnitFrobeniusIntegerEquiv_primitiveRoot p n u
  calc
    r (padicCompletedMultiplicativePrimitivePoint p n) =
        padicCompletedLevelPowerSeriesEval p n
          (r lambda)
          (padicCompletedUnitFrobeniusIntegerEquiv_hasEval
            p n u lambda hlambda)
          (PowerSeries.map WittVector.frobenius H) := by
      simpa only [r, lambda, hlambda, H,
        padicCompletedMultiplicativePrimitivePoint] using
        (padicCompletedUnitFrobeniusIntegerEquiv_evaluation
          p n u lambda hlambda H)
    _ =
        padicCompletedLevelPowerSeriesEval p n
          (padicCompletedStandardPrimitivePointUnitAction p n u)
          (padicCompletedStandardPrimitivePointUnitAction_hasEval p n u)
          H := by
      rw [padicCompletedStandardToMultiplicativeIntertwiner_frobenius]
      exact
        padicCompletedLevelPowerSeriesEval_congr_point p n
          (padicCompletedUnitFrobeniusIntegerEquiv_hasEval
            p n u lambda hlambda)
          (padicCompletedStandardPrimitivePointUnitAction_hasEval p n u)
          hpoint H
    _ = padicCompletedMultiplicativePrimitivePointUnitAction p u n := by
      simpa only [lambda, hlambda, H,
        padicCompletedStandardPrimitivePointUnitAction,
        padicCompletedMultiplicativePrimitivePointUnitAction,
        padicCompletedMultiplicativeUnitEndomorphism,
        padicCompletedMultiplicativeScalarEndomorphismValue,
        padicCompletedMultiplicativePrimitivePoint] using
        (padicCompletedStandardToMultiplicativeIntertwiner_eval_endomorphism
          p n lambda hlambda
            (u : (padicLocalField p).valuationSubring))

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedChangedUniformizerThetaFixed
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Fixedness of completed p-adic changed-uniformizer theta values

The Frobenius lift whose primitive-point action is indexed by the inverse
unit is the genuine diagonal action relevant to change of uniformizer.
Semilinear evaluation changes theta coefficients by Witt Frobenius, while
the first changed-uniformizer identity changes the evaluation point by the
unit itself.  The unit and inverse-unit actions cancel, so the actual
convergent theta value is fixed.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

noncomputable local instance
    padicCompletedThetaFixedTargetWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (padicCompletedLevelCompleteDVF p n).valuationSubring where
  i := (padicCompletedLevelCompleteDVF p n).maximalIdeal

theorem padicCompletedThetaFixedEvaluation_eq_of_point_eq
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x y : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy : x = y) :
    padicCompletedLevelPowerSeriesEval p n x hx =
      padicCompletedLevelPowerSeriesEval p n y hy := by
  subst y
  rfl

/-- On the genuine multiplicative primitive point, the multiplicative
unit action cancels the inverse-unit action prescribed by the diagonal
completed Frobenius lift. -/
theorem padicCompletedDiagonalFrobenius_multiplicativeUnitAction
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let r :=
      padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹
    let x := padicCompletedMultiplicativePrimitivePoint p n
    let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (r x)
        (padicCompletedUnitFrobeniusIntegerEquiv_hasEval
          p n u⁻¹ x hx)
        (u : (padicLocalField p).valuationSubring) =
      x := by
  let r :=
    padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  have hpoint :
      r x =
        padicCompletedMultiplicativePrimitivePointUnitAction p u⁻¹ n := by
    simpa only [r, x] using
      padicCompletedUnitFrobeniusIntegerEquiv_multiplicativePrimitivePoint
        p n u⁻¹
  have htransport :=
    DFunLike.congr_fun
      (padicCompletedThetaFixedEvaluation_eq_of_point_eq p n
        (r x)
        (padicCompletedMultiplicativePrimitivePointUnitAction p u⁻¹ n)
        (padicCompletedUnitFrobeniusIntegerEquiv_hasEval
          p n u⁻¹ x hx)
        (padicCompletedMultiplicativePrimitivePointUnitAction_hasEval
          p u⁻¹ n)
        hpoint)
      (padicCompletedMultiplicativeUnitEndomorphism p u)
  calc
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (r x)
        (padicCompletedUnitFrobeniusIntegerEquiv_hasEval
          p n u⁻¹ x hx)
        (u : (padicLocalField p).valuationSubring) =
      padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePointUnitAction p u⁻¹ n)
        (padicCompletedMultiplicativePrimitivePointUnitAction_hasEval
          p u⁻¹ n)
        (u : (padicLocalField p).valuationSubring) := by
      simpa only [padicCompletedMultiplicativeUnitEndomorphism,
        padicCompletedMultiplicativeScalarEndomorphismValue] using
        htransport
    _ = x := by
      simpa only [x, hx,
        padicCompletedMultiplicativePrimitivePointUnitAction,
        padicCompletedMultiplicativeUnitEndomorphism,
        padicCompletedMultiplicativeScalarEndomorphismValue] using
        (padicCompletedMultiplicativeScalarEndomorphismValue_unit_after_inverse
          p n
          (padicCompletedMultiplicativePrimitivePoint p n)
          (padicCompletedMultiplicativePrimitivePoint_hasEval p n) u)

/-- The inverse-unit diagonal completed Frobenius fixes the genuine
changed-uniformizer theta value in the completed-level valuation ring. -/
theorem
    padicCompletedChangedUniformizerThetaValue_fixed_by_diagonalFrobeniusInteger
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹
        (padicChangedUniformizerThetaValue p u n) =
      padicChangedUniformizerThetaValue p u n := by
  let r :=
    padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  let rx := r x
  let hrx :=
    padicCompletedUnitFrobeniusIntegerEquiv_hasEval
      p n u⁻¹ x hx
  let U := padicCompletedMultiplicativeUnitEndomorphism p u
  let xBack :=
    padicCompletedLevelPowerSeriesEval p n rx hrx U
  let hxBack :=
    padicCompletedLevelPowerSeriesEval_hasEval p n rx hrx U
      (padicCompletedMultiplicativeUnitEndomorphism_hasSubst p u)
  let Θ := padicChangedUniformizerIntertwiner p u
  have hsemi :=
    padicCompletedUnitFrobeniusIntegerEquiv_evaluation
      p n u⁻¹ x hx Θ
  have hfrobenius :=
    padicChangedUniformizerIntertwiner_frobenius_evaluation
      p u n rx hrx
  have hpoint : xBack = x := by
    change
      padicCompletedMultiplicativeScalarEndomorphismValue p n rx hrx
          (u : (padicLocalField p).valuationSubring) =
        x
    simpa only [r, x, hx, rx, hrx] using
      (padicCompletedDiagonalFrobenius_multiplicativeUnitAction p u n)
  have hevaluation :
      padicCompletedLevelPowerSeriesEval p n xBack hxBack Θ =
        padicCompletedLevelPowerSeriesEval p n x hx Θ :=
    DFunLike.congr_fun
      (padicCompletedThetaFixedEvaluation_eq_of_point_eq
        p n xBack x hxBack hx hpoint) Θ
  change
    r (padicCompletedLevelPowerSeriesEval p n x hx Θ) =
      padicCompletedLevelPowerSeriesEval p n x hx Θ
  calc
    _ =
        padicCompletedLevelPowerSeriesEval p n rx hrx
          (PowerSeries.map WittVector.frobenius Θ) := by
      simpa only [r, x, hx, rx, hrx, Θ] using hsemi
    _ = padicCompletedLevelPowerSeriesEval p n xBack hxBack Θ := by
      simpa only [xBack, hxBack, U, Θ] using hfrobenius
    _ = padicCompletedLevelPowerSeriesEval p n x hx Θ :=
      hevaluation

/-- The inverse-unit diagonal completed Frobenius field automorphism fixes
the genuine changed-uniformizer theta value. -/
theorem
    padicCompletedChangedUniformizerThetaValue_fixed_by_diagonalFrobenius
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedUnitFrobeniusLiftEquiv p n u⁻¹
        ((padicChangedUniformizerThetaValue p u n :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) =
      ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n) := by
  simpa only [padicCompletedUnitFrobeniusIntegerEquiv_coe] using
    congrArg
      (fun z : (padicCompletedLevelCompleteDVF p n).valuationSubring =>
        (z : padicCompletedLevelField p n))
      (padicCompletedChangedUniformizerThetaValue_fixed_by_diagonalFrobeniusInteger
        p u n)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedChangedUniformizerFixedField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseNontriviallyNormedField _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.zHatUnitsDecomposition_freeCoordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The changed p-adic Lubin--Tate level as a completed Frobenius fixed field

The completed Frobenius lift whose action on the standard primitive point is
indexed by `u⁻¹` is an actual `ℚ_[p]`-automorphism.  Its fixed field is
exactly the finite changed-uniformizer Lubin--Tate level generated by the
genuine theta value.

The key reverse inclusion is coefficient descent in the theta power basis:
fixedness makes every completed-unramified coefficient Frobenius-fixed, and
the fixed-field theorem for Witt Frobenius puts that coefficient in
`ℚ_[p]`.  The final norm formula is therefore transported from the actual
finite changed level, with no comparison hypothesis.
-/

noncomputable section

open scoped Polynomial

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- The inverse-unit completed Frobenius lift, regarded as an actual
automorphism over `ℚ_[p]`. -/
noncomputable def padicCompletedChangedUniformizerFrobeniusAlgEquiv
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedLevelField p n ≃ₐ[ℚ_[p]]
      padicCompletedLevelField p n :=
  AlgEquiv.ofRingEquiv (by
    intro b
    change
      padicCompletedUnitFrobeniusLiftEquiv p n u⁻¹
          (algebraMap (padicCompletedUnramifiedField p)
            (padicCompletedLevelField p n)
            (algebraMap ℚ_[p]
              (padicCompletedUnramifiedField p) b)) =
        algebraMap (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n)
          (algebraMap ℚ_[p]
            (padicCompletedUnramifiedField p) b)
    rw [padicCompletedUnitFrobeniusLiftEquiv_algebraMap,
      (padicCompletedUnramifiedFrobenius p).commutes])

/-- The underlying action of the changed-uniformizer Frobenius
automorphism is the actual completed inverse-unit lift. -/
@[simp]
theorem padicCompletedChangedUniformizerFrobeniusAlgEquiv_apply
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : padicCompletedLevelField p n) :
    padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n x =
      padicCompletedUnitFrobeniusLiftEquiv p n u⁻¹ x :=
  rfl

/-- The cyclic subgroup generated by the completed changed-uniformizer
Frobenius automorphism. -/
noncomputable def padicCompletedChangedUniformizerFrobeniusSubgroup
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Subgroup
      (padicCompletedLevelField p n ≃ₐ[ℚ_[p]]
        padicCompletedLevelField p n) :=
  Subgroup.zpowers
    (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n)

/-- The field fixed by the actual inverse-unit completed Frobenius lift. -/
noncomputable def padicCompletedChangedUniformizerFixedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IntermediateField ℚ_[p] (padicCompletedLevelField p n) :=
  IntermediateField.fixedField
    (padicCompletedChangedUniformizerFrobeniusSubgroup p u n)

/-- The genuine theta value belongs to the completed Frobenius fixed field. -/
theorem padicChangedUniformizerThetaValue_mem_completedFixedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) ∈
      padicCompletedChangedUniformizerFixedField p u n := by
  rw [padicCompletedChangedUniformizerFixedField,
    IntermediateField.mem_fixedField_iff]
  intro σ hσ
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
  have hfixed :
      (((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n)) ∈
        MulAction.fixedBy
          (padicCompletedLevelField p n)
          (padicCompletedChangedUniformizerFrobeniusAlgEquiv
            p u n) := by
    rw [MulAction.mem_fixedBy]
    change
      padicCompletedUnitFrobeniusLiftEquiv p n u⁻¹
          ((padicChangedUniformizerThetaValue p u n :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
              padicCompletedLevelField p n) =
        _
    exact
      padicCompletedChangedUniformizerThetaValue_fixed_by_diagonalFrobenius
        p u n
  exact MulAction.mem_fixedBy_zpow hfixed j

/-- The completed changed-level embedding is pointwise fixed by the
inverse-unit Frobenius lift. -/
theorem padicChangedUniformizerLevelEmbedding_mem_completedFixedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x :
      standardLubinTateChangedLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u n) :
    padicChangedUniformizerLevelEmbedding p u n x ∈
      padicCompletedChangedUniformizerFixedField p u n := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let L := standardLubinTateLevelField hπ n
  let E := padicCompletedLevelField p n
  let ι : L →ₐ[ℚ_[p]] E :=
    padicChangedUniformizerLevelEmbedding p u n
  let δ : E ≃ₐ[ℚ_[p]] E :=
    padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n
  have hintertwine : δ.toAlgHom.comp ι = ι := by
    apply (standardLubinTateLevelPowerBasis hπ n).algHom_ext
    change
      δ (ι (standardLubinTateLevelPowerBasis hπ n).gen) =
        ι (standardLubinTateLevelPowerBasis hπ n).gen
    rw [show
      ι (standardLubinTateLevelPowerBasis hπ n).gen =
        ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n) by
          exact padicChangedUniformizerLevelEmbedding_apply_gen p u n]
    exact
      padicCompletedChangedUniformizerThetaValue_fixed_by_diagonalFrobenius
        p u n
  rw [padicCompletedChangedUniformizerFixedField,
    IntermediateField.mem_fixedField_iff]
  intro σ hσ
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
  have hfixed :
      ι x ∈ MulAction.fixedBy E δ := by
    rw [MulAction.mem_fixedBy]
    exact DFunLike.congr_fun hintertwine x
  exact MulAction.mem_fixedBy_zpow hfixed j

/-- The finite changed Lubin--Tate level embedded directly into the
completed Frobenius fixed field. -/
noncomputable def padicChangedUniformizerLevelToCompletedFixedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    standardLubinTateChangedLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u n
      →ₐ[ℚ_[p]]
        padicCompletedChangedUniformizerFixedField p u n :=
  (padicChangedUniformizerLevelEmbedding p u n).codRestrict
    (padicCompletedChangedUniformizerFixedField p u n).toSubalgebra
    (padicChangedUniformizerLevelEmbedding_mem_completedFixedField
      p u n)

/-- The fixed-field embedding sends the finite changed-level generator to
the genuine theta value. -/
@[simp]
theorem padicChangedUniformizerLevelToCompletedFixedField_apply_gen
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let hπ :=
      standardLubinTateChangedUniformizer_isUniformizer
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u
    padicChangedUniformizerLevelToCompletedFixedField p u n
        (standardLubinTateLevelPowerBasis hπ n).gen =
      ⟨((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n),
        padicChangedUniformizerThetaValue_mem_completedFixedField
          p u n⟩ := by
  apply Subtype.ext
  exact padicChangedUniformizerLevelEmbedding_apply_gen p u n

/-- A Frobenius-fixed element of the completed level belongs to the
`ℚ_[p]`-field generated by the theta value. -/
theorem padicCompletedChangedUniformizerFrobenius_fixed_mem_adjoin_theta
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : padicCompletedLevelField p n)
    (hx :
      padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n x = x) :
    x ∈ IntermediateField.adjoin ℚ_[p]
      ({((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n)} :
        Set (padicCompletedLevelField p n)) := by
  let A := padicCompletedUnramifiedField p
  let E := padicCompletedLevelField p n
  let φ := padicCompletedUnramifiedFrobenius p
  let δ :=
    padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n
  let y : E :=
    ((padicChangedUniformizerThetaValue p u n :
      (padicCompletedLevelCompleteDVF p n).valuationSubring) : E)
  let pb : PowerBasis A E :=
    padicChangedUniformizerThetaPowerBasis p u n
  let S : IntermediateField ℚ_[p] E :=
    IntermediateField.adjoin ℚ_[p] ({y} : Set E)
  have hδCoeff (c : A) :
      δ (algebraMap A E c) =
        algebraMap A E (φ c) := by
    change
      padicCompletedUnitFrobeniusLiftEquiv p n u⁻¹
          (algebraMap A E c) =
        algebraMap A E
          (padicCompletedUnramifiedFrobenius p c)
    exact
      padicCompletedUnitFrobeniusLiftEquiv_algebraMap p n u⁻¹ c
  have hδY : δ y = y := by
    change
      padicCompletedUnitFrobeniusLiftEquiv p n u⁻¹
          ((padicChangedUniformizerThetaValue p u n :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) : E) =
        _
    exact
      padicCompletedChangedUniformizerThetaValue_fixed_by_diagonalFrobenius
        p u n
  have hδBasis (i : Fin pb.dim) :
      δ (pb.basis i) = pb.basis i := by
    rw [pb.coe_basis, map_pow, show pb.gen = y by
      exact padicChangedUniformizerThetaPowerBasis_gen p u n, hδY]
  have hsemisum :
      (∑ i : Fin pb.dim, φ (pb.basis.repr x i) • pb.basis i) =
        x := by
    calc
      (∑ i : Fin pb.dim, φ (pb.basis.repr x i) • pb.basis i) =
          δ (∑ i : Fin pb.dim,
            pb.basis.repr x i • pb.basis i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Algebra.smul_def, Algebra.smul_def, map_mul,
          hδCoeff, hδBasis]
      _ = δ x := by rw [pb.basis.sum_repr]
      _ = x := hx
  have hcoeff (i : Fin pb.dim) :
      φ (pb.basis.repr x i) = pb.basis.repr x i := by
    have hrepr := congrArg pb.basis.repr hsemisum
    have hi := congrArg (fun c ↦ c i) hrepr
    simp only [map_sum, map_smul, Module.Basis.repr_self,
      Finsupp.smul_single', mul_one] at hi
    rw [Finsupp.finsetSum_apply] at hi
    rw [Finset.sum_eq_single i] at hi
    · simpa only [Finsupp.single_eq_same] using hi
    · intro j hj hji
      exact Finsupp.single_eq_of_ne hji.symm
    · simp
  change x ∈ S
  rw [← pb.basis.sum_repr x]
  apply S.sum_mem
  intro i hi
  rw [pb.coe_basis, Algebra.smul_def]
  apply S.mul_mem
  · obtain ⟨c, hc⟩ :=
      (padicCompletedUnramifiedFrobenius_fixed_iff
        p (pb.basis.repr x i)).1 (hcoeff i)
    change algebraMap A E (pb.basis.repr x i) ∈ S
    rw [← hc, ← IsScalarTower.algebraMap_apply ℚ_[p] A E]
    exact S.algebraMap_mem c
  · have hgen : pb.gen ∈ S := by
      rw [show pb.gen = y by
        exact padicChangedUniformizerThetaPowerBasis_gen p u n]
      exact IntermediateField.mem_adjoin_simple_self ℚ_[p] y
    simpa using S.pow_mem hgen i.val

/-- The completed inverse-unit Frobenius fixed field is exactly the
`ℚ_[p]`-field generated by the theta value. -/
theorem padicCompletedChangedUniformizerFixedField_eq_adjoin_theta
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedChangedUniformizerFixedField p u n =
      IntermediateField.adjoin ℚ_[p]
        ({((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n)} :
          Set (padicCompletedLevelField p n)) := by
  apply le_antisymm
  · intro x hx
    apply
      padicCompletedChangedUniformizerFrobenius_fixed_mem_adjoin_theta
        p u n x
    change x ∈ IntermediateField.fixedField
      (padicCompletedChangedUniformizerFrobeniusSubgroup p u n) at hx
    exact
      (IntermediateField.mem_fixedField_iff
        (H := padicCompletedChangedUniformizerFrobeniusSubgroup
          p u n) x).1 hx
        (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n)
        (Subgroup.mem_zpowers _)
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact
      padicChangedUniformizerThetaValue_mem_completedFixedField p u n

/-- The theta value is integral over `ℚ_[p]`. -/
theorem padicChangedUniformizerThetaValue_isIntegral_padicBase
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsIntegral ℚ_[p]
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) := by
  let πu :=
    standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) u
  refine
    ⟨standardLubinTatePrimitivePolynomialOverField
        (padicLocalField p) πu n,
      standardLubinTatePrimitivePolynomialOverField_monic
        (padicLocalField p) πu n, ?_⟩
  rw [← Polynomial.eval_map]
  exact padicChangedUniformizerThetaValue_field_isRoot p u n

/-- Over `ℚ_[p]`, the theta value has the actual changed Lubin--Tate
primitive polynomial as its minimal polynomial. -/
theorem padicChangedUniformizerThetaValue_minpoly_padicBase
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    minpoly ℚ_[p]
        ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n) =
      standardLubinTatePrimitivePolynomialOverField
        (padicLocalField p)
        (standardLubinTateChangedUniformizer
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let P :=
    standardLubinTatePrimitivePolynomialOverField
      (padicLocalField p)
      (standardLubinTateChangedUniformizer
        (padicLocalField p)
        (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n
  have hroot :
      Polynomial.aeval
          ((padicChangedUniformizerThetaValue p u n :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
              padicCompletedLevelField p n) P =
        0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact padicChangedUniformizerThetaValue_field_isRoot p u n
  have hmin :=
    minpoly.eq_of_irreducible
      (standardLubinTatePrimitivePolynomialOverField_irreducible
        hπ n) hroot
  rw [(standardLubinTatePrimitivePolynomialOverField_monic
    (padicLocalField p)
    (standardLubinTateChangedUniformizer
      (padicLocalField p)
      (padicIntEquivValuationSubring p (p : ℤ_[p])) u) n).leadingCoeff,
    inv_one, Polynomial.C_1, mul_one] at hmin
  exact hmin.symm

noncomputable local instance
    padicCompletedChangedUniformizerFixedFieldAlgebra
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Algebra ℚ_[p]
      (padicCompletedChangedUniformizerFixedField p u n) :=
  Subalgebra.algebra
    (padicCompletedChangedUniformizerFixedField p u n).toSubalgebra

noncomputable local instance
    padicCompletedChangedUniformizerFixedFieldSMul_r94cbaf_1
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    SMul ℚ_[p]
      (padicCompletedChangedUniformizerFixedField p u n) :=
  @Algebra.toSMul _ _ _ _
    (padicCompletedChangedUniformizerFixedFieldAlgebra p u n)
noncomputable local instance
    padicCompletedChangedUniformizerFixedFieldModule
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Module ℚ_[p]
      (padicCompletedChangedUniformizerFixedField p u n) :=
  @Algebra.toModule _ _ _ _
    (padicCompletedChangedUniformizerFixedFieldAlgebra p u n)

/-- The completed changed-uniformizer fixed field has degree
`(p - 1) * p ^ n` over `ℚ_[p]`. -/
theorem padicCompletedChangedUniformizerFixedField_finrank
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Module.finrank ℚ_[p]
        (padicCompletedChangedUniformizerFixedField p u n) =
      (p - 1) * p ^ n := by
  let y : padicCompletedLevelField p n :=
    ((padicChangedUniformizerThetaValue p u n :
      (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n)
  let S := IntermediateField.adjoin ℚ_[p] ({y} :
    Set (padicCompletedLevelField p n))
  let SAlgebra : Algebra ℚ_[p] S :=
    Subalgebra.algebra S.toSubalgebra
  let SSMul : SMul ℚ_[p] S :=
    @Algebra.toSMul _ _ _ _ SAlgebra
  let SModule : Module ℚ_[p] S :=
    @Algebra.toModule _ _ _ _ SAlgebra
  have hfield :
      padicCompletedChangedUniformizerFixedField p u n = S :=
    padicCompletedChangedUniformizerFixedField_eq_adjoin_theta p u n
  have hcard :
      Nat.card (padicLocalField p).residueField = p := by
    simpa [padicLocalField] using
      padicCompleteDVF_residueField_card p
  calc
    Module.finrank ℚ_[p]
        (padicCompletedChangedUniformizerFixedField p u n) =
      Module.finrank ℚ_[p] S :=
        (IntermediateField.equivOfEq hfield).toLinearEquiv.finrank_eq
    _ = (p - 1) * p ^ n := by
      dsimp only [S, y]
      rw [IntermediateField.adjoin.finrank
          (padicChangedUniformizerThetaValue_isIntegral_padicBase
            p u n),
        padicChangedUniformizerThetaValue_minpoly_padicBase,
        standardLubinTatePrimitivePolynomialOverField_natDegree,
        hcard]

/-- The actual finite changed Lubin--Tate level is algebraically equivalent
to the completed inverse-unit Frobenius fixed field. -/
noncomputable def padicChangedUniformizerLevelEquivCompletedFixedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    standardLubinTateChangedLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u n
      ≃ₐ[ℚ_[p]]
        padicCompletedChangedUniformizerFixedField p u n := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let f :=
    padicChangedUniformizerLevelToCompletedFixedField p u n
  letI : FiniteDimensional ℚ_[p]
      (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  letI : FiniteDimensional ℚ_[p]
      (padicCompletedChangedUniformizerFixedField p u n) :=
    FiniteDimensional.of_finrank_pos (by
      rw [padicCompletedChangedUniformizerFixedField_finrank]
      exact Nat.mul_pos
        (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
        (Nat.pow_pos (Fact.out : p.Prime).pos))
  apply AlgEquiv.ofBijective f
  refine ⟨f.injective, ?_⟩
  have hcard :
      Nat.card (padicLocalField p).residueField = p := by
    simpa [padicLocalField] using
      padicCompleteDVF_residueField_card p
  have hdim :
      Module.finrank ℚ_[p]
          (standardLubinTateLevelField hπ n) =
        Module.finrank ℚ_[p]
          (padicCompletedChangedUniformizerFixedField p u n) := by
    rw [standardLubinTateLevelField_finrank,
      padicCompletedChangedUniformizerFixedField_finrank, hcard]
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mp f.injective

/-- The fixed-field equivalence sends the changed finite-level generator
to the genuine theta value. -/
@[simp]
theorem
    padicChangedUniformizerLevelEquivCompletedFixedField_apply_generator
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicChangedUniformizerLevelEquivCompletedFixedField p u n
        (standardLubinTateChangedLevelGenerator
          (padicMultiplicativeLubinTateSeries_isUniformizer p) u n) =
      ⟨((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n),
        padicChangedUniformizerThetaValue_mem_completedFixedField
          p u n⟩ := by
  simp only [padicChangedUniformizerLevelEquivCompletedFixedField]
  exact
    padicChangedUniformizerLevelToCompletedFixedField_apply_gen p u n

/-- The theta value, regarded as an element of the completed Frobenius
fixed field. -/
noncomputable def padicCompletedChangedUniformizerPrimeElement
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedChangedUniformizerFixedField p u n :=
  ⟨((padicChangedUniformizerThetaValue p u n :
      (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n),
    padicChangedUniformizerThetaValue_mem_completedFixedField
      p u n⟩

/-- The fixed-field prime element is the image of the changed finite-level
generator. -/
theorem
    padicCompletedChangedUniformizerPrimeElement_eq_equiv_generator
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedChangedUniformizerPrimeElement p u n =
      padicChangedUniformizerLevelEquivCompletedFixedField p u n
        (standardLubinTateChangedLevelGenerator
          (padicMultiplicativeLubinTateSeries_isUniformizer p) u n) := by
  rw [
    padicChangedUniformizerLevelEquivCompletedFixedField_apply_generator]
  rfl

/-- The completed changed-uniformizer norm formula:
`N(-theta) = u * p`. -/
theorem padicCompletedChangedUniformizer_norm_neg_primeElement
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Algebra.norm ℚ_[p]
        (-padicCompletedChangedUniformizerPrimeElement p u n) =
      (standardLubinTateChangedUniformizer
        (padicLocalField p)
        (padicIntEquivValuationSubring p (p : ℤ_[p])) u :
          ℚ_[p]) := by
  rw [
    padicCompletedChangedUniformizerPrimeElement_eq_equiv_generator,
    ← map_neg, Algebra.norm_eq_of_algEquiv]
  exact
    standardLubinTateChanged_norm_neg_levelGenerator
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u n

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedStandardLevelTransport
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.zHatUnitsDecomposition_freeCoordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.padicChangedUniformizerLevelEquivCompletedFixedField_apply_generator _root_.LubinTate.padicChangedUniformizerLevelToCompletedFixedField_apply_gen _root_.LubinTate.padicChangedUniformizerThetaPowerBasis_gen _root_.LubinTate.padicCompletedChangedUniformizerFrobeniusAlgEquiv_apply _root_.LubinTate.padicCompletedUnitFrobeniusIntegerEquiv_coe _root_.LubinTate.padicCompletedUnitFrobeniusIntegerEquiv_primitiveRoot _root_.LubinTate.padicCompletedUnitFrobeniusIntegerEquiv_symm_coe _root_.LubinTate.padicCompletedUnitFrobeniusLiftEquiv_symm_algebraMap _root_.LubinTate.padicCompletedUnramifiedFrobeniusIntegerEquiv_coe _root_.LubinTate.padicCompletedUnramifiedFrobeniusIntegerEquiv_symm_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Transporting a finite p-adic Lubin--Tate level to the completed level

The ordinary standard Lubin--Tate level embeds in the completed level by
sending its primitive generator to the chosen completed primitive point.
This file proves that the embedding also preserves the integral analytic
action.  In particular, the direct completed action of a p-adic unit is
the image of the finite action with the *same* unit-parameter class.

This fixes the parameter orientation before the completed Frobenius is
used in the changed-uniformizer norm argument.
-/

noncomputable section

open scoped PowerSeries

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

noncomputable local instance
    padicStandardLevelTransportCoefficientUniformSpace
    (p : ℕ) [Fact p.Prime] :
    UniformSpace (padicLocalField p).valuationSubring :=
  ⊥

noncomputable local instance
    padicStandardLevelTransportCoefficientTopologicalSpace
    (p : ℕ) [Fact p.Prime] :
    TopologicalSpace (padicLocalField p).valuationSubring :=
  ⊥

noncomputable local instance (priority := 50)
    padicStandardLevelTransportWittUniformSpace
    (p : ℕ) [Fact p.Prime] :
    UniformSpace (padicCompletedUnramifiedWittRing p) :=
  ⊥

noncomputable local instance
    padicStandardLevelTransportSourceWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring where
  i :=
    (standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
    ).maximalIdeal

noncomputable local instance
    padicStandardLevelTransportTargetWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (padicCompletedLevelCompleteDVF p n).valuationSubring where
  i := (padicCompletedLevelCompleteDVF p n).maximalIdeal

noncomputable local instance (priority := 2000)
    padicStandardLevelTransportSourceUniformSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    UniformSpace
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring :=
  WithIdeal.instUniformSpace _

noncomputable local instance (priority := 2000)
    padicStandardLevelTransportSourceTopologicalSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    TopologicalSpace
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring :=
  (padicStandardLevelTransportSourceUniformSpace p n).toTopologicalSpace

noncomputable local instance (priority := 2000)
    padicStandardLevelTransportTargetTopologicalSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    TopologicalSpace (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  WithIdeal.instUniformSpace _ |>.toTopologicalSpace

noncomputable local instance (priority := 2000)
    padicStandardLevelTransportTargetUniformSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    UniformSpace (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  WithIdeal.instUniformSpace _

noncomputable local instance
    padicStandardLevelTransportSourceCompleteSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring := by
  let source :=
    standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
  have hadic : IsAdic source.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp source.isAdicComplete).1

noncomputable local instance
    padicStandardLevelTransportSourceT2Space
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring := by
  let source :=
    standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
  have hadic : IsAdic source.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp source.isAdicComplete).2

noncomputable local instance
    padicStandardLevelTransportTargetCompleteSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

noncomputable local instance
    padicStandardLevelTransportTargetT2Space
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

/-- The standard finite-level embedding restricted to the actual valuation
rings. -/
noncomputable def padicStandardLevelIntegerEmbedding
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring →+*
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let source := standardLubinTateLevelCompleteDVF hπ n
  let A := padicCompletedUnramifiedCompleteDVF p
  let E := padicCompletedLevelField p n
  let target := padicCompletedLevelCompleteDVF p n
  let ι : L →ₐ[ℚ_[p]] E := padicStandardLevelEmbedding p n
  letI : F.valuation.HasExtension source.valuation :=
    standardLubinTateLevelCompleteDVF_hasExtension
      (F := padicLocalField p)
      (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  letI : Algebra F.valuationSubring source.valuationSubring :=
    Valuation.HasExtension.instAlgebra_valuationSubring
      (padicLocalField p).valuation
      (standardLubinTateLevelCompleteDVF
        (F := padicLocalField p)
        (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n).valuation
  letI : IsScalarTower F.valuationSubring source.valuationSubring L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure
      source.valuationSubring F.valuationSubring L :=
    standardLubinTateLevelCompleteDVF_isIntegralClosure hπ n
  letI : IsScalarTower A.valuationSubring target.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure
      target.valuationSubring A.valuationSubring E :=
    padicCompletedLevelCompleteDVF_isIntegralClosure p n
  let f : source.valuationSubring →+* E :=
    ι.toRingHom.comp source.valuation.valuationSubring.subtype
  apply RingHom.codRestrict f target.valuation.valuationSubring
  intro x
  have hxIntegral :
      IsIntegral F.valuationSubring (x : L) :=
    (IsIntegralClosure.isIntegral_iff
      (A := source.valuationSubring)
      (R := F.valuationSubring)
      (B := L)).2 ⟨x, rfl⟩
  have hcomp :
      (algebraMap A.valuationSubring E).comp
          (padicCompletedUnramifiedIntegerMap p) =
        ι.toRingHom.comp (algebraMap F.valuationSubring L) := by
    ext a
    simp only [RingHom.comp_apply]
    change
      algebraMap (padicCompletedUnramifiedField p) E
          ((padicCompletedUnramifiedIntegerMap p a :
            A.valuationSubring) :
              padicCompletedUnramifiedField p) =
        ι (algebraMap ℚ_[p] L (a : ℚ_[p]))
    rw [padicCompletedUnramifiedIntegerMap_coe]
    calc
      algebraMap (padicCompletedUnramifiedField p) E
          (algebraMap ℚ_[p]
            (padicCompletedUnramifiedField p) (a : ℚ_[p])) =
          algebraMap ℚ_[p] E (a : ℚ_[p]) :=
        (IsScalarTower.algebraMap_apply ℚ_[p]
          (padicCompletedUnramifiedField p) E (a : ℚ_[p])).symm
      _ = ι (algebraMap ℚ_[p] L (a : ℚ_[p])) :=
        (ι.commutes (a : ℚ_[p])).symm
  have hxMappedIntegral :
      IsIntegral A.valuationSubring (ι (x : L)) :=
    IsIntegral.map_of_comp_eq
      (padicCompletedUnramifiedIntegerMap p)
      ι.toRingHom hcomp hxIntegral
  rcases
      (IsIntegralClosure.isIntegral_iff
        (A := target.valuationSubring)
        (R := A.valuationSubring)
        (B := E)).1 hxMappedIntegral with
    ⟨z, hz⟩
  exact hz ▸ z.property

/-- Coercing the integral standard-level embedding to the completed field
recovers the field embedding. -/
@[simp]
theorem padicStandardLevelIntegerEmbedding_coe
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring) :
    ((padicStandardLevelIntegerEmbedding p n x :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
        padicStandardLevelEmbedding p n
          (x :
            standardLubinTateLevelField
              (padicMultiplicativeLubinTateSeries_isUniformizer p) n) := by
  rfl

/-- The integral embedding sends the finite primitive point to the chosen
completed primitive point. -/
@[simp]
theorem padicStandardLevelIntegerEmbedding_apply_primitivePoint
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    padicStandardLevelIntegerEmbedding p n
        (standardLubinTatePrimitivePointInteger hπ n) =
      padicCompletedPrimitiveRootInteger p n := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  apply Subtype.ext
  rw [padicStandardLevelIntegerEmbedding_coe,
    padicCompletedPrimitiveRootInteger_coe]
  have hpoint := congrArg (padicStandardLevelEmbedding p n)
    (standardLubinTatePrimitivePointInteger_coe
      (F := padicLocalField p) hπ n)
  exact hpoint.trans (padicStandardLevelEmbedding_apply_gen p n)

/-- The integral standard-level embedding is continuous for the two
maximal-ideal adic topologies. -/
theorem padicStandardLevelIntegerEmbedding_continuous
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Continuous (padicStandardLevelIntegerEmbedding p n) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let source := standardLubinTateLevelCompleteDVF hπ n
  let target := padicCompletedLevelCompleteDVF p n
  let f : source.valuationSubring →+* target.valuationSubring :=
    padicStandardLevelIntegerEmbedding p n
  have hmap :
      Ideal.map f source.maximalIdeal ≤ target.maximalIdeal := by
    rw [source.maximalIdeal_eq_span_uniformizer
      (standardLubinTatePrimitivePoint_isUniformizer hπ n),
      Ideal.map_span, Set.image_singleton, Ideal.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    change
      padicStandardLevelIntegerEmbedding p n
          (standardLubinTatePrimitivePointInteger hπ n) ∈
        target.maximalIdeal
    rw [padicStandardLevelIntegerEmbedding_apply_primitivePoint]
    exact padicCompletedPrimitiveRootInteger_mem_maximalIdeal p n
  exact
    (WithIdeal.uniformContinuous_of_map_le (f := f) hmap).continuous

/-- The integral embedding commutes with the canonical maps of p-adic
integer coefficients. -/
theorem padicStandardLevelIntegerEmbedding_comp_coefficientHom
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    (padicStandardLevelIntegerEmbedding p n).comp
        (standardLubinTateLevelCoefficientHom hπ n) =
      padicCompletedLevelPadicIntegerCoefficientHom p n := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let E := padicCompletedLevelField p n
  ext a
  simp only [RingHom.comp_apply,
    padicStandardLevelIntegerEmbedding_coe,
    padicCompletedLevelPadicIntegerCoefficientHom_coe]
  change
    padicStandardLevelEmbedding p n
        (algebraMap ℚ_[p] L (a : ℚ_[p])) =
      algebraMap (padicCompletedUnramifiedField p) E
        (algebraMap ℚ_[p]
          (padicCompletedUnramifiedField p) (a : ℚ_[p]))
  rw [(padicStandardLevelEmbedding p n).commutes,
    ← IsScalarTower.algebraMap_apply ℚ_[p]
      (padicCompletedUnramifiedField p) E]

/-- Evaluation after extending p-adic coefficients to the completed Witt
ring is evaluation through the direct p-adic coefficient map. -/
theorem padicCompletedLevelPowerSeriesEval_map_padicCoefficients
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (f : PowerSeries (padicLocalField p).valuationSubring) :
    padicCompletedLevelPowerSeriesEval p n x hx
        (PowerSeries.map
          (padicValuationSubringToCompletedUnramifiedWittRing p) f) =
      PowerSeries.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x f := by
  have hpadic :
      Continuous (padicCompletedLevelPadicIntegerCoefficientHom p n) :=
    continuous_of_discreteTopology
  rw [padicCompletedLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom,
    PowerSeries.eval₂_eq_tsum
      (padicCompletedLevelWittCoefficientHom_continuous p n) hx,
    PowerSeries.eval₂_eq_tsum hpadic hx]
  apply tsum_congr
  intro d
  rw [PowerSeries.coeff_map]
  rfl

/-- Analytic evaluation in the finite standard level commutes with its
integral embedding into the completed level. -/
theorem padicStandardLevelIntegerEmbedding_powerSeriesEval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (f : PowerSeries (padicLocalField p).valuationSubring) :
    padicStandardLevelIntegerEmbedding p n
        (standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          n x hx f) =
      padicCompletedLevelPowerSeriesEval p n
        (padicStandardLevelIntegerEmbedding p n x)
        (hx.map (padicStandardLevelIntegerEmbedding_continuous p n))
        (PowerSeries.map
          (padicValuationSubringToCompletedUnramifiedWittRing p) f) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let j := padicStandardLevelIntegerEmbedding p n
  have hraw :=
    congrFun
      (PowerSeries.comp_eval₂
        (φ := standardLubinTateLevelCoefficientHom hπ n)
        continuous_of_discreteTopology hx
        (padicStandardLevelIntegerEmbedding_continuous p n)) f
  have htransport :
      j
          (PowerSeries.eval₂
            (standardLubinTateLevelCoefficientHom hπ n) x f) =
        PowerSeries.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (j x) f := by
    rw [← padicStandardLevelIntegerEmbedding_comp_coefficientHom p n]
    simpa only [Function.comp_apply] using hraw
  calc
    j
        (standardLubinTateLevelPowerSeriesEval hπ n x hx f) =
        PowerSeries.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (j x) f := by
      simpa only [standardLubinTateLevelPowerSeriesEval,
        PowerSeries.coe_eval₂Hom] using htransport
    _ =
        padicCompletedLevelPowerSeriesEval p n (j x)
          (hx.map (padicStandardLevelIntegerEmbedding_continuous p n))
          (PowerSeries.map
            (padicValuationSubringToCompletedUnramifiedWittRing p) f) :=
      (padicCompletedLevelPowerSeriesEval_map_padicCoefficients
        p n (j x)
        (hx.map (padicStandardLevelIntegerEmbedding_continuous p n))
        f).symm

/-- The integral embedding carries the finite analytic unit action to the
direct completed analytic unit action with the same unit. -/
@[simp]
theorem
    padicStandardLevelIntegerEmbedding_apply_primitivePointUnitAction
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    padicStandardLevelIntegerEmbedding p n
        (standardLubinTatePrimitivePointIntegerAction hπ n u) =
      padicCompletedStandardPrimitivePointUnitAction p n u := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  have h :=
    padicStandardLevelIntegerEmbedding_powerSeriesEval p n
      (standardLubinTatePrimitivePointInteger hπ n)
      (standardLubinTatePrimitivePointInteger_hasEval hπ n)
      (standardLubinTateEndomorphism hπ
        (u : (padicLocalField p).valuationSubring))
  simpa only [
    standardLubinTatePrimitivePointIntegerAction,
    standardLubinTateEndomorphismValue,
    standardLubinTateEndomorphismEvalAt,
    padicCompletedStandardPrimitivePointUnitAction,
    padicCompletedStandardScalarEndomorphismValue,
    padicCompletedStandardScalarEndomorphism,
    padicStandardLevelIntegerEmbedding_apply_primitivePoint] using h

/-- At the finite p-adic level, the parameter class of a unit realizes
exactly its direct analytic action. -/
theorem padicStandardUnitParameterLevelRoot_class
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let F := padicLocalField p
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    standardLubinTateUnitParameterLevelRoot F hπ n
        (standardLubinTateUnitParameterClass F n u) =
      standardLubinTatePrimitiveLevelAction hπ n u := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  apply Subtype.ext
  exact (standardLubinTateUnitParameterLevelRoot_coe F hπ n
    (standardLubinTateUnitParameterClass F n u)).trans
      ((standardLubinTateUnitParameterRoot_class F hπ n u).trans
        (standardLubinTatePrimitiveLevelAction_coe
          (F := F) hπ n u).symm)

/-- The direct completed unit action is the completed realization of the
same finite unit-parameter class. -/
@[simp]
theorem
    padicCompletedStandardPrimitivePointUnitAction_eq_unitParameterRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    ((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
        padicCompletedUnitParameterRoot p n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let source := standardLubinTateLevelCompleteDVF hπ n
  calc
    ((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
        ((padicStandardLevelIntegerEmbedding p n
            (standardLubinTatePrimitivePointIntegerAction hπ n u) :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n) := by
      rw [
        padicStandardLevelIntegerEmbedding_apply_primitivePointUnitAction]
    _ =
        padicStandardLevelEmbedding p n
          ((standardLubinTatePrimitivePointIntegerAction hπ n u :
            source.valuationSubring) :
              standardLubinTateLevelField hπ n) := by
      rw [padicStandardLevelIntegerEmbedding_coe]
    _ =
        padicStandardLevelEmbedding p n
          (standardLubinTateUnitParameterLevelRoot
            (padicLocalField p) hπ n
            (standardLubinTateUnitParameterClass
              (padicLocalField p) n u)) := by
      congr 1
      change
        standardLubinTatePrimitiveLevelAction hπ n u =
          standardLubinTateUnitParameterLevelRoot
            (padicLocalField p) hπ n
            (standardLubinTateUnitParameterClass
              (padicLocalField p) n u)
      exact (padicStandardUnitParameterLevelRoot_class p n u).symm
    _ =
        padicCompletedUnitParameterRoot p n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) :=
      rfl

/-- The completed unit-indexed Frobenius lift restricts to the finite
standard-level automorphism with the same unit-parameter class. -/
theorem padicCompletedUnitFrobeniusLiftEquiv_standardLevelEmbedding
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x :
      standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :
    padicCompletedUnitFrobeniusLiftEquiv p n u
        (padicStandardLevelEmbedding p n x) =
      padicStandardLevelEmbedding p n
        (standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) x) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let E := padicCompletedLevelField p n
  let ι : L →ₐ[ℚ_[p]] E := padicStandardLevelEmbedding p n
  let δ : E →ₐ[ℚ_[p]] E :=
    { toRingHom :=
        (padicCompletedUnitFrobeniusLiftEquiv p n u).toRingHom
      commutes' := by
        intro b
        change
          padicCompletedUnitFrobeniusLiftEquiv p n u
              (algebraMap (padicCompletedUnramifiedField p) E
                (algebraMap ℚ_[p]
                  (padicCompletedUnramifiedField p) b)) =
            algebraMap (padicCompletedUnramifiedField p) E
              (algebraMap ℚ_[p]
                (padicCompletedUnramifiedField p) b)
        rw [padicCompletedUnitFrobeniusLiftEquiv_algebraMap,
          (padicCompletedUnramifiedFrobenius p).commutes] }
  let σ : L ≃ₐ[ℚ_[p]] L :=
    standardLubinTateUnitParameterAlgEquiv
      (padicLocalField p) hπ n
      (standardLubinTateUnitParameterClass
        (padicLocalField p) n u)
  have hintertwine : δ.comp ι = ι.comp σ.toAlgHom := by
    apply (standardLubinTateLevelPowerBasis hπ n).algHom_ext
    change
      padicCompletedUnitFrobeniusLiftEquiv p n u
          (padicStandardLevelEmbedding p n
            (standardLubinTateLevelPowerBasis hπ n).gen) =
        padicStandardLevelEmbedding p n
          (standardLubinTateUnitParameterAlgEquiv
            (padicLocalField p) hπ n
            (standardLubinTateUnitParameterClass
              (padicLocalField p) n u)
            (standardLubinTateLevelPowerBasis hπ n).gen)
    rw [padicStandardLevelEmbedding_apply_gen,
      padicCompletedUnitFrobeniusLiftEquiv_primitiveRoot]
    have hgen := congrArg (padicStandardLevelEmbedding p n)
      (standardLubinTateUnitParameterAlgEquiv_apply_gen
        (padicLocalField p) hπ n
        (standardLubinTateUnitParameterClass (padicLocalField p) n u))
    exact (padicCompletedStandardPrimitivePointUnitAction_eq_unitParameterRoot
      p n u).trans hgen.symm
  exact DFunLike.congr_fun hintertwine x

/-- The inverse completed unit-indexed Frobenius lift restricts to the
inverse finite unit-parameter automorphism. -/
theorem padicCompletedUnitFrobeniusLiftEquiv_symm_standardLevelEmbedding
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x :
      standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :
    (padicCompletedUnitFrobeniusLiftEquiv p n u).symm
        (padicStandardLevelEmbedding p n x) =
      padicStandardLevelEmbedding p n
        ((standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u)).symm x) := by
  apply (padicCompletedUnitFrobeniusLiftEquiv p n u).injective
  rw [
    (padicCompletedUnitFrobeniusLiftEquiv p n u).apply_symm_apply,
    padicCompletedUnitFrobeniusLiftEquiv_standardLevelEmbedding,
    (standardLubinTateUnitParameterAlgEquiv
      (padicLocalField p)
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      (standardLubinTateUnitParameterClass
        (padicLocalField p) n u)).apply_symm_apply]

/-- With the inverse unit as Frobenius-lift parameter, the inverse completed
lift acts on the standard finite level by the direct unit parameter.  This is
the orientation used by the actual local Artin map after changed-uniformizer
descent. -/
theorem
    padicCompletedInverseUnitFrobeniusLiftEquiv_standardLevelEmbedding
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x :
      standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :
    (padicCompletedUnitFrobeniusLiftEquiv p n u⁻¹).symm
        (padicStandardLevelEmbedding p n x) =
      padicStandardLevelEmbedding p n
        (standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) x) := by
  rw [
    padicCompletedUnitFrobeniusLiftEquiv_symm_standardLevelEmbedding]
  have hclass :
      standardLubinTateUnitParameterClass
          (padicLocalField p) n u⁻¹ =
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u)⁻¹ :=
    (standardLubinTateUnitParameterClass
      (padicLocalField p) n).map_inv u
  have hparameter :
      standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u⁻¹) =
        (standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u))⁻¹ := by
    change
      standardLubinTateUnitParameterEquivGal
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u⁻¹) =
        (standardLubinTateUnitParameterEquivGal
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u))⁻¹
    rw [hclass,
      (standardLubinTateUnitParameterEquivGal
        (padicLocalField p)
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).map_inv]
  rw [hparameter]
  rfl

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedChangedStandardCompositum
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseNontriviallyNormedField _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.zHatUnitsDecomposition_freeCoordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The finite standard/changed compositum in the completed p-adic level

The completed level contains two finite abelian extensions of `ℚ_[p]`:

* the image of the ordinary standard multiplicative Lubin--Tate level;
* the fixed field of the inverse-unit completed Frobenius lift, identified
  with the changed-uniformizer level.

Their compositum is therefore a genuine finite abelian extension.  The
inverse of the Frobenius lift preserves this compositum, fixes the changed
factor, and acts on the standard factor by the direct unit parameter.  This
is the finite automorphism which the changed-uniformizer norm calculation
will identify with the actual local Artin symbol.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- The copy of the ordinary standard multiplicative level inside the
completed level. -/
def padicCompletedStandardLevelField
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IntermediateField ℚ_[p] (padicCompletedLevelField p n) :=
  (padicStandardLevelEmbedding p n).fieldRange

/-- The ordinary standard level is equivalent to its image in the completed
level. -/
noncomputable def padicStandardLevelEquivCompletedStandardLevelField
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ≃ₐ[ℚ_[p]]
        padicCompletedStandardLevelField p n :=
  AlgEquiv.ofInjectiveField (padicStandardLevelEmbedding p n)

noncomputable instance
    padicCompletedStandardLevelField_finiteDimensional
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    FiniteDimensional ℚ_[p]
      (padicCompletedStandardLevelField p n) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let : FiniteDimensional ℚ_[p]
      (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let e := padicStandardLevelEquivCompletedStandardLevelField p n
  exact e.toLinearEquiv.finiteDimensional

noncomputable instance
    padicCompletedStandardLevelField_isAbelianGalois
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsAbelianGalois ℚ_[p]
      (padicCompletedStandardLevelField p n) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let : IsAbelianGalois ℚ_[p] (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_isAbelianGalois (padicLocalField p)
      (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  exact IsAbelianGalois.of_algHom
    (padicStandardLevelEquivCompletedStandardLevelField p n).symm.toAlgHom

noncomputable instance
    padicCompletedChangedUniformizerFixedField_finiteDimensional
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    FiniteDimensional ℚ_[p]
      (padicCompletedChangedUniformizerFixedField p u n) := by
  let hπ :=
    standardLubinTateChangedUniformizer_isUniformizer
      (padicMultiplicativeLubinTateSeries_isUniformizer p) u
  let : FiniteDimensional ℚ_[p]
      (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let e := padicChangedUniformizerLevelEquivCompletedFixedField p u n
  exact e.toLinearEquiv.finiteDimensional

noncomputable instance
    padicCompletedChangedUniformizerFixedField_isAbelianGalois
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsAbelianGalois ℚ_[p]
      (padicCompletedChangedUniformizerFixedField p u n) :=
  IsAbelianGalois.of_algHom
    (padicChangedUniformizerLevelEquivCompletedFixedField p u n).symm.toAlgHom

/-- The finite compositum of the standard level and the actual
changed-uniformizer fixed field inside the completed level. -/
def padicCompletedStandardChangedCompositum
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IntermediateField ℚ_[p] (padicCompletedLevelField p n) :=
  padicCompletedStandardLevelField p n ⊔
    padicCompletedChangedUniformizerFixedField p u n

noncomputable instance
    padicCompletedStandardChangedCompositum_finiteDimensional
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    FiniteDimensional ℚ_[p]
      (padicCompletedStandardChangedCompositum p u n) :=
  IntermediateField.finiteDimensional_sup
    (padicCompletedStandardLevelField p n)
    (padicCompletedChangedUniformizerFixedField p u n)

noncomputable instance
    padicCompletedStandardChangedCompositum_isAbelianGalois
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsAbelianGalois ℚ_[p]
      (padicCompletedStandardChangedCompositum p u n) :=
  AlgebraicNumberTheory.isAbelianGalois_sup ℚ_[p]
    (padicCompletedStandardLevelField p n)
    (padicCompletedChangedUniformizerFixedField p u n)

noncomputable instance
    padicCompletedStandardChangedCompositum_changedFieldAlgebra
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    Algebra (padicCompletedChangedUniformizerFixedField p u n)
      (padicCompletedStandardChangedCompositum p u n) :=
  (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra

instance padicCompletedStandardChangedCompositum_changedFieldScalarTower
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsScalarTower ℚ_[p]
      (padicCompletedChangedUniformizerFixedField p u n)
      (padicCompletedStandardChangedCompositum p u n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The standard finite level embedded into the finite standard/changed
compositum. -/
noncomputable def padicStandardLevelToCompletedChangedCompositum
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      →ₐ[ℚ_[p]]
        padicCompletedStandardChangedCompositum p u n :=
  (padicStandardLevelEmbedding p n).codRestrict
    (padicCompletedStandardChangedCompositum p u n).toSubalgebra
    (fun x =>
      (show padicCompletedStandardLevelField p n ≤
          padicCompletedStandardChangedCompositum p u n from le_sup_left)
      (show padicStandardLevelEmbedding p n x ∈
          padicCompletedStandardLevelField p n from
        ⟨x, rfl⟩))

/-- The changed fixed field included into the finite standard/changed
compositum. -/
noncomputable def
    padicCompletedChangedFixedFieldToStandardChangedCompositum
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedChangedUniformizerFixedField p u n
      →ₐ[ℚ_[p]]
        padicCompletedStandardChangedCompositum p u n :=
  IntermediateField.inclusion le_sup_right

/-- The inverse-unit Frobenius inverse carries the standard completed copy
to itself. -/
theorem
    padicCompletedChangedUniformizerFrobenius_symm_map_standard_le
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicCompletedStandardLevelField p n).map
        (padicCompletedChangedUniformizerFrobeniusAlgEquiv
          p u n).symm.toAlgHom ≤
      padicCompletedStandardLevelField p n := by
  rw [IntermediateField.map_le_iff_le_comap]
  intro x hx
  change
    (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm x ∈
      padicCompletedStandardLevelField p n
  change x ∈ (padicStandardLevelEmbedding p n).fieldRange at hx
  change
    (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm x ∈
      (padicStandardLevelEmbedding p n).fieldRange
  rw [AlgHom.mem_fieldRange] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine
    ⟨standardLubinTateUnitParameterAlgEquiv
        (padicLocalField p)
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u) y, ?_⟩
  exact
    (padicCompletedInverseUnitFrobeniusLiftEquiv_standardLevelEmbedding
      p n u y).symm

/-- Every element of the changed fixed field is fixed by the inverse of its
defining Frobenius lift. -/
theorem
    padicCompletedChangedUniformizerFrobenius_symm_fixed
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : padicCompletedChangedUniformizerFixedField p u n) :
    (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm
      (x : padicCompletedLevelField p n) =
        x := by
  have hxFixed :
      padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n
          (x : padicCompletedLevelField p n) =
        x := by
    have hxmem := x.property
    change
      (x : padicCompletedLevelField p n) ∈
        IntermediateField.fixedField
          (padicCompletedChangedUniformizerFrobeniusSubgroup p u n)
      at hxmem
    rw [IntermediateField.mem_fixedField_iff] at hxmem
    exact hxmem
      (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n)
      (Subgroup.mem_zpowers
        (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n))
  calc
    (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm
        (x : padicCompletedLevelField p n) =
      (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm
        (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n x) := by
          rw [hxFixed]
    _ = x :=
      (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm_apply_apply x

/-- The inverse defining Frobenius carries the changed fixed field to
itself. -/
theorem
    padicCompletedChangedUniformizerFrobenius_symm_map_fixedField_le
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicCompletedChangedUniformizerFixedField p u n).map
        (padicCompletedChangedUniformizerFrobeniusAlgEquiv
          p u n).symm.toAlgHom ≤
      padicCompletedChangedUniformizerFixedField p u n := by
  rw [IntermediateField.map_le_iff_le_comap]
  intro x hx
  change
    (padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm x ∈
      padicCompletedChangedUniformizerFixedField p u n
  have hfixed :=
    padicCompletedChangedUniformizerFrobenius_symm_fixed p u n
      ⟨x, hx⟩
  rw [hfixed]
  exact hx

/-- The inverse defining Frobenius preserves the finite standard/changed
compositum. -/
theorem
    padicCompletedChangedUniformizerFrobenius_symm_map_compositum_le
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicCompletedStandardChangedCompositum p u n).map
        (padicCompletedChangedUniformizerFrobeniusAlgEquiv
          p u n).symm.toAlgHom ≤
      padicCompletedStandardChangedCompositum p u n := by
  rw [padicCompletedStandardChangedCompositum,
    IntermediateField.map_sup]
  exact sup_le_sup
    (padicCompletedChangedUniformizerFrobenius_symm_map_standard_le
      p u n)
    (padicCompletedChangedUniformizerFrobenius_symm_map_fixedField_le
      p u n)

/-- The inverse defining Frobenius restricted to the genuine finite
standard/changed compositum. -/
noncomputable def padicCompletedChangedUniformizerArtinCandidateAlgHom
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedStandardChangedCompositum p u n
      →ₐ[ℚ_[p]]
        padicCompletedStandardChangedCompositum p u n :=
  (((padicCompletedChangedUniformizerFrobeniusAlgEquiv p u n).symm.toAlgHom).comp
        (padicCompletedStandardChangedCompositum p u n).val).codRestrict
    (padicCompletedStandardChangedCompositum p u n).toSubalgebra
    (fun x => by
      apply
        padicCompletedChangedUniformizerFrobenius_symm_map_compositum_le
          p u n
      rw [IntermediateField.mem_map]
      exact ⟨x, x.property, rfl⟩)

/-- The finite Artin candidate is an automorphism. -/
noncomputable def padicCompletedChangedUniformizerArtinCandidate
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedStandardChangedCompositum p u n
      ≃ₐ[ℚ_[p]]
        padicCompletedStandardChangedCompositum p u n := by
  let f :=
    padicCompletedChangedUniformizerArtinCandidateAlgHom p u n
  apply AlgEquiv.ofBijective f
  refine ⟨f.injective, ?_⟩
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) rfl).mp f.injective

/-- On the standard factor, the finite Artin candidate is the direct
unit-parameter automorphism. -/
@[simp]
theorem
    padicCompletedChangedUniformizerArtinCandidate_standardLevel
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x :
      standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :
    padicCompletedChangedUniformizerArtinCandidate p u n
        (padicStandardLevelToCompletedChangedCompositum p u n x) =
      padicStandardLevelToCompletedChangedCompositum p u n
        (standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) x) := by
  apply Subtype.ext
  exact
    padicCompletedInverseUnitFrobeniusLiftEquiv_standardLevelEmbedding
      p n u x

/-- On the changed factor, the finite Artin candidate is the identity. -/
@[simp]
theorem
    padicCompletedChangedUniformizerArtinCandidate_fixedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : padicCompletedChangedUniformizerFixedField p u n) :
    padicCompletedChangedUniformizerArtinCandidate p u n
        (padicCompletedChangedFixedFieldToStandardChangedCompositum
          p u n x) =
      padicCompletedChangedFixedFieldToStandardChangedCompositum
        p u n x := by
  apply Subtype.ext
  exact
    padicCompletedChangedUniformizerFrobenius_symm_fixed p u n x

/-- The finite Artin candidate as an automorphism over the changed fixed
field that it fixes pointwise. -/
noncomputable def
    padicCompletedChangedUniformizerRelativeArtinCandidate
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedStandardChangedCompositum p u n
      ≃ₐ[padicCompletedChangedUniformizerFixedField p u n]
        padicCompletedStandardChangedCompositum p u n where
  __ := (padicCompletedChangedUniformizerArtinCandidate p u n).toRingEquiv
  commutes' x :=
    padicCompletedChangedUniformizerArtinCandidate_fixedField
      p u n x

/-- Forgetting the changed-field scalar structure recovers the original
finite candidate. -/
@[simp]
theorem padicCompletedChangedUniformizerRelativeArtinCandidate_apply
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ)
    (x : padicCompletedStandardChangedCompositum p u n) :
    padicCompletedChangedUniformizerRelativeArtinCandidate p u n x =
      padicCompletedChangedUniformizerArtinCandidate p u n x :=
  rfl

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedPrimitiveUniformizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadicTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.padicCompletedChangedUniformizerFixedField_finiteDimensional _root_.LubinTate.padicCompletedChangedUniformizerFixedField_isAbelianGalois _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_finiteDimensional _root_.LubinTate.padicCompletedStandardChangedCompositum_isAbelianGalois _root_.LubinTate.padicCompletedStandardLevelField_finiteDimensional _root_.LubinTate.padicCompletedStandardLevelField_isAbelianGalois _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.zHatUnitsDecomposition_freeCoordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.padicChangedUniformizerLevelEquivCompletedFixedField_apply_generator _root_.LubinTate.padicChangedUniformizerLevelToCompletedFixedField_apply_gen _root_.LubinTate.padicCompletedChangedUniformizerArtinCandidate_fixedField _root_.LubinTate.padicCompletedChangedUniformizerArtinCandidate_standardLevel _root_.LubinTate.padicCompletedChangedUniformizerFrobeniusAlgEquiv_apply _root_.LubinTate.padicCompletedChangedUniformizerRelativeArtinCandidate_apply _root_.LubinTate.padicCompletedStandardPrimitivePointUnitAction_eq_unitParameterRoot _root_.LubinTate.padicCompletedUnitFrobeniusIntegerEquiv_coe _root_.LubinTate.padicCompletedUnitFrobeniusIntegerEquiv_primitiveRoot _root_.LubinTate.padicCompletedUnitFrobeniusIntegerEquiv_symm_coe _root_.LubinTate.padicCompletedUnitFrobeniusLiftAlgHom_primitiveRoot _root_.LubinTate.padicCompletedUnitFrobeniusLiftEquiv_algebraMap _root_.LubinTate.padicCompletedUnitFrobeniusLiftEquiv_primitiveRoot _root_.LubinTate.padicCompletedUnitFrobeniusLiftEquiv_symm_algebraMap _root_.LubinTate.padicCompletedUnitFrobeniusLift_algebraMap _root_.LubinTate.padicCompletedUnitFrobeniusLift_primitiveRoot _root_.LubinTate.padicCompletedUnramifiedFrobeniusIntegerEquiv_coe _root_.LubinTate.padicCompletedUnramifiedFrobeniusIntegerEquiv_symm_coe _root_.LubinTate.padicStandardLevelIntegerEmbedding_apply_primitivePoint _root_.LubinTate.padicStandardLevelIntegerEmbedding_apply_primitivePointUnitAction _root_.LubinTate.padicStandardLevelIntegerEmbedding_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

noncomputable local instance
    padicCompletedPrimitiveUniformizerTargetWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (padicCompletedLevelCompleteDVF p n).valuationSubring where
  i := (padicCompletedLevelCompleteDVF p n).maximalIdeal

theorem
    padicCompletedPrimitiveRootInteger_addVal_and_ramificationIndex
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsDiscreteValuationRing.addVal
        (padicCompletedLevelCompleteDVF p n).valuationSubring
        (padicCompletedPrimitiveRootInteger p n) = 1 ∧
      ramificationIndex
          (padicCompletedUnramifiedCompleteDVF p).toDVF
          (padicCompletedLevelCompleteDVF p n).toDVF =
        degree
          (padicCompletedUnramifiedCompleteDVF p).toDVF
          (padicCompletedLevelCompleteDVF p n).toDVF := by
  let A := padicCompletedUnramifiedField p
  let E := padicCompletedLevelField p n
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let Q := padicCompletedPrimitivePolynomialInteger p n
  let d := (p - 1) * p ^ n
  let e := ramificationIndex base.toDVF target.toDVF
  let f := residueDegree base.toDVF target.toDVF
  let 𝔭 := base.maximalIdeal
  let 𝔓 := target.maximalIdeal
  let j := integerMap base.toDVF target.toDVF
  let root := padicCompletedPrimitiveRootInteger p n
  let R := Q - Polynomial.X ^ d
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let πA : base.valuationSubring :=
    padicCompletedUnramifiedIntegerMap p π
  let : IsScalarTower base.valuationSubring
      target.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
      (Nat.pow_pos (Fact.out : p.Prime).pos)
  have hdne : d ≠ 0 := Nat.ne_of_gt hdpos
  have hQnatDegree : Q.natDegree = d := by
    simpa only [Q, d] using
      padicCompletedPrimitivePolynomialInteger_natDegree p n
  have hQmonic : Q.Monic := by
    simpa only [Q] using
      padicCompletedPrimitivePolynomialInteger_monic p n
  have hQeisenstein : Q.IsEisensteinAt 𝔭 := by
    simpa only [Q, 𝔭, base] using
      padicCompletedPrimitivePolynomialInteger_isEisensteinAt p n
  have hdegree : degree base.toDVF target.toDVF = d := by
    change Module.finrank A E = d
    calc
      Module.finrank A E =
          (padicCompletedPrimitivePowerBasis p n).dim :=
        PowerBasis.finrank (padicCompletedPrimitivePowerBasis p n)
      _ =
          (minpoly A
            (padicCompletedPrimitivePowerBasis p n).gen).natDegree :=
        (padicCompletedPrimitivePowerBasis p n).natDegree_minpoly.symm
      _ =
          (padicCompletedPrimitivePolynomial p n).natDegree := by
        rw [padicCompletedPrimitivePowerBasis_gen,
          padicCompletedPrimitiveRoot_minpoly]
      _ = d := by
        simpa only [d] using
          padicCompletedPrimitivePolynomial_natDegree p n
  have hfund : d = e * f := by
    calc
      d = degree base.toDVF target.toDVF := hdegree.symm
      _ = e * f := by
        simpa only [e, f] using
          degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable
            base target
  have he_ne : e ≠ 0 := by
    intro he
    apply hdne
    rw [hfund, he, zero_mul]
  have hf_ne : f ≠ 0 := by
    intro hf
    apply hdne
    rw [hfund, hf, mul_zero]
  have hele : e ≤ d := by
    rw [hfund]
    exact Nat.le_mul_of_pos_right e (Nat.pos_of_ne_zero hf_ne)
  have hRcoeff (i : ℕ) : R.coeff i ∈ 𝔭 := by
    rcases lt_trichotomy i d with hi | hi | hi
    · have hQi : Q.coeff i ∈ 𝔭 := by
        apply hQeisenstein.mem
        rwa [hQnatDegree]
      change (Q - Polynomial.X ^ d).coeff i ∈ 𝔭
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        ite_eq_right (ne_of_lt hi), sub_zero]
      exact hQi
    · subst i
      have hQd : Q.coeff d = 1 := by
        rw [← hQnatDegree]
        exact hQmonic.coeff_natDegree
      change (Q - Polynomial.X ^ d).coeff d ∈ 𝔭
      rw [Polynomial.coeff_sub, hQd, Polynomial.coeff_X_pow,
        ite_eq_left rfl, sub_self]
      exact 𝔭.zero_mem
    · have hQi : Q.coeff i = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rwa [hQnatDegree]
      change (Q - Polynomial.X ^ d).coeff i ∈ 𝔭
      rw [Polynomial.coeff_sub, hQi, Polynomial.coeff_X_pow,
        ite_eq_right (ne_of_gt hi), sub_zero]
      exact 𝔭.zero_mem
  have hR_eval_mem_map :
      R.eval₂ j root ∈ Ideal.map j 𝔭 :=
    completedPolynomial_eval₂_mem_ideal_of_coeff_mem
      j (Ideal.map j 𝔭) R root
      (fun i => Ideal.mem_map_of_mem j (hRcoeff i))
  have hmap :
      Ideal.map j 𝔭 = 𝔓 ^ e := by
    simpa only [j, 𝔭, 𝔓, e] using
      maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex
        base target
  have hR_eval_mem_pow : R.eval₂ j root ∈ 𝔓 ^ e := by
    rw [← hmap]
    exact hR_eval_mem_map
  have hroot : Q.eval₂ j root = 0 := by
    simpa only [Polynomial.aeval_def, Q, j, root, base, target,
      integerMap] using
      padicCompletedPrimitiveRootInteger_aeval p n
  have hQdecomp : Q = Polynomial.X ^ d + R := by
    calc
      Q = (Q - Polynomial.X ^ d) + Polynomial.X ^ d :=
        (sub_add_cancel Q (Polynomial.X ^ d)).symm
      _ = Polynomial.X ^ d + R := by rw [add_comm]
  have hrootDecomp : root ^ d + R.eval₂ j root = 0 := by
    rw [hQdecomp, Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_X] at hroot
    exact hroot
  have hrootMem : root ∈ 𝔓 := by
    simpa only [root, 𝔓, target] using
      padicCompletedPrimitiveRootInteger_mem_maximalIdeal p n
  have hdivCoeff (i : ℕ) : R.divX.coeff i ∈ 𝔭 := by
    rw [Polynomial.coeff_divX]
    exact hRcoeff (i + 1)
  let tail := R.divX.eval₂ j root
  have htail_mem_map : tail ∈ Ideal.map j 𝔭 :=
    completedPolynomial_eval₂_mem_ideal_of_coeff_mem
      j (Ideal.map j 𝔭) R.divX root
      (fun i => Ideal.mem_map_of_mem j (hdivCoeff i))
  have htail_mem_pow : tail ∈ 𝔓 ^ e := by
    rw [← hmap]
    exact htail_mem_map
  have hrootTailMem : root * tail ∈ 𝔓 ^ (e + 1) := by
    rw [pow_succ]
    have hmul : tail * root ∈ 𝔓 ^ e * 𝔓 :=
      Ideal.mul_mem_mul htail_mem_pow hrootMem
    rwa [mul_comm tail root] at hmul
  have hRcoeffZero : R.coeff 0 = πA := by
    change
      (padicCompletedPrimitivePolynomialInteger p n -
        Polynomial.X ^ d).coeff 0 = πA
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      ite_eq_right hdne.symm, sub_zero,
      padicCompletedPrimitivePolynomialInteger, Polynomial.coeff_map]
    exact congrArg (padicCompletedUnramifiedIntegerMap p)
      (standardLubinTatePrimitivePolynomial_coeff_zero (padicLocalField p) π n)
  have hπA :
      base.valuation.IsUniformizer
        (πA : padicCompletedUnramifiedField p) := by
    simpa only [base, π, πA] using
      padicCompletedUnramifiedIntegerMap_isUniformizer p
  have hπAIrreducible : Irreducible πA := by
    exact
      (IsDiscreteValuationRing.irreducible_iff_uniformizer πA).2
        (base.maximalIdeal_eq_span_uniformizer hπA)
  have hconst :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (j (R.coeff 0)) = (e : ℕ∞) := by
    rw [hRcoeffZero,
      addVal_integerMap_eq_ramificationIndex_nsmul base target πA,
      IsDiscreteValuationRing.addVal_uniformizer hπAIrreducible]
    simp only [e, nsmul_eq_mul, mul_one]
  have hR_eval :
      R.eval₂ j root = j (R.coeff 0) + root * tail := by
    have h :=
      congrArg (Polynomial.eval₂ j root)
        (Polynomial.X_mul_divX_add R)
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at h
    calc
      R.eval₂ j root = root * tail + j (R.coeff 0) := by
        simpa only [tail] using h.symm
      _ = j (R.coeff 0) + root * tail := add_comm _ _
  have htailVal :
      ((e + 1 : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal target.valuationSubring
          (root * tail) :=
    (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge
      (root * tail) (e + 1)).1 hrootTailMem
  have heCastLt :
      (e : ℕ∞) <
        IsDiscreteValuationRing.addVal target.valuationSubring
          (root * tail) := by
    exact
      (show (e : ℕ∞) < ((e + 1 : ℕ) : ℕ∞) by
        exact_mod_cast Nat.lt_succ_self e).trans_le htailVal
  have hdistinct :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (j (R.coeff 0)) ≠
        IsDiscreteValuationRing.addVal target.valuationSubring
          (root * tail) := by
    rw [hconst]
    exact ne_of_lt heCastLt
  have hRval :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (R.eval₂ j root) = (e : ℕ∞) := by
    rw [hR_eval,
      (IsDiscreteValuationRing.addVal
        target.valuationSubring).map_add_of_distinct_val hdistinct,
      hconst, min_eq_left]
    exact heCastLt.le
  have hpowEq : root ^ d = -(R.eval₂ j root) :=
    eq_neg_of_add_eq_zero_left hrootDecomp
  have hmul :
      (d : ℕ∞) *
          IsDiscreteValuationRing.addVal target.valuationSubring root =
        (e : ℕ∞) := by
    calc
      (d : ℕ∞) *
          IsDiscreteValuationRing.addVal target.valuationSubring root =
          d • IsDiscreteValuationRing.addVal
            target.valuationSubring root := by rw [nsmul_eq_mul]
      _ = IsDiscreteValuationRing.addVal target.valuationSubring
          (root ^ d) := by
        symm
        exact IsDiscreteValuationRing.addVal_pow root d
      _ = IsDiscreteValuationRing.addVal target.valuationSubring
          (-(R.eval₂ j root)) := by rw [hpowEq]
      _ = IsDiscreteValuationRing.addVal target.valuationSubring
          (R.eval₂ j root) :=
        (IsDiscreteValuationRing.addVal target.valuationSubring).map_neg _
      _ = (e : ℕ∞) := hRval
  have honele :
      1 ≤ IsDiscreteValuationRing.addVal
        target.valuationSubring root := by
    simpa using
      (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge
        root 1).1
        (by simpa only [pow_one] using hrootMem)
  have hdcoe : (d : ℕ∞) ≠ 0 := by
    exact_mod_cast hdne
  have hmul_le :
      (d : ℕ∞) *
          IsDiscreteValuationRing.addVal target.valuationSubring root ≤
        (d : ℕ∞) * 1 := by
    rw [hmul]
    have hcast : (e : ℕ∞) ≤ (d : ℕ∞) := by
      exact_mod_cast hele
    simpa using hcast
  have hvle :
      IsDiscreteValuationRing.addVal target.valuationSubring root ≤ 1 :=
    (ENat.mul_le_mul_left_iff hdcoe (ENat.natCast_ne_top d)).1 hmul_le
  have hrootVal :
      IsDiscreteValuationRing.addVal target.valuationSubring root = 1 :=
    le_antisymm hvle honele
  have hed : e = d := by
    rw [hrootVal, mul_one] at hmul
    exact_mod_cast hmul.symm
  have heramDegree :
      ramificationIndex
          (padicCompletedUnramifiedCompleteDVF p).toDVF
          (padicCompletedLevelCompleteDVF p n).toDVF =
        degree
          (padicCompletedUnramifiedCompleteDVF p).toDVF
          (padicCompletedLevelCompleteDVF p n).toDVF := by
    simpa only [base, target, e] using hed.trans hdegree.symm
  exact ⟨hrootVal, heramDegree⟩

/-- The completed multiplicative Lubin--Tate level is totally ramified over
the completed-unramified coefficient field. -/
theorem padicCompletedLevel_ramificationIndex_eq_degree
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ramificationIndex
        (padicCompletedUnramifiedCompleteDVF p).toDVF
        (padicCompletedLevelCompleteDVF p n).toDVF =
      degree
        (padicCompletedUnramifiedCompleteDVF p).toDVF
        (padicCompletedLevelCompleteDVF p n).toDVF :=
  (padicCompletedPrimitiveRootInteger_addVal_and_ramificationIndex
    p n).2

theorem
    padicChangedUniformizerThetaValue_addVal_and_ramificationIndex
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsDiscreteValuationRing.addVal
        (padicCompletedLevelCompleteDVF p n).valuationSubring
        (padicChangedUniformizerThetaValue p u n) = 1 ∧
      ramificationIndex
          (padicCompletedUnramifiedCompleteDVF p).toDVF
          (padicCompletedLevelCompleteDVF p n).toDVF =
        (p - 1) * p ^ n := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let Q := padicChangedCompletedPrimitivePolynomialInteger p u n
  let d := (p - 1) * p ^ n
  let e := ramificationIndex base.toDVF target.toDVF
  let 𝔭 := base.maximalIdeal
  let 𝔓 := target.maximalIdeal
  let j := integerMap base.toDVF target.toDVF
  let θ := padicChangedUniformizerThetaValue p u n
  let R := Q - Polynomial.X ^ d
  let π := padicIntEquivValuationSubring p (p : ℤ_[p])
  let πu :=
    standardLubinTateChangedUniformizer
      (padicLocalField p) π u
  let πuA : base.valuationSubring :=
    padicCompletedUnramifiedIntegerMap p πu
  let : IsScalarTower base.valuationSubring
      target.valuationSubring (padicCompletedLevelField p n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
      (Nat.pow_pos (Fact.out : p.Prime).pos)
  have hdne : d ≠ 0 := Nat.ne_of_gt hdpos
  have hQnatDegree : Q.natDegree = d := by
    simpa only [Q, d] using
      padicChangedCompletedPrimitivePolynomialInteger_natDegree p u n
  have hQmonic : Q.Monic := by
    simpa only [Q] using
      padicChangedCompletedPrimitivePolynomialInteger_monic p u n
  have hQeisenstein : Q.IsEisensteinAt 𝔭 := by
    simpa only [Q, 𝔭, base] using
      padicChangedCompletedPrimitivePolynomialInteger_isEisensteinAt
        p u n
  have hdegree :
      degree base.toDVF target.toDVF = d := by
    let pb := padicCompletedPrimitivePowerBasis p n
    change Module.finrank
      (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) = d
    calc
      Module.finrank
          (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) =
          pb.dim :=
        PowerBasis.finrank pb
      _ =
          (minpoly (padicCompletedUnramifiedField p) pb.gen).natDegree :=
        pb.natDegree_minpoly.symm
      _ =
          (padicCompletedPrimitivePolynomial p n).natDegree := by
        rw [padicCompletedPrimitivePowerBasis_gen,
          padicCompletedPrimitiveRoot_minpoly]
      _ = d := by
        simpa only [d] using
          padicCompletedPrimitivePolynomial_natDegree p n
  have hed : e = d := by
    calc
      e =
          degree
            (padicCompletedUnramifiedCompleteDVF p).toDVF
            (padicCompletedLevelCompleteDVF p n).toDVF := by
        simpa only [e, base, target] using
          padicCompletedLevel_ramificationIndex_eq_degree p n
      _ = d := by simpa only [base, target] using hdegree
  have hRcoeff (i : ℕ) : R.coeff i ∈ 𝔭 := by
    rcases lt_trichotomy i d with hi | hi | hi
    · have hQi : Q.coeff i ∈ 𝔭 := by
        apply hQeisenstein.mem
        rwa [hQnatDegree]
      change (Q - Polynomial.X ^ d).coeff i ∈ 𝔭
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        ite_eq_right (ne_of_lt hi), sub_zero]
      exact hQi
    · subst i
      have hQd : Q.coeff d = 1 := by
        rw [← hQnatDegree]
        exact hQmonic.coeff_natDegree
      change (Q - Polynomial.X ^ d).coeff d ∈ 𝔭
      rw [Polynomial.coeff_sub, hQd, Polynomial.coeff_X_pow,
        ite_eq_left rfl, sub_self]
      exact 𝔭.zero_mem
    · have hQi : Q.coeff i = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rwa [hQnatDegree]
      change (Q - Polynomial.X ^ d).coeff i ∈ 𝔭
      rw [Polynomial.coeff_sub, hQi, Polynomial.coeff_X_pow,
        ite_eq_right (ne_of_gt hi), sub_zero]
      exact 𝔭.zero_mem
  have hmap :
      Ideal.map j 𝔭 = 𝔓 ^ e := by
    simpa only [j, 𝔭, 𝔓, e] using
      maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex
        base target
  have hθmem : θ ∈ 𝔓 := by
    have hadic : IsAdic 𝔓 := rfl
    have h𝔓nhds :
        ((𝔓 : Ideal target.valuationSubring) :
          Set target.valuationSubring) ∈
            𝓝 (0 : target.valuationSubring) := by
      simpa only [pow_one] using
        (hadic.hasBasis_nhds_zero.mem_of_mem (i := 1) trivial)
    have hThetaEval :=
      padicChangedUniformizerThetaValue_hasEval p u n
    obtain ⟨m, hm⟩ :=
      hThetaEval.exists_pow_mem_of_mem_nhds h𝔓nhds
    exact
      (IsLocalRing.maximalIdeal.isMaximal
        target.valuationSubring).isPrime.mem_of_pow_mem m hm
  have hcomp :
      j.comp (padicCompletedUnramifiedIntegerMap p) =
        padicCompletedLevelPadicIntegerCoefficientHom p n := by
    ext z
    rw [RingHom.comp_apply, integerMap_apply,
      padicCompletedUnramifiedIntegerMap_coe,
      padicCompletedLevelPadicIntegerCoefficientHom_coe]
    rfl
  have hroot : Q.eval₂ j θ = 0 := by
    have h :=
      padicChangedUniformizerThetaValue_isRoot p u n
    rw [Polynomial.IsRoot, Polynomial.eval_map] at h
    change
      Polynomial.eval₂ j θ
          ((standardLubinTatePrimitivePolynomial
            (padicLocalField p) πu n).map
              (padicCompletedUnramifiedIntegerMap p)) =
        0
    rw [Polynomial.eval₂_map, hcomp]
    simpa only [πu] using h
  have hQdecomp : Q = Polynomial.X ^ d + R := by
    calc
      Q = (Q - Polynomial.X ^ d) + Polynomial.X ^ d :=
        (sub_add_cancel Q (Polynomial.X ^ d)).symm
      _ = Polynomial.X ^ d + R := by rw [add_comm]
  have hrootDecomp : θ ^ d + R.eval₂ j θ = 0 := by
    rw [hQdecomp, Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_X] at hroot
    exact hroot
  have hdivCoeff (i : ℕ) : R.divX.coeff i ∈ 𝔭 := by
    rw [Polynomial.coeff_divX]
    exact hRcoeff (i + 1)
  let tail := R.divX.eval₂ j θ
  have htail_mem_map : tail ∈ Ideal.map j 𝔭 :=
    completedPolynomial_eval₂_mem_ideal_of_coeff_mem
      j (Ideal.map j 𝔭) R.divX θ
      (fun i => Ideal.mem_map_of_mem j (hdivCoeff i))
  have htail_mem_pow : tail ∈ 𝔓 ^ e := by
    rw [← hmap]
    exact htail_mem_map
  have hθtail_mem : θ * tail ∈ 𝔓 ^ (e + 1) := by
    rw [pow_succ]
    have hmul : tail * θ ∈ 𝔓 ^ e * 𝔓 :=
      Ideal.mul_mem_mul htail_mem_pow hθmem
    rwa [mul_comm tail θ] at hmul
  have hRcoeffZero : R.coeff 0 = πuA := by
    change
      (padicChangedCompletedPrimitivePolynomialInteger p u n -
        Polynomial.X ^ d).coeff 0 = πuA
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      ite_eq_right hdne.symm, sub_zero,
      padicChangedCompletedPrimitivePolynomialInteger, Polynomial.coeff_map]
    exact congrArg (padicCompletedUnramifiedIntegerMap p)
      (standardLubinTatePrimitivePolynomial_coeff_zero
        (padicLocalField p) πu n)
  have hπuA :
      base.valuation.IsUniformizer
        (πuA : padicCompletedUnramifiedField p) := by
    simpa only [base, π, πu, πuA] using
      padicChangedCompletedUniformizer_isUniformizer p u
  have hπuAIrreducible : Irreducible πuA := by
    exact
      (IsDiscreteValuationRing.irreducible_iff_uniformizer πuA).2
        (base.maximalIdeal_eq_span_uniformizer hπuA)
  have hconst :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (j (R.coeff 0)) = (e : ℕ∞) := by
    rw [hRcoeffZero,
      addVal_integerMap_eq_ramificationIndex_nsmul base target πuA,
      IsDiscreteValuationRing.addVal_uniformizer hπuAIrreducible]
    simp only [e, nsmul_eq_mul, mul_one]
  have hR_eval :
      R.eval₂ j θ = j (R.coeff 0) + θ * tail := by
    have h :=
      congrArg (Polynomial.eval₂ j θ)
        (Polynomial.X_mul_divX_add R)
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at h
    calc
      R.eval₂ j θ = θ * tail + j (R.coeff 0) := by
        simpa only [tail] using h.symm
      _ = j (R.coeff 0) + θ * tail := add_comm _ _
  have htailVal :
      ((e + 1 : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal target.valuationSubring
          (θ * tail) :=
    (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge
      (θ * tail) (e + 1)).1 hθtail_mem
  have heCastLt :
      (e : ℕ∞) <
        IsDiscreteValuationRing.addVal target.valuationSubring
          (θ * tail) := by
    exact
      (show (e : ℕ∞) < ((e + 1 : ℕ) : ℕ∞) by
        exact_mod_cast Nat.lt_succ_self e).trans_le htailVal
  have hdistinct :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (j (R.coeff 0)) ≠
        IsDiscreteValuationRing.addVal target.valuationSubring
          (θ * tail) := by
    rw [hconst]
    exact ne_of_lt heCastLt
  have hRval :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (R.eval₂ j θ) = (e : ℕ∞) := by
    rw [hR_eval,
      (IsDiscreteValuationRing.addVal
        target.valuationSubring).map_add_of_distinct_val hdistinct,
      hconst, min_eq_left]
    exact heCastLt.le
  have hpowEq : θ ^ d = -(R.eval₂ j θ) :=
    eq_neg_of_add_eq_zero_left hrootDecomp
  have hmul :
      (d : ℕ∞) *
          IsDiscreteValuationRing.addVal target.valuationSubring θ =
        (e : ℕ∞) := by
    calc
      (d : ℕ∞) *
          IsDiscreteValuationRing.addVal target.valuationSubring θ =
          d • IsDiscreteValuationRing.addVal
            target.valuationSubring θ := by rw [nsmul_eq_mul]
      _ = IsDiscreteValuationRing.addVal target.valuationSubring
          (θ ^ d) := by
        symm
        exact IsDiscreteValuationRing.addVal_pow θ d
      _ = IsDiscreteValuationRing.addVal target.valuationSubring
          (-(R.eval₂ j θ)) := by rw [hpowEq]
      _ = IsDiscreteValuationRing.addVal target.valuationSubring
          (R.eval₂ j θ) :=
        (IsDiscreteValuationRing.addVal target.valuationSubring).map_neg _
      _ = (e : ℕ∞) := hRval
  have honele :
      1 ≤ IsDiscreteValuationRing.addVal
        target.valuationSubring θ := by
    simpa using
      (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge
        θ 1).1
        (by simpa only [pow_one] using hθmem)
  have hdcoe : (d : ℕ∞) ≠ 0 := by
    exact_mod_cast hdne
  have hmul_le :
      (d : ℕ∞) *
          IsDiscreteValuationRing.addVal target.valuationSubring θ ≤
        (d : ℕ∞) * 1 := by
    rw [hmul, hed, mul_one]
  have hvle :
      IsDiscreteValuationRing.addVal target.valuationSubring θ ≤ 1 :=
    (ENat.mul_le_mul_left_iff hdcoe (ENat.natCast_ne_top d)).1 hmul_le
  have hθval :
      IsDiscreteValuationRing.addVal target.valuationSubring θ = 1 :=
    le_antisymm hvle honele
  exact ⟨hθval, hed⟩

/-- The genuine changed-uniformizer theta point has normalized additive
valuation one in the completed standard level. -/
theorem padicChangedUniformizerThetaValue_addVal
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsDiscreteValuationRing.addVal
        (padicCompletedLevelCompleteDVF p n).valuationSubring
        (padicChangedUniformizerThetaValue p u n) = 1 :=
  (padicChangedUniformizerThetaValue_addVal_and_ramificationIndex
    p u n).1

/-- The genuine changed-uniformizer theta point is a uniformizer of the
completed standard level. -/
theorem padicChangedUniformizerThetaValue_isUniformizer
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicCompletedLevelCompleteDVF p n).valuation.IsUniformizer
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) := by
  let target := padicCompletedLevelCompleteDVF p n
  let θ := padicChangedUniformizerThetaValue p u n
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible target.valuationSubring
  have hval :
      IsDiscreteValuationRing.addVal target.valuationSubring θ =
        IsDiscreteValuationRing.addVal target.valuationSubring ϖ := by
    rw [padicChangedUniformizerThetaValue_addVal,
      IsDiscreteValuationRing.addVal_uniformizer hϖ]
  have hθirreducible : Irreducible θ :=
    ((IsDiscreteValuationRing.addVal_eq_iff_associated θ ϖ).1
      hval).symm.irreducible hϖ
  exact Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := target.valuation) hθirreducible.maximalIdeal_eq

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedChangedStandardResidue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsNonarchimedeanLocalField _root_.chosenFinitePlaceBaseValuativeRel _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Residue embedding for the completed standard/changed compositum

The finite standard/changed compositum is realized inside the completed
Lubin--Tate level.  Uniqueness of the finite extension of the p-adic
valuation therefore gives a canonical injection from its residue field into
the residue field of the ambient completed level.

This injection is the faithful comparison map used to identify the finite
relative Artin candidate with inverse arithmetic Frobenius.
-/

noncomputable section

namespace LubinTate

open scoped ValuativeRel

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The changed fixed field carries its canonical finite-extension spectral
norm. -/
noncomputable instance
    padicCompletedChangedUniformizerFixedField_nontriviallyNormedField
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    NontriviallyNormedField
      (padicCompletedChangedUniformizerFixedField p u n) :=
  finiteExtensionSpectralNormedField ℚ_[p]
    (padicCompletedChangedUniformizerFixedField p u n)

/-- The changed fixed field has the canonical valuative relation induced by
its finite p-adic spectral norm. -/
noncomputable instance
    padicCompletedChangedUniformizerFixedField_valuativeRel
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    ValuativeRel
      (padicCompletedChangedUniformizerFixedField p u n) :=
  finiteExtensionSpectralValuativeRel ℚ_[p]
    (padicCompletedChangedUniformizerFixedField p u n)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedResidueFrobenius
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedChangedUniformizerFixedField_finiteDimensional _root_.LubinTate.padicCompletedChangedUniformizerFixedField_isAbelianGalois _root_.LubinTate.padicCompletedChangedUniformizerFixedField_nontriviallyNormedField _root_.LubinTate.padicCompletedChangedUniformizerFixedField_valuativeRel _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldAlgebra _root_.LubinTate.padicCompletedStandardChangedCompositum_changedFieldScalarTower _root_.LubinTate.padicCompletedStandardChangedCompositum_finiteDimensional _root_.LubinTate.padicCompletedStandardChangedCompositum_isAbelianGalois _root_.LubinTate.padicCompletedStandardLevelField_finiteDimensional _root_.LubinTate.padicCompletedStandardLevelField_isAbelianGalois _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFieldGalEquivZHat_fullRestriction _root_.GlobalClassFieldTheory.Reciprocity.rationalPrimeUnitValuationSubringUnit_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.zHatUnitsDecomposition_freeCoordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.padicChangedUniformizerLevelEquivCompletedFixedField_apply_generator _root_.LubinTate.padicChangedUniformizerLevelToCompletedFixedField_apply_gen _root_.LubinTate.padicCompletedChangedUniformizerArtinCandidate_fixedField _root_.LubinTate.padicCompletedChangedUniformizerArtinCandidate_standardLevel _root_.LubinTate.padicCompletedChangedUniformizerFrobeniusAlgEquiv_apply _root_.LubinTate.padicCompletedChangedUniformizerRelativeArtinCandidate_apply _root_.LubinTate.padicCompletedStandardPrimitivePointUnitAction_eq_unitParameterRoot _root_.LubinTate.padicStandardLevelIntegerEmbedding_apply_primitivePoint _root_.LubinTate.padicStandardLevelIntegerEmbedding_apply_primitivePointUnitAction _root_.LubinTate.padicStandardLevelIntegerEmbedding_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteResidueActionOfHenselianDVF_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Residue Frobenius on completed p-adic Lubin--Tate levels

The completed multiplicative Lubin--Tate level is totally ramified over its
completed-unramified coefficient field.  Hence the canonical residue map is
an isomorphism.  Under this identification, every unit-indexed completed
Frobenius lift induces the arithmetic Frobenius `x ↦ x ^ p` on the residue
field.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ResidueField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The completed multiplicative level has residue degree one over the
completed-unramified coefficient field. -/
theorem padicCompletedLevel_residueDegree_eq_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    residueDegree
        (padicCompletedUnramifiedCompleteDVF p).toDVF
        (padicCompletedLevelCompleteDVF p n).toDVF = 1 := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let E := padicCompletedLevelField p n
  let : IsScalarTower base.valuationSubring
      target.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact
    (residueDegree_eq_one_iff_ramificationIndex_eq_degree_of_finite_separable
      base target).2
      (by
        simpa only [base, target] using
          padicCompletedLevel_ramificationIndex_eq_degree p n)

/-- The target residue field has linear rank one over the
completed-unramified residue field. -/
theorem padicCompletedLevel_residueField_finrank_eq_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Module.finrank
        (padicCompletedUnramifiedCompleteDVF p).residueField
        (padicCompletedLevelCompleteDVF p n).residueField = 1 := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let E := padicCompletedLevelField p n
  let : IsScalarTower base.valuationSubring
      target.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : target.maximalIdeal.LiesOver base.maximalIdeal :=
    maximalIdeal_liesOver base target
  have hfinrank :
      residueDegree base.toDVF target.toDVF =
        Module.finrank base.residueField target.residueField := by
    rw [residueDegree_eq_finrank_quotient base target]
    rfl
  change Module.finrank base.residueField target.residueField = 1
  calc
    Module.finrank base.residueField target.residueField =
        residueDegree base.toDVF target.toDVF :=
      hfinrank.symm
    _ = 1 := by
      simpa only [base, target] using
        padicCompletedLevel_residueDegree_eq_one p n

/-- The canonical residue map from the completed-unramified coefficient
field onto the completed level is surjective. -/
theorem padicCompletedLevel_residueMap_surjective
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Function.Surjective
      (residueMap
        (padicCompletedUnramifiedCompleteDVF p).toDVF
        (padicCompletedLevelCompleteDVF p n).toDVF) := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  have hbijective :
      Function.Bijective
        (algebraMap base.residueField target.residueField) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap).1
      (by
        simpa only [base, target] using
          padicCompletedLevel_residueField_finrank_eq_one p n)
  exact hbijective.2

/-- The canonical residue-field equivalence from the completed-unramified
coefficient field to a completed multiplicative level. -/
noncomputable def padicCompletedLevelResidueFieldEquiv
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedUnramifiedCompleteDVF p).residueField ≃+*
      (padicCompletedLevelCompleteDVF p n).residueField :=
  residueFieldEquivOfSurjective
    (padicCompletedUnramifiedCompleteDVF p).toDVF
    (padicCompletedLevelCompleteDVF p n).toDVF
    (padicCompletedLevel_residueMap_surjective p n)

/-- The completed-level residue equivalence evaluates by the canonical
residue map. -/
@[simp]
theorem padicCompletedLevelResidueFieldEquiv_apply
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedUnramifiedCompleteDVF p).residueField) :
    padicCompletedLevelResidueFieldEquiv p n x =
      residueMap
        (padicCompletedUnramifiedCompleteDVF p).toDVF
        (padicCompletedLevelCompleteDVF p n).toDVF x :=
  rfl

/-- On integral representatives, the completed-level residue equivalence is
the residue of the canonical valuation-ring inclusion. -/
@[simp]
theorem padicCompletedLevelResidueFieldEquiv_apply_residue
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : (padicCompletedUnramifiedCompleteDVF p).valuationSubring) :
    padicCompletedLevelResidueFieldEquiv p n
        ((padicCompletedUnramifiedCompleteDVF p).residueMap a) =
      (padicCompletedLevelCompleteDVF p n).residueMap
        (integerMap
          (padicCompletedUnramifiedCompleteDVF p).toDVF
          (padicCompletedLevelCompleteDVF p n).toDVF a) := by
  exact
    residueFieldEquivOfSurjective_apply_residue
      (padicCompletedUnramifiedCompleteDVF p).toDVF
      (padicCompletedLevelCompleteDVF p n).toDVF
      (padicCompletedLevel_residueMap_surjective p n) a

end LubinTate
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicPrincipalProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul
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
local instance rationalCyclotomicPrincipalProductPrimePowerNumberField_r94cbaf_1
    (p : Nat.Primes) (k : ℕ) :
    NumberField (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
local instance rationalCyclotomicPrincipalProductPrimePowerFiniteDimensional
    (p : Nat.Primes) (k : ℕ) :
    FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

end Reciprocity
end GlobalClassFieldTheory
end
end


