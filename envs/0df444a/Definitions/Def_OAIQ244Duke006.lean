-- Prove2me | Definitions.Def_OAIQ244Duke006
-- name    : OAIQ244Duke006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:11:53.178222+00:00
-- url     : https://prove2.me/theorems/2c7ee0ac-f3c4-441f-864c-3741acc17e86
-- title:
--   Definitions bundle OAIQ244Duke006 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 493 declarations of OpenAI's Lean: 154 definitions, 6 inductive types or structures, 22 instances and 311 theorems. The definitions and types are `FiniteIdeleGroup.intrinsicIntegerEquivValuedInteger`, `FiniteIdeleGroup.intrinsicResidueFieldEquivValuedResidueField`, `FiniteSPlaceFactors`, `HilbertRamification.Dedekind.basePrime`, `LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation`, `LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring`, `LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntResidueFieldEquivZMod`, `LocalFieldTheory.DiscreteValuationField.IwasawaDegree`, `LocalFieldTheory.DiscreteValuationField.IwasawaIndex`, `LocalFieldTheory.DiscreteValuationField.LocalField.coherentWithZeroMultiplicativeIntGroup`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.HasUnitUniformizerDecomposition`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.IsUniformizer`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.UnitUniformizerDecomposition`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.canonicalUnitUniformizerDecomposition`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.expConvergenceAddSubgroupOfWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.expSeriesFieldOfWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.expSeriesPartialSumField`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.expSeriesTerm`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.expSeriesTermField`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusLeftVariableLogSubst`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgument`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgumentBasicFactor`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgumentBasicFactorChoices`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgumentBasicFactorFinset`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgumentBasicFactorLabel`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgumentBasicFactorLabelCount`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgumentBasicFactorLabelCountChoices`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgumentBasicFactorProductChoices`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgumentLeftChoiceCount`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgumentMixedChoiceCount`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgumentRightChoiceCount`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductFormulaDefect`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductRightSide`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusRightVariableLogSubst`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.logOnePlusPartialSumField`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.logOnePlusSeriesFieldOfWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.logSeriesTermField`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.ofWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.quotientZeroSubgroupEquivValueSubgroup` and 120 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Adele_FiniteRestrictedProductBaseChange`, `AlgebraicNumberTheory_Adele_InfinitePlaceTensorBlock`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_FinitePlaceCompletion`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice`, `AlgebraicNumberTheory_Adele_LocalComponents`, `AlgebraicNumberTheory_Adele_RestrictedAction`, `AlgebraicNumberTheory_Completion_ExtensionIndex`, `AlgebraicNumberTheory_Completion_IntegerRingComparison`, `AlgebraicNumberTheory_Idele_BaseChange`, `AlgebraicNumberTheory_Idele_Cohomology_Decomposition`, `AlgebraicNumberTheory_Idele_Extension_NormLocalOrder`, `AlgebraicNumberTheory_NormalClosure`, `AlgebraicNumberTheory_RayClass_Basic`, `AlgebraicNumberTheory_RayClass_FullModulus`, `AlgebraicNumberTheory_RayClass_Ideal`, `AlgebraicNumberTheory_RayClass_Topology`, `AlgebraicNumberTheory_SUnit_GaloisAction`, `LocalField_Analytic_Arithmetic`, `LocalField_Analytic_DenominatorValuation`, `LocalField_Analytic_LogExpSeries_ExpConvergence`, `LocalField_Analytic_LogExpSeries_FormalCoreBase_BasicFactors`, `LocalField_Analytic_LogExpSeries_FormalCoreBase_ChoiceCountSystem`, `LocalField_Analytic_LogExpSeries_FormalCoreBase_ExplicitChoiceCounts`, `LocalField_Analytic_LogExpSeries_FormalCoreBase_ProductArgument`, `LocalField_Analytic_LogExpSeries_FormalProduct`, `LocalField_Analytic_LogExpSeries_Homomorphisms`, `LocalField_Analytic_LogExpSeries_LogConvergence`, `LocalField_Analytic_LogExpSeries_SeriesTerms`, `LocalField_DiscreteValuationField_IwasawaIndexing`, `LocalField_DiscreteValuationField_Norm_Basic`, `LocalField_DiscreteValuationField_Norm_Quotients`, `LocalField_DiscreteValuationField_PadicField`, `LocalField_DiscreteValuationField_ValuationSubringUnits_CyclicValueGroup`, `LocalField_DiscreteValuationField_ValuationSubringUnits_IntegerValuation`, `LocalField_DiscreteValuationField_ValuationSubringUnits_RangeRestriction`, `LocalField_DiscreteValuationField_ValuationSubringUnits_SeriesValuationEstimates`, `LocalField_GroupTheory_IntegerMultipleSubgroup`, `LocalField_NonarchimedeanLocalField_Basic`, `LocalField_NonarchimedeanLocalField_Norm`, `LocalField_NonarchimedeanLocalField_Valuation`, `LocalField_NonarchimedeanLocalField_ValuationExactSequence`, `LocalField_NonarchimedeanLocalField_ValuativeExtension`, `PrimePackets_PacketMoments`, `Ramification_HilbertRamification_Dedekind_Basic`, `Ramification_HilbertRamification_Dedekind_PrimeContractions`, `Valuation_AbsoluteValue_Theory_Core`, `Valuation_AbsoluteValue_Theory_ExponentialValuations`, `Valuation_Completion_FiniteProductNormTrace`, `Valuation_DiscreteValuationField_AdicPower`, `Valuation_DiscreteValuationField_ChevalleyExtension`, `Valuation_DiscreteValuationField_Complete`, `Valuation_DiscreteValuationField_Henselian`, `Valuation_DiscreteValuationField_HenselianFinite`, `Valuation_DiscreteValuationField_IntegralClosure`, `Valuation_HenselLemma`, `Valuation_Topology_AdicCompletionInverseLimit`, `Valuation_Topology_AdicCompletionInverseLimitRing`, `Valuation_Topology_CompatibleInverseLimit`, `Valuation_Topology_Models`, `Valuation_ValuedAdicComplete`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke017`, `OAIQ244Duke018`, `OAIQ244Duke019`, `OAIQ244Duke020`, `OAIQ244Duke021`, `OAIQ244Duke022`, `OAIQ244Duke023` and `OAIQ244Duke024`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Hom.Basic
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
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
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
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
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
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.Gershgorin
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
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.RingHoms
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
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Filtration
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
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.SimpleModule.Basic
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
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
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
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.WithTopology

section
-- module Solutions.OAIQ244_DUKE.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_LocalComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Joint local components of relative adeles and ideles

The archimedean and finite tensor components jointly determine an element
of `𝔸_K ⊗[K] L`.  This file records the corresponding injective
homomorphism on relative ideles.  Surjectivity onto the restricted local
product is handled separately, once integral compatibility with the local
tensor decomposition has been established.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The unrestricted family of every archimedean and finite local
tensor unit group. -/
abbrev RelativeLocalTensorFamily :=
  (∀ w : InfinitePlace K,
      (w.Completion ⊗[K] L)ˣ) ×
    (∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ)
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Basic structure of nonarchimedean local fields

Compactness facts and the normalized integer-valued valuation attached to a
nonarchimedean local field.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- The normalized integer valuation attached to a nonarchimedean local field.

It is obtained by transporting the value group to `WithZero (Multiplicative Int)` and then taking
the exponent of the nonzero value of a field unit. -/
noncomputable def v (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Additive Kˣ → Int :=
  fun x =>
    Multiplicative.toAdd
      (WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K ((Additive.toMul x : Kˣ) : K)))
        (by simp))

/-- The normalized integer valuation is obtained by transporting the field valuation to
multiplicative integers and taking its additive exponent. -/
@[simp]
theorem v_apply (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Additive Kˣ) :
    v K x =
      Multiplicative.toAdd
        (WithZero.unzero
          (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
            (ValuativeRel.valuation K ((Additive.toMul x : Kˣ) : K)))
          (by simp)) :=
  rfl

/-- The normalized valuation turns multiplication of field units into addition of integers. -/
theorem v_mul (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    v K (Additive.ofMul (x * y)) =
      v K (Additive.ofMul x) + v K (Additive.ofMul y) := by
  simp [v, Valuation.map_mul, WithZero.unzero_mul, toAdd_mul]

/-- The normalized valuation of the multiplicative identity is zero. -/
@[simp]
theorem v_one (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    v K (Additive.ofMul (1 : Kˣ)) = 0 := by
  dsimp [v]
  have hunzero :
      WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K (((1 : Kˣ) : K))))
        (by simp) = (1 : Multiplicative Int) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero]
    simp
  rw [hunzero]
  exact toAdd_one

/-- The normalized valuation of an inverse is the negative of the original valuation. -/
theorem v_inv (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) :
    v K (Additive.ofMul x⁻¹) = -v K (Additive.ofMul x) := by
  have hmul := v_mul K x x⁻¹
  rw [mul_inv_cancel, v_one] at hmul
  omega

/-- The normalized valuation of a quotient is the difference of the two valuations. -/
theorem v_div (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    v K (Additive.ofMul (x / y)) =
      v K (Additive.ofMul x) - v K (Additive.ofMul y) := by
  rw [div_eq_mul_inv, v_mul, v_inv, sub_eq_add_neg]

/-- Raising a field unit to a natural power multiplies its normalized valuation by that power. -/
theorem v_pow (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Nat) :
    v K (Additive.ofMul (x ^ n)) = (n : Int) * v K (Additive.ofMul x) := by
  induction n with
  | zero =>
      rw [pow_zero, v_one]
      simp
  | succ n ih =>
      rw [pow_succ, v_mul, ih]
      rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 by simp]
      ring

/-- Raising a field unit to an integral power multiplies its normalized valuation by that integer.
Raising a field unit to an integral power multiplies its normalized valuation by that integer. -/
theorem v_zpow (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Int) :
    v K (Additive.ofMul (x ^ n)) = n * v K (Additive.ofMul x) := by
  cases n with
  | ofNat n =>
      simpa using v_pow K x n
  | negSucc n =>
      rw [zpow_negSucc, v_inv, v_pow]
      change -(((n + 1 : Nat) : Int) * v K (Additive.ofMul x)) =
        (-(((n + 1 : Nat) : Int))) * v K (Additive.ofMul x)
      ring

/-- The canonical inclusion of valuation-integer units into field units. -/
def integerUnitsToFieldUnits (K : Type u) [Field K] [ValuativeRel K] : 𝒪[K]ˣ →* Kˣ :=
  Units.map (algebraMap 𝒪[K] K).toMonoidHom

/-- The inclusion of valuation-ring units into field units preserves the underlying field element.
The inclusion of valuation-ring units into field units preserves the underlying field element. -/
@[simp]
theorem integerUnitsToFieldUnits_apply (K : Type u) [Field K] [ValuativeRel K]
    (x : 𝒪[K]ˣ) :
    ((integerUnitsToFieldUnits K x : Kˣ) : K) = (((x : 𝒪[K]ˣ) : 𝒪[K]) : K) :=
  rfl

/-- A valuation-integer unit has normalized valuation zero as a field unit. -/
@[simp]
theorem v_integerUnitsToFieldUnits (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : 𝒪[K]ˣ) :
    v K (Additive.ofMul (integerUnitsToFieldUnits K x)) = 0 := by
  have hxv :
      ValuativeRel.valuation K ((integerUnitsToFieldUnits K x : Kˣ) : K) = 1 := by
    simpa [integerUnitsToFieldUnits] using
      (Valuation.Integers.valuation_unit
        (Valuation.integer.integers (ValuativeRel.valuation K)) x)
  rw [v_apply]
  apply (WithZero.toAdd_unzero_eq_iff _ 0).2
  change
    (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
        (ValuativeRel.valuation K
          ((integerUnitsToFieldUnits K x : Kˣ) : K)) =
      ((Multiplicative.ofAdd (0 : Int) : Multiplicative Int) :
        WithZero (Multiplicative Int))
  rw [hxv, map_one]
  rfl

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ValuativeExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Valuative extensions

Records when the valuation ring of an extension field is integral over the
base valuation ring, the hypothesis needed to restrict field norms integrally.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u v

open scoped ValuativeRel

/-- A valued extension whose valuation integer ring in `L` is integral over the base integer ring.

This is the algebraic input used to restrict field norms to valuation integer rings. -/
class ValuativeExtension (K : Type u) (L : Type v) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L] : Prop where
  /-- Every target valuation integer is integral over the base valuation
  integers. -/
  integer_isIntegral : ∀ x : 𝒪[L], IsIntegral 𝒪[K] (x : L)

/-- An integral-closure identification of valuation rings makes the target valuation an extension of
the base valuation. -/
instance valuativeExtensionOfIsIntegralClosure
    (K : Type u) (L : Type v) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    ValuativeExtension K L where
  integer_isIntegral x :=
    (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).2 ⟨x, rfl⟩

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_Norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Norms in valued field extensions

Packages field norms as homomorphisms on units and restricts them to valuation
rings and their unit groups under the appropriate integral hypotheses.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u v

namespace IsNonarchimedeanLocalField

open scoped BigOperators ValuativeRel

variable {K : Type u} {L : Type v}

section UnitNorm

variable [Field K] [Field L] [Algebra K L]

/-- Base units embedded in an extension. -/
def mapBaseUnitsToExtensionUnits
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Kˣ →* Lˣ :=
  Units.map (algebraMap K L).toMonoidHom


/-- The inclusion of base-field units into extension-field units agrees with the algebra map on
underlying elements. -/
@[simp]
lemma mapBaseUnitsToExtensionUnits_apply_coe (x : Kˣ) :
    ((mapBaseUnitsToExtensionUnits K L x : Lˣ) : L) = algebraMap K L (x : K) :=
  rfl

/-- The norm of an element integral over the base valuation ring lies in the base valuation ring. -/
lemma algebraNorm_mem_integers_of_mem_integers [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]) :
    Algebra.norm K (x : L) ∈ 𝒪[K] := by
  exact Valuation.Integers.mem_of_integral
    (Valuation.integer.integers (ValuativeRel.valuation K))
    (Algebra.isIntegral_norm K (LocalFieldTheory.ValuativeExtension.integer_isIntegral x))

/-- Defines `normIntegerUnitsValue`. -/
def normIntegerUnitsValue [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) : 𝒪[K] :=
  ⟨Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L),
    algebraNorm_mem_integers_of_mem_integers ((x : 𝒪[L]ˣ) : 𝒪[L])⟩

/-- The norm value constructed from an integer unit multiplied by its inverse is one. -/
lemma normIntegerUnitsValue_mul_inv [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) :
    normIntegerUnitsValue (K := K) (L := L) x *
      normIntegerUnitsValue (K := K) (L := L) x⁻¹ = 1 := by
  ext
  change Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      Algebra.norm K (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
  have hx : (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1 := by
    change (((x * x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
    simp
  rw [← map_mul (Algebra.norm K)]
  simp [hx]

/-- The inverse norm value multiplied by the norm value of an integer unit is one. -/
lemma normIntegerUnitsValue_inv_mul [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) :
    normIntegerUnitsValue (K := K) (L := L) x⁻¹ *
      normIntegerUnitsValue (K := K) (L := L) x = 1 := by
  ext
  change Algebra.norm K (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
  have hx : (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1 := by
    change (((x⁻¹ * x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
    simp
  rw [← map_mul (Algebra.norm K)]
  simp [hx]

/-- Norm restricted to valuation-integer units. -/
def normIntegerUnits
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [LocalFieldTheory.ValuativeExtension K L] : 𝒪[L]ˣ →* 𝒪[K]ˣ where
  toFun := fun x => {
    val := normIntegerUnitsValue (K := K) (L := L) x
    inv := normIntegerUnitsValue (K := K) (L := L) x⁻¹
    val_inv := normIntegerUnitsValue_mul_inv (K := K) (L := L) x
    inv_val := normIntegerUnitsValue_inv_mul (K := K) (L := L) x
  }
  map_one' := by
    ext
    simp [normIntegerUnitsValue]
  map_mul' := by
    intro x y
    ext
    simp [normIntegerUnitsValue]

end UnitNorm

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_GroupTheory_IntegerMultipleSubgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Integer multiple subgroups

Pure group-theoretic infrastructure for the subgroup of multiplicative
integers divisible by a fixed integer and its cyclic quotient. It lives below
the discrete-valuation-field layer so generic power-index code does not depend
on valued-field norm modules.

The declarations retain the established
`LocalFieldTheory.DiscreteValuationField` namespace because the same value
group is used by the valuation API; their implementation has no valued-field
hypotheses.
-/

set_option autoImplicit false

namespace LocalFieldTheory.DiscreteValuationField

/-- The subgroup of `Multiplicative ℤ` consisting of elements whose additive
integer is divisible by `d`. -/
def integerMultipleSubgroup (d : ℤ) : Subgroup (Multiplicative ℤ) where
  carrier := {n | d ∣ Multiplicative.toAdd n}
  one_mem' := by
    change d ∣ (0 : ℤ)
    exact dvd_zero d
  mul_mem' := by
    intro x y hx hy
    change d ∣ Multiplicative.toAdd (x * y)
    rw [toAdd_mul]
    exact dvd_add hx hy
  inv_mem' := by
    intro x hx
    change d ∣ Multiplicative.toAdd x⁻¹
    rw [toAdd_inv]
    exact dvd_neg.mpr hx

/-- An integer lies in the subgroup generated by multiples of `n` exactly when `n` divides it. -/
@[simp] theorem mem_integerMultipleSubgroup_iff
    (d : ℤ) (n : Multiplicative ℤ) :
    n ∈ integerMultipleSubgroup d ↔ d ∣ Multiplicative.toAdd n :=
  Iff.rfl

/-- Membership of a multiplicative integer in the multiple subgroup is equivalent to divisibility of
its additive value. -/
@[simp] theorem ofAdd_mem_integerMultipleSubgroup_iff (d n : ℤ) :
    Multiplicative.ofAdd n ∈ integerMultipleSubgroup d ↔ d ∣ n := by
  rw [mem_integerMultipleSubgroup_iff, toAdd_ofAdd]

/-- Every multiplicative integer belongs to the subgroup of multiples of one. -/
@[simp] theorem integerMultipleSubgroup_one_eq_top :
    integerMultipleSubgroup (1 : ℤ) = ⊤ := by
  ext n
  rw [mem_integerMultipleSubgroup_iff]
  simp

/-- Reduction of multiplicative integers modulo the subgroup of multiples of
`d`, written as a homomorphism to `Multiplicative (ZMod |d|)`. -/
def multiplicativeIntToZModHom (d : ℤ) :
    Multiplicative ℤ →* Multiplicative (ZMod d.natAbs) :=
  AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod d.natAbs))

/-- Reduction modulo `n` sends a multiplicative integer to the residue class of its additive value.
Reduction modulo `n` sends a multiplicative integer to the residue class of its additive value. -/
@[simp] theorem multiplicativeIntToZModHom_apply
    (d : ℤ) (n : Multiplicative ℤ) :
    multiplicativeIntToZModHom d n =
      Multiplicative.ofAdd ((n.toAdd : ZMod d.natAbs)) :=
  rfl

/-- The kernel of reduction modulo `n` is precisely the subgroup of integer multiples of `n`. -/
theorem multiplicativeIntToZModHom_ker_eq_integerMultipleSubgroup (d : ℤ) :
    (multiplicativeIntToZModHom d).ker = integerMultipleSubgroup d := by
  ext n
  change ((n.toAdd : ZMod d.natAbs) = 0) ↔ d ∣ n.toAdd
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.natAbs_dvd

/-- Every residue class modulo `n` is represented by a multiplicative integer. -/
theorem multiplicativeIntToZModHom_surjective (d : ℤ) :
    Function.Surjective (multiplicativeIntToZModHom d) := by
  intro q
  rcases ZMod.intCast_surjective q.toAdd with ⟨n, hn⟩
  refine ⟨Multiplicative.ofAdd n, ?_⟩
  change Multiplicative.ofAdd ((n : ZMod d.natAbs)) = q
  rw [hn]
  rfl

/-- The quotient of multiplicative integers by multiples of `d` is the
standard cyclic value group `Multiplicative (ZMod |d|)`. -/
noncomputable def valueModIntegerMultipleSubgroupEquivZMod (d : ℤ) :
    Multiplicative ℤ ⧸ integerMultipleSubgroup d ≃*
      Multiplicative (ZMod d.natAbs) :=
  (QuotientGroup.quotientMulEquivOfEq
      (multiplicativeIntToZModHom_ker_eq_integerMultipleSubgroup d).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (multiplicativeIntToZModHom d)
      (multiplicativeIntToZModHom_surjective d))

/-- The quotient-to-`ZMod` equivalence sends a quotient class to reduction of its representative
modulo `n`. -/
@[simp] theorem valueModIntegerMultipleSubgroupEquivZMod_mk
    (d n : ℤ) :
    valueModIntegerMultipleSubgroupEquivZMod d
        (QuotientGroup.mk' (integerMultipleSubgroup d)
          (Multiplicative.ofAdd n)) =
      Multiplicative.ofAdd ((n : ZMod d.natAbs)) := by
  change
    (QuotientGroup.quotientKerEquivOfSurjective
        (multiplicativeIntToZModHom d)
        (multiplicativeIntToZModHom_surjective d))
      (QuotientGroup.mk' (multiplicativeIntToZModHom d).ker
        (Multiplicative.ofAdd n)) =
      Multiplicative.ofAdd ((n : ZMod d.natAbs))
  unfold QuotientGroup.quotientKerEquivOfSurjective
    QuotientGroup.quotientKerEquivOfRightInverse
  change
    QuotientGroup.kerLift (multiplicativeIntToZModHom d)
      (QuotientGroup.mk' (multiplicativeIntToZModHom d).ker
        (Multiplicative.ofAdd n)) =
      Multiplicative.ofAdd ((n : ZMod d.natAbs))
  rfl

end LocalFieldTheory.DiscreteValuationField
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_Norm_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Integer-valued norm data

This file contains the norm-subgroup lemmas used in local CFT from an abstract
integer-valued multiplicative valuation and a norm homomorphism satisfying the
standard valuation formula.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

/-- A multiplicative group valuation with values in additive integers. -/
structure MultiplicativeIntegerValuation (G : Type u) [Group G] where
  /-- The integer valuation of a group element. -/
  val : G → ℤ
  /-- The identity has valuation zero. -/
  map_one : val 1 = 0
  /-- Valuation turns multiplication into integer addition. -/
  map_mul : ∀ x y : G, val (x * y) = val x + val y

namespace MultiplicativeIntegerValuation

variable {G : Type u} [Group G] (V : MultiplicativeIntegerValuation G)

/-- Establishes the identity `V.val (1 : G) = 0`. -/
@[simp] theorem val_one : V.val (1 : G) = 0 :=
  V.map_one

/-- `val` satisfies the multiplication formula `V.val (x * y) = V.val x + V.val y`. -/
@[simp] theorem val_mul (x y : G) :
    V.val (x * y) = V.val x + V.val y :=
  V.map_mul x y

/-- The integer-valued valuation as a multiplicative homomorphism to the
additive group of integers written multiplicatively. -/
def valuationHom : G →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (V.val x)
  map_one' := by
    simp [V.val_one]
  map_mul' x y := by
    rw [V.val_mul, ofAdd_add]

/--
The defining evaluation formula for `valuationHom` is `V.valuationHom x = Multiplicative.ofAdd
(V.val x)`.
-/
@[simp] theorem valuationHom_apply (x : G) :
    V.valuationHom x = Multiplicative.ofAdd (V.val x) :=
  rfl

/-- Characterizes `x ∈ V.valuationHom.ker` by the equivalent condition `V.val x = 0`. -/
theorem mem_valuationHom_ker_iff (x : G) :
    x ∈ V.valuationHom.ker ↔ V.val x = 0 := by
  change V.valuationHom x = 1 ↔ V.val x = 0
  rw [V.valuationHom_apply]
  constructor
  · intro hx
    exact Multiplicative.ofAdd.injective (by simpa using hx)
  · intro hx
    rw [hx]
    simp

/-- `val` satisfies the inverse formula `V.val x⁻¹ = -V.val x`. -/
@[simp] theorem val_inv (x : G) :
    V.val x⁻¹ = -V.val x := by
  have h := V.map_mul x x⁻¹
  have h' : V.val x + V.val x⁻¹ = 0 := by
    simpa [V.map_one] using h.symm
  exact eq_neg_iff_add_eq_zero.2 (by simpa [add_comm] using h')

/-- `val` satisfies the division formula `V.val (x / y) = V.val x - V.val y`. -/
@[simp] theorem val_div (x y : G) :
    V.val (x / y) = V.val x - V.val y := by
  rw [div_eq_mul_inv, V.val_mul, V.val_inv, sub_eq_add_neg]

/-- `val` satisfies the natural-power formula `V.val (x ^ n) = (n : ℤ) * V.val x`. -/
@[simp] theorem val_pow (x : G) (n : ℕ) :
    V.val (x ^ n) = (n : ℤ) * V.val x := by
  induction n with
  | zero =>
      rw [pow_zero, V.val_one]
      simp
  | succ n ih =>
      calc
        V.val (x ^ Nat.succ n) = V.val (x ^ n * x) := by
            rw [pow_succ]
        _ = V.val (x ^ n) + V.val x := V.val_mul _ _
        _ = (n : ℤ) * V.val x + V.val x := by
            rw [ih]
        _ = ((n : ℤ) + 1) * V.val x := by
            rw [add_mul, one_mul]
        _ = (Nat.succ n : ℤ) * V.val x := by
            rw [Nat.cast_succ]

/-- `val` satisfies the integer-power formula `V.val (x ^ n) = n * V.val x`. -/
@[simp] theorem val_zpow (x : G) (n : ℤ) :
    V.val (x ^ n) = n * V.val x := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, V.val_pow]
  | negSucc n =>
      rw [zpow_negSucc, V.val_inv, V.val_pow]
      change -(((n + 1 : ℕ) : ℤ) * V.val x) =
        -(((n + 1 : ℕ) : ℤ)) * V.val x
      rw [neg_mul]

/-- Establishes the identity `V.val x⁻¹ = 0`. -/
theorem val_inv_eq_zero_of_val_eq_zero {x : G} (hx : V.val x = 0) :
    V.val x⁻¹ = 0 := by
  rw [V.val_inv, hx, neg_zero]

/-- Characterizes `V.val (x / y) = 0` by the equivalent condition `V.val x = V.val y`. -/
theorem val_div_eq_zero_iff (x y : G) :
    V.val (x / y) = 0 ↔ V.val x = V.val y := by
  rw [V.val_div]
  constructor
  · exact sub_eq_zero.mp
  · exact sub_eq_zero.mpr

/-- Elements of valuation zero. -/
def zeroSubgroup : Subgroup G where
  carrier := {x | V.val x = 0}
  one_mem' := by simp [V.map_one]
  mul_mem' := by
    intro x y hx hy
    change V.val (x * y) = 0
    rw [V.map_mul, hx, hy, add_zero]
  inv_mem' := by
    intro x hx
    exact V.val_inv_eq_zero_of_val_eq_zero hx

/-- Characterizes `x ∈ V.zeroSubgroup` by the equivalent condition `V.val x = 0`. -/
@[simp] theorem mem_zeroSubgroup_iff (x : G) :
    x ∈ V.zeroSubgroup ↔ V.val x = 0 :=
  Iff.rfl

/-- Establishes the identity `V.valuationHom.ker = V.zeroSubgroup`. -/
theorem valuationHom_ker_eq_zeroSubgroup :
    V.valuationHom.ker = V.zeroSubgroup := by
  ext x
  rw [V.mem_valuationHom_ker_iff, V.mem_zeroSubgroup_iff]

/-- The subgroup appearing in `(V.zeroSubgroup).Normal` is normal. -/
instance zeroSubgroup_normal : (V.zeroSubgroup).Normal := by
  rw [← V.valuationHom_ker_eq_zeroSubgroup]
  infer_instance

/-- The value subgroup of an integer-valued valuation.  It is the range of the
valuation homomorphism `valuationHom`. -/
def valueSubgroup : Subgroup (Multiplicative ℤ) :=
  V.valuationHom.range

/--
Characterizes `n ∈ V.valueSubgroup` by the equivalent condition `∃ x : G, V.valuationHom x = n`.
-/
@[simp] theorem mem_valueSubgroup_iff (n : Multiplicative ℤ) :
    n ∈ V.valueSubgroup ↔ ∃ x : G, V.valuationHom x = n :=
  Iff.rfl

/-- First-isomorphism-theorem form for an integer-valued valuation:
the quotient by valuation-zero elements is the value subgroup. -/
noncomputable def quotientZeroSubgroupEquivValueSubgroup :
    G ⧸ V.zeroSubgroup ≃* V.valueSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq
      (V.valuationHom_ker_eq_zeroSubgroup).symm).trans
    (QuotientGroup.quotientKerEquivRange V.valuationHom)

/--
Establishes the identity `V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
V.zeroSubgroup x) = V.valuationHom.rangeRestrict x`.
-/
@[simp] theorem quotientZeroSubgroupEquivValueSubgroup_mk (x : G) :
    V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup x) =
      V.valuationHom.rangeRestrict x :=
  rfl

/--
Establishes the identity `((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
V.zeroSubgroup x) : V.valueSubgroup) : Multiplicative ℤ) = Multiplicative.ofAdd (V.val x)`.
-/
@[simp] theorem coe_quotientZeroSubgroupEquivValueSubgroup_mk (x : G) :
    ((V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) :
      Multiplicative ℤ) =
      Multiplicative.ofAdd (V.val x) := by
  rw [V.quotientZeroSubgroupEquivValueSubgroup_mk]
  rfl

/--
Establishes the identity `Multiplicative.toAdd (((V.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) : Multiplicative ℤ)) = V.val x`.
-/
@[simp] theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_mk (x : G) :
    Multiplicative.toAdd
      (((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) :
        Multiplicative ℤ)) = V.val x := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_mk, toAdd_ofAdd]

/--
Establishes the identity `Multiplicative.toAdd (((V.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' V.zeroSubgroup (x / y)) : V.valueSubgroup) : Multiplicative ℤ)) = V.val x -
V.val y`.
-/
@[simp] theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_div_mk
    (x y : G) :
    Multiplicative.toAdd
      (((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup (x / y)) : V.valueSubgroup) :
        Multiplicative ℤ)) = V.val x - V.val y := by
  rw [V.toAdd_quotientZeroSubgroupEquivValueSubgroup_mk, V.val_div]

/-- A multiplicative element of valuation one. -/
def IsUniformizer (ϖ : G) : Prop :=
  V.val ϖ = 1

/-- `val_uniformizer` satisfies the integer-power formula `V.val (ϖ ^ n) = n`. -/
@[simp] theorem val_uniformizer_zpow {ϖ : G} (hϖ : V.IsUniformizer ϖ)
    (n : ℤ) :
    V.val (ϖ ^ n) = n := by
  rw [V.val_zpow, hϖ, mul_one]

/-- `val_uniformizer` satisfies the natural-power formula `V.val (ϖ ^ n) = (n : ℤ)`. -/
@[simp] theorem val_uniformizer_pow {ϖ : G} (hϖ : V.IsUniformizer ϖ)
    (n : ℕ) :
    V.val (ϖ ^ n) = (n : ℤ) := by
  simpa using V.val_uniformizer_zpow hϖ (n : ℤ)

/--
`coe_quotientZeroSubgroupEquivValueSubgroup_uniformizer` satisfies the integer-power formula
`((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk' V.zeroSubgroup (ϖ ^ n)) :
V.valueSubgroup) : Multiplicative ℤ) = Multiplicative.ofAdd n`.
-/
@[simp] theorem coe_quotientZeroSubgroupEquivValueSubgroup_uniformizer_zpow
    {ϖ : G} (hϖ : V.IsUniformizer ϖ) (n : ℤ) :
    ((V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup (ϖ ^ n)) : V.valueSubgroup) :
      Multiplicative ℤ) = Multiplicative.ofAdd n := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_mk,
    V.val_uniformizer_zpow hϖ n]

/--
`toAdd_quotientZeroSubgroupEquivValueSubgroup_uniformizer` satisfies the integer-power formula
`Multiplicative.toAdd (((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
V.zeroSubgroup (ϖ ^ n)) : V.valueSubgroup) : Multiplicative ℤ)) = n`.
-/
@[simp] theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_uniformizer_zpow
    {ϖ : G} (hϖ : V.IsUniformizer ϖ) (n : ℤ) :
    Multiplicative.toAdd
      (((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup (ϖ ^ n)) : V.valueSubgroup) :
        Multiplicative ℤ)) = n := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_uniformizer_zpow hϖ n,
    toAdd_ofAdd]

/-- A representative-level decomposition `x = u * ϖ^n`, with `u` of valuation
zero.  This is the abstract multiplicative form of `Kˣ = O_Kˣ · ϖ^ℤ`. -/
structure UnitUniformizerDecomposition (ϖ x : G) where
  /-- The valuation-zero factor. -/
  unitPart : G
  /-- The unit factor has valuation zero. -/
  unit_mem : unitPart ∈ V.zeroSubgroup
  /-- The exponent of the chosen uniformizer. -/
  exponent : ℤ
  /-- Reconstruction from the unit factor and uniformizer power. -/
  eq_unit_mul_zpow : x = unitPart * ϖ ^ exponent

/-- Every element admits a unit-uniformizer decomposition with respect to `ϖ`. -/
def HasUnitUniformizerDecomposition (ϖ : G) : Prop :=
  ∀ x : G, Nonempty (V.UnitUniformizerDecomposition ϖ x)

/-- The canonical unit-uniformizer decomposition attached to a uniformizer. -/
def canonicalUnitUniformizerDecomposition {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (x : G) :
    V.UnitUniformizerDecomposition ϖ x where
  unitPart := x * ϖ ^ (-(V.val x))
  unit_mem := by
    rw [V.mem_zeroSubgroup_iff, V.val_mul, V.val_zpow, hϖ]
    ring
  exponent := V.val x
  eq_unit_mul_zpow := by
    calc
      x = x * 1 := by rw [mul_one]
      _ = x * (ϖ ^ (-(V.val x)) * ϖ ^ V.val x) := by
        rw [← zpow_add, neg_add_cancel, zpow_zero]
      _ = (x * ϖ ^ (-(V.val x))) * ϖ ^ V.val x := by
        rw [mul_assoc]

/--
A chosen uniformizer gives a unit-times-uniformizer-power decomposition of every group element.
-/
theorem hasUnitUniformizerDecomposition_of_uniformizer {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) :
    V.HasUnitUniformizerDecomposition ϖ := by
  intro x
  exact ⟨V.canonicalUnitUniformizerDecomposition hϖ x⟩

/--
Every group element has a unit-times-uniformizer-power decomposition relative to a chosen
uniformizer.
-/
theorem unitUniformizerDecomposition {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (x : G) :
    Nonempty (V.UnitUniformizerDecomposition ϖ x) :=
  V.hasUnitUniformizerDecomposition_of_uniformizer hϖ x

/--
`exists_zeroSubgroup_mul_uniformizer` satisfies the integer-power formula `∃ u : G, u ∈
V.zeroSubgroup ∧ ∃ n : ℤ, x = u * ϖ ^ n`.
-/
theorem exists_zeroSubgroup_mul_uniformizer_zpow {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (x : G) :
    ∃ u : G, u ∈ V.zeroSubgroup ∧ ∃ n : ℤ, x = u * ϖ ^ n := by
  rcases V.unitUniformizerDecomposition hϖ x with ⟨d⟩
  exact ⟨d.unitPart, d.unit_mem, d.exponent, d.eq_unit_mul_zpow⟩

namespace UnitUniformizerDecomposition

variable {V : MultiplicativeIntegerValuation G} {ϖ x : G}

/-- Establishes the identity `V.val d.unitPart = 0`. -/
@[simp] theorem unitPart_val_zero
    (d : V.UnitUniformizerDecomposition ϖ x) :
    V.val d.unitPart = 0 :=
  (V.mem_zeroSubgroup_iff d.unitPart).1 d.unit_mem

/-- A valuation-zero multiple of a uniformizer power has valuation equal to
the exponent. -/
theorem val_unit_mul_zpow (hϖ : V.IsUniformizer ϖ)
    {u : G} (hu : u ∈ V.zeroSubgroup) (n : ℤ) :
    V.val (u * ϖ ^ n) = n := by
  rw [V.val_mul, (V.mem_zeroSubgroup_iff u).1 hu,
    V.val_uniformizer_zpow hϖ n, zero_add]

/-- Equality of two unit-uniformizer normal forms forces equality of
exponents. -/
theorem exponent_unique_of_unit_mul_eq (hϖ : V.IsUniformizer ϖ)
    {u w : G} (hu : u ∈ V.zeroSubgroup) (hw : w ∈ V.zeroSubgroup)
    {m n : ℤ} (h : u * ϖ ^ m = w * ϖ ^ n) :
    m = n := by
  have hv := congrArg V.val h
  rw [val_unit_mul_zpow hϖ hu m, val_unit_mul_zpow hϖ hw n] at hv
  exact hv

/-- Equality of two unit-uniformizer normal forms is equivalent to equality of
both the unit part and exponent. -/
theorem unit_mul_zpow_eq_iff (hϖ : V.IsUniformizer ϖ)
    {u w : G} (hu : u ∈ V.zeroSubgroup) (hw : w ∈ V.zeroSubgroup)
    {m n : ℤ} :
    u * ϖ ^ m = w * ϖ ^ n ↔ u = w ∧ m = n := by
  constructor
  · intro h
    have hmn : m = n :=
      exponent_unique_of_unit_mul_eq hϖ hu hw h
    have huw : u = w := by
      calc
        u = (u * ϖ ^ m) * (ϖ ^ m)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
        _ = (w * ϖ ^ n) * (ϖ ^ m)⁻¹ := by
          rw [h]
        _ = (w * ϖ ^ m) * (ϖ ^ m)⁻¹ := by
          rw [hmn]
        _ = w := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
    exact ⟨huw, hmn⟩
  · rintro ⟨huw, hmn⟩
    rw [huw, hmn]

end UnitUniformizerDecomposition

/-- Characterizes `u * ϖ ^ m = w * ϖ ^ n` by the equivalent condition `u = w ∧ m = n`. -/
theorem unit_uniformizer_normal_form_eq_iff {ϖ u w : G}
    (hϖ : V.IsUniformizer ϖ) (hu : u ∈ V.zeroSubgroup)
    (hw : w ∈ V.zeroSubgroup) {m n : ℤ} :
    u * ϖ ^ m = w * ϖ ^ n ↔ u = w ∧ m = n :=
  UnitUniformizerDecomposition.unit_mul_zpow_eq_iff hϖ hu hw

/-- Characterizes `x / y ∈ V.zeroSubgroup` by the equivalent condition `V.val x = V.val y`. -/
theorem div_mem_zeroSubgroup_iff (x y : G) :
    x / y ∈ V.zeroSubgroup ↔ V.val x = V.val y := by
  rw [MultiplicativeIntegerValuation.mem_zeroSubgroup_iff V (x / y),
    V.val_div_eq_zero_iff]

/-- Two elements have quotient in the zero-valuation subgroup exactly when the
left element is the right element multiplied on the left by a zero-valuation
element.  This is the right-coset representative form used in
`Kˣ / O_Kˣ` calculations. -/
theorem div_mem_zeroSubgroup_iff_exists_zeroSubgroup_mul_eq (x y : G) :
    x / y ∈ V.zeroSubgroup ↔
      ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x := by
  constructor
  · intro hxy
    exact ⟨x / y, hxy, by simp [div_eq_mul_inv, mul_assoc]⟩
  · rintro ⟨u, hu, hux⟩
    have hu_eq : u = x / y := by
      have h := congrArg (fun t : G => t * y⁻¹) hux
      simpa [div_eq_mul_inv, mul_assoc] using h
    simpa [← hu_eq] using hu

/--
Characterizes `V.val x = V.val y` by the equivalent condition `∃ u : G, u ∈ V.zeroSubgroup ∧ u * y
= x`.
-/
theorem val_eq_iff_exists_zeroSubgroup_mul_eq (x y : G) :
    V.val x = V.val y ↔
      ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x := by
  rw [← V.div_mem_zeroSubgroup_iff x y,
    V.div_mem_zeroSubgroup_iff_exists_zeroSubgroup_mul_eq x y]

/-- Establishes the identity `∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x`. -/
theorem exists_zeroSubgroup_mul_eq_of_val_eq {x y : G}
    (hxy : V.val x = V.val y) :
    ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x :=
  (V.val_eq_iff_exists_zeroSubgroup_mul_eq x y).1 hxy

end MultiplicativeIntegerValuation

/-- A norm-like homomorphism compatible with integer-valued valuations.

`residueDegree` is proof-attached data: it is the multiplier in
`valuation_formula`, not an independent field-extension invariant.  In the
usual discrete-valued application the source has a uniformizer, and evaluating
`valuation_formula` at that uniformizer uniquely determines this coefficient.
The generic group-level abstraction does not require a uniformizer, so it keeps
the coefficient together with the formula that certifies it. -/
structure ValuedNorm {G : Type u} {H : Type v} [Group G] [Group H]
    (vG : MultiplicativeIntegerValuation G)
    (vH : MultiplicativeIntegerValuation H) where
  /-- The multiplicative norm homomorphism. -/
  toHom : H →* G
  /-- The nonnegative scaling factor in the valuation formula. -/
  residueDegree : ℕ
  /-- Applying the norm scales valuation by the residue-degree factor. -/
  valuation_formula :
    ∀ x : H, vG.val (toHom x) = (residueDegree : ℤ) * vH.val x

end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_Norm_Quotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
Develops quotient groups attached to an abstract valued norm, including kernel, image, and
representative criteria.
-/

/-!
Identifies norm-quotient classes with valuation classes modulo the residue degree and constructs
the resulting cyclic equivalences.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u v

namespace DiscreteValuationField
namespace ValuedNorm

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}
variable (N : ValuedNorm vG vH)

/--
The defining evaluation formula for `valuation` is `vG.val (N.toHom x) = (N.residueDegree : ℤ) *
vH.val x`.
-/
@[simp] theorem valuation_apply (x : H) :
    vG.val (N.toHom x) = (N.residueDegree : ℤ) * vH.val x :=
  N.valuation_formula x

/--
`valuation_apply` satisfies the division formula `vG.val (N.toHom (x / y)) = (N.residueDegree : ℤ)
* (vH.val x - vH.val y)`.
-/
@[simp] theorem valuation_apply_div (x y : H) :
    vG.val (N.toHom (x / y)) =
      (N.residueDegree : ℤ) * (vH.val x - vH.val y) := by
  rw [N.valuation_apply, vH.val_div]

/--
`valuation_apply_uniformizer` satisfies the integer-power formula `vG.val (N.toHom (ϖH ^ n)) =
(N.residueDegree : ℤ) * n`.
-/
@[simp] theorem valuation_apply_uniformizer_zpow {ϖH : H}
    (hϖH : vH.IsUniformizer ϖH) (n : ℤ) :
    vG.val (N.toHom (ϖH ^ n)) = (N.residueDegree : ℤ) * n := by
  rw [N.valuation_apply, vH.val_uniformizer_zpow hϖH n]

/--
`valuation_apply_uniformizer` satisfies the natural-power formula `vG.val (N.toHom (ϖH ^ n)) =
(N.residueDegree : ℤ) * (n : ℤ)`.
-/
@[simp] theorem valuation_apply_uniformizer_pow {ϖH : H}
    (hϖH : vH.IsUniformizer ϖH) (n : ℕ) :
    vG.val (N.toHom (ϖH ^ n)) = (N.residueDegree : ℤ) * (n : ℤ) := by
  rw [N.valuation_apply, vH.val_uniformizer_pow hϖH n]

/--
Establishes the identity `vG.valuationHom (N.toHom x) = vH.valuationHom x ^ (N.residueDegree :
ℤ)`.
-/
@[simp] theorem valuationHom_apply_norm (x : H) :
    vG.valuationHom (N.toHom x) =
      vH.valuationHom x ^ (N.residueDegree : ℤ) := by
  rw [MultiplicativeIntegerValuation.valuationHom_apply,
    N.valuation_apply,
    MultiplicativeIntegerValuation.valuationHom_apply,
    mul_comm (N.residueDegree : ℤ) (vH.val x),
    Int.ofAdd_mul]

/--
Establishes the identity `Multiplicative.toAdd (vG.valuationHom (N.toHom x)) = (N.residueDegree :
ℤ) * Multiplicative.toAdd (vH.valuationHom x)`.
-/
@[simp] theorem toAdd_valuationHom_apply_norm (x : H) :
    Multiplicative.toAdd (vG.valuationHom (N.toHom x)) =
      (N.residueDegree : ℤ) *
        Multiplicative.toAdd (vH.valuationHom x) := by
  rw [N.valuationHom_apply_norm, Int.toAdd_zpow,
    MultiplicativeIntegerValuation.valuationHom_apply, toAdd_ofAdd,
    mul_comm (vH.val x) (N.residueDegree : ℤ)]

/--
`valuationHom_apply_norm` satisfies the division formula `vG.valuationHom (N.toHom (x / y)) =
vH.valuationHom (x / y) ^ (N.residueDegree : ℤ)`.
-/
@[simp] theorem valuationHom_apply_norm_div (x y : H) :
    vG.valuationHom (N.toHom (x / y)) =
      vH.valuationHom (x / y) ^ (N.residueDegree : ℤ) :=
  N.valuationHom_apply_norm (x / y)

/-- The norm subgroup attached to a valued norm. -/
def normSubgroup : Subgroup G :=
  N.toHom.range

/-- The valuation of any norm is divisible by the residue degree. -/
theorem residueDegree_dvd_valuation_of_mem_normSubgroup
    {x : G} (hx : x ∈ N.normSubgroup) :
    (N.residueDegree : ℤ) ∣ vG.val x := by
  rcases hx with ⟨y, rfl⟩
  exact ⟨vH.val y, N.valuation_apply y⟩

/--
Establishes the identity `((vG.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) : Multiplicative ℤ) = vH.valuationHom x ^
(N.residueDegree : ℤ)`.
-/
@[simp] theorem coe_quotientZeroSubgroupEquivValueSubgroup_norm_mk
    (x : H) :
    ((vG.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) :
      Multiplicative ℤ) =
      vH.valuationHom x ^ (N.residueDegree : ℤ) := by
  rw [MultiplicativeIntegerValuation.coe_quotientZeroSubgroupEquivValueSubgroup_mk]
  exact N.valuationHom_apply_norm x

/--
Establishes the identity `Multiplicative.toAdd (((vG.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) : Multiplicative ℤ)) =
(N.residueDegree : ℤ) * vH.val x`.
-/
@[simp] theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_norm_mk
    (x : H) :
    Multiplicative.toAdd
      (((vG.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) :
        Multiplicative ℤ)) =
      (N.residueDegree : ℤ) * vH.val x := by
  rw [N.coe_quotientZeroSubgroupEquivValueSubgroup_norm_mk,
    Int.toAdd_zpow,
    MultiplicativeIntegerValuation.valuationHom_apply, toAdd_ofAdd,
    mul_comm (vH.val x) (N.residueDegree : ℤ)]

/-- If all valuation-zero target elements are norms and the source valuation
has a uniformizer, valuation divisibility by the residue degree is sufficient
for norm-subgroup membership. -/
theorem mem_normSubgroup_of_residueDegree_dvd_val_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    {x : G} (hx : (N.residueDegree : ℤ) ∣ vG.val x) :
    x ∈ N.normSubgroup := by
  rcases hx with ⟨n, hn⟩
  have hval :
      vG.val x = vG.val (N.toHom (ϖH ^ n)) := by
    rw [N.valuation_apply_uniformizer_zpow hϖH n, hn]
  rcases vG.exists_zeroSubgroup_mul_eq_of_val_eq hval with ⟨u, hu, hux⟩
  have hu_norm : u ∈ N.normSubgroup := hzero hu
  have hnorm : u * N.toHom (ϖH ^ n) ∈ N.normSubgroup :=
    N.normSubgroup.mul_mem hu_norm
      ((MonoidHom.mem_range (f := N.toHom)).2 ⟨ϖH ^ n, rfl⟩)
  simpa [← hux] using hnorm

/-- With source uniformizer and norm-surjectivity on valuation-zero target
elements, the norm subgroup is exactly the elements whose valuation is
divisible by the residue degree. -/
theorem mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    x ∈ N.normSubgroup ↔ (N.residueDegree : ℤ) ∣ vG.val x := by
  constructor
  · exact N.residueDegree_dvd_valuation_of_mem_normSubgroup
  · exact N.mem_normSubgroup_of_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖH hzero

/-- The valuation map modulo the residue-degree multiple subgroup.  This is
the canonical value-group map used to compare norm quotients with
`ℤ / fℤ`. -/
def valueModResidueDegreeHom :
    G →* Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  (QuotientGroup.mk'
      (integerMultipleSubgroup (N.residueDegree : ℤ))).comp
    vG.valuationHom

/--
The defining evaluation formula for `valueModResidueDegreeHom` is `N.valueModResidueDegreeHom x =
QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (vG.valuationHom x)`.
-/
@[simp] theorem valueModResidueDegreeHom_apply (x : G) :
    N.valueModResidueDegreeHom x =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (vG.valuationHom x) :=
  rfl

/--
Characterizes `x ∈ N.valueModResidueDegreeHom.ker` by the equivalent condition `(N.residueDegree :
ℤ) ∣ vG.val x`.
-/
theorem mem_valueModResidueDegreeHom_ker_iff (x : G) :
    x ∈ N.valueModResidueDegreeHom.ker ↔
      (N.residueDegree : ℤ) ∣ vG.val x := by
  change N.valueModResidueDegreeHom x = 1 ↔
    (N.residueDegree : ℤ) ∣ vG.val x
  rw [N.valueModResidueDegreeHom_apply,
    MultiplicativeIntegerValuation.valuationHom_apply]
  simp [QuotientGroup.mk'_apply]

/-- The subgroup of `G/G⁰` consisting of classes whose value is divisible by the
residue degree.  This is the kernel of the value-mod-residue-degree map. -/
def residueDegreeClassSubgroup :
    Subgroup (G ⧸ vG.zeroSubgroup) :=
  Subgroup.map (QuotientGroup.mk' vG.zeroSubgroup)
    N.valueModResidueDegreeHom.ker

/-- The subgroup appearing in `N.residueDegreeClassSubgroup.Normal` is normal. -/
instance residueDegreeClassSubgroup_normal :
    N.residueDegreeClassSubgroup.Normal := by
  dsimp [residueDegreeClassSubgroup]
  infer_instance

/-- Establishes the identity `N.valueModResidueDegreeHom.ker = N.normSubgroup`. -/
theorem valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    N.valueModResidueDegreeHom.ker = N.normSubgroup := by
  ext x
  rw [N.mem_valueModResidueDegreeHom_ker_iff,
    N.mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖH hzero x]

/-- The subgroup `N/G⁰` inside the zero-valuation quotient `G/G⁰`, where
`N` is the norm subgroup. -/
def normSubgroupClassInZeroQuotient : Subgroup (G ⧸ vG.zeroSubgroup) :=
  Subgroup.map (QuotientGroup.mk' vG.zeroSubgroup) N.normSubgroup

/-- The subgroup appearing in `N.normSubgroupClassInZeroQuotient.Normal` is normal. -/
instance normSubgroupClassInZeroQuotient_normal
    [(N.normSubgroup).Normal] :
    N.normSubgroupClassInZeroQuotient.Normal := by
  dsimp [normSubgroupClassInZeroQuotient]
  infer_instance

/-- Establishes the identity `N.residueDegreeClassSubgroup = N.normSubgroupClassInZeroQuotient`. -/
theorem residueDegreeClassSubgroup_eq_normSubgroupClassInZeroQuotient_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    N.residueDegreeClassSubgroup =
      N.normSubgroupClassInZeroQuotient := by
  rw [residueDegreeClassSubgroup, normSubgroupClassInZeroQuotient,
    N.valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
      hϖH hzero]

/-- The quotient by the value-side residue-degree class subgroup is the same
as the quotient by the norm-class subgroup when valuation-zero target elements
are norms. -/
noncomputable def zeroQuotientModuloResidueDegreeClassEquivNormClass
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    (G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup ≃*
      (G ⧸ vG.zeroSubgroup) ⧸ N.normSubgroupClassInZeroQuotient :=
  QuotientGroup.quotientMulEquivOfEq
    (N.residueDegreeClassSubgroup_eq_normSubgroupClassInZeroQuotient_of_zeroSubgroup_le
      hϖH hzero)

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup q) = QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient q`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q := by
  rfl

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup x)`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_mk_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk hϖH hzero]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
(QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q) = QuotientGroup.mk'
N.residueDegreeClassSubgroup q`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup q := by
  apply (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).injective
  calc
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        ((N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
          (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q)) =
      QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q := by
        exact
          (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).apply_symm_apply _
    _ =
      N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) := by
        rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk hϖH hzero q]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
(QuotientGroup.mk' N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk hϖH hzero]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormClass_uniformizerClass` satisfies the integer-power
formula `N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero ((QuotientGroup.mk'
N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) = (QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        ((QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk_mk
      hϖH hzero (ϖG ^ n)]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_uniformizerClass` satisfies the
integer-power formula `(N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
((QuotientGroup.mk' N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n)
= (QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
-/
@[simp] theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
        ((QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n]
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk_mk
    hϖH hzero (ϖG ^ n)]

end ValuedNorm

end DiscreteValuationField

end

end LocalFieldTheory

universe u v
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_Valuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Integer-valued valuations

Relates membership in the valuation ring to the ambient valuation and exposes
the associated surjective multiplicative valuation with a uniformizer.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open _root_.LocalFieldTheory.DiscreteValuationField
open scoped ValuativeRel

/-- An element belongs to the valuation ring exactly when its valuation is at most one. -/
theorem valuation_integer_membership
    (K : Type u) [Field K] [ValuativeRel K] (x : K) :
    x ∈ 𝒪[K] ↔ ValuativeRel.valuation K x ≤ 1 :=
  (Valuation.mem_integer_iff (ValuativeRel.valuation K) x).symm

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ValuationExactSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
# The valuation exact sequence

Builds the normalized valuation map `Kˣ → ℤ` and proves exactness of the
sequence from valuation-ring units through field units to `ℤ`.
-/

namespace LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- The multiplicative normalized valuation on field units. -/
noncomputable def valuationUnitsMulHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ →* Multiplicative Int :=
  (@WithZero.unitsWithZeroEquiv (Multiplicative Int) _).toMonoidHom.comp
    ((Units.map (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidHom).comp
      (Units.map (ValuativeRel.valuation K).toMonoidWithZeroHom.toMonoidHom))

/-- The actual normalized valuation map on field units, bundled as an additive hom. -/
noncomputable def valuationMap (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : Additive Kˣ →+ Int :=
  MonoidHom.toAdditive (valuationUnitsMulHom K)

/-- A valuation-theoretic uniformizer, regarded as a unit of the ambient
field.  The nonzero proof is supplied by the actual uniformizer property. -/
noncomputable def uniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : 𝒪[K])
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K)) :
    Kˣ :=
  Units.mk0 (π : K) hπ.ne_zero

/-- Defines `additiveIntegerUnitsToFieldUnits`. -/
def additiveIntegerUnitsToFieldUnits (K : Type u) [Field K] [ValuativeRel K] :
    Additive 𝒪[K]ˣ →+ Additive Kˣ :=
  MonoidHom.toAdditive (integerUnitsToFieldUnits K)

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite ray-modulus data

This file contains the finite local data used by ray congruence subgroups.
A full modulus, including a selected set of real places, is defined in
`AlgebraicNumberTheory.RayClass.FullModulus`.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-- A finite ray modulus. Its finite support records the prime powers
dividing the modulus. -/
abbrev FiniteModulus (K : Type*) [Field K] [NumberField K] :=
  HeightOneSpectrum (𝓞 K) →₀ ℕ

/-- Reduction of local integral units modulo the `n`-th power of the maximal
ideal. -/
def localHigherUnitMap
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (v.adicCompletionIntegers K).units →*
      ((v.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ n)ˣ :=
  (Units.map
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ n)).toMonoidHom).comp
    (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.toMonoidHom

/-- The local higher unit group `U_v^(n)`. -/
def localHigherUnitGroup
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (v.adicCompletion K)ˣ :=
  Subgroup.map
    (v.adicCompletionIntegers K).units.subtype
    (localHigherUnitMap v n).ker

theorem mem_localHigherUnitGroup_iff
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ localHigherUnitGroup v n ↔
      ∃ y : (v.adicCompletionIntegers K).units,
        (y : (v.adicCompletion K)ˣ) = x ∧
        localHigherUnitMap v n y = 1 := by
  rw [localHigherUnitGroup, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, rfl, MonoidHom.mem_ker.mp hy⟩
  · rintro ⟨y, rfl, hy⟩
    exact ⟨y, MonoidHom.mem_ker.mpr hy, rfl⟩

/-- The zeroth higher unit group is the full group of local integral
units. -/
theorem localHigherUnitGroup_zero
    (v : HeightOneSpectrum (𝓞 K)) :
    localHigherUnitGroup v 0 =
      (v.adicCompletionIntegers K).units := by
  ext x
  rw [mem_localHigherUnitGroup_iff]
  constructor
  · rintro ⟨y, rfl, _hy⟩
    exact y.property
  · intro hx
    let y : (v.adicCompletionIntegers K).units := ⟨x, hx⟩
    refine ⟨y, rfl, ?_⟩
    change Units.map
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ 0)).toMonoidHom
        ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y) =
      1
    let : Subsingleton
        ((v.adicCompletionIntegers K) ⧸
          (IsLocalRing.maximalIdeal
            (v.adicCompletionIntegers K)) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    apply Units.ext
    exact Subsingleton.elim _ _

/-- Positivity at a real infinite place.  At a complex place the condition
is vacuous, so this is the whole local multiplicative group. -/
def infinitePositiveSubgroup (v : InfinitePlace K) :
    Subgroup v.Completionˣ where
  carrier := {x | ∀ hv : v.IsReal,
    0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
      hv (x : v.Completion)}
  one_mem' hv := by simp
  mul_mem' {x y} hx hy hv := by
    change 0 <
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
        hv ((x : v.Completion) * (y : v.Completion))
    rw [map_mul]
    exact mul_pos (hx hv) (hy hv)
  inv_mem' {x} hx hv := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_pos.mpr (hx hv)

omit [NumberField K] in
@[simp]
theorem mem_infinitePositiveSubgroup_iff
    (v : InfinitePlace K) (x : v.Completionˣ) :
    x ∈ infinitePositiveSubgroup v ↔
      ∀ hv : v.IsReal,
        0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
          hv (x : v.Completion) :=
  Iff.rfl

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_FullModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ray moduli with selected real places

A ray modulus consists of a finite modulus together with the real places at
which positivity is imposed.  This file defines the corresponding idèle and
idèle-class congruence subgroups without fixing an archimedean convention.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-- A real infinite place of a number field. -/
abbrev RealPlace (K : Type*) [Field K] [NumberField K] :=
  {v : InfinitePlace K // v.IsReal}

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

/-- The integral representative of a unit in a finite completion. -/
def localIntegralValue
    (v : HeightOneSpectrum (𝓞 K))
    (y : (v.adicCompletionIntegers K).units) :
    v.adicCompletionIntegers K :=
  ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y :
    (v.adicCompletionIntegers K)ˣ).1

/-- A local integral unit maps to one modulo the `n`-th maximal-ideal
power exactly when its difference from one belongs to that power. -/
theorem localHigherUnitMap_eq_one_iff
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (y : (v.adicCompletionIntegers K).units) :
    localHigherUnitMap v n y = 1 ↔
      localIntegralValue v y - 1 ∈
          (IsLocalRing.maximalIdeal
            (v.adicCompletionIntegers K)) ^ n := by
  let I :=
    (IsLocalRing.maximalIdeal
      (v.adicCompletionIntegers K)) ^ n
  change
    Units.map (Ideal.Quotient.mk I).toMonoidHom
        ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y) =
      1 ↔ _
  rw [Units.ext_iff]
  change Ideal.Quotient.mk I (localIntegralValue v y) =
      Ideal.Quotient.mk I 1 ↔ _
  exact Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := I) (localIntegralValue v y)
      (1 : v.adicCompletionIntegers K)

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Ideal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ideals prime to a ray-class modulus

This file defines the subgroup of fractional ideals prime to a modulus,
connects it with the corresponding finite-idele higher-unit conditions, and
develops the approximation maps used in ray-class ideal constructions.
-/

open scoped NumberField WithZero Classical
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-! ### Simultaneous approximation at the places in a modulus -/

theorem adicAbv_not_isEquiv_of_ne
    {v w : HeightOneSpectrum (𝓞 K)} (hvw : v ≠ w) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv
      (NumberField.HeightOneSpectrum.adicAbv K w) := by
  intro h
  have hnotle : ¬ v.asIdeal ≤ w.asIdeal := by
    intro hvw_le
    have htop_le : (⊤ : Ideal (𝓞 K)) ≤ w.asIdeal := by
      rw [← (v.isCoprime_of_ne w hvw).sup_eq]
      exact sup_le hvw_le le_rfl
    exact w.isPrime.ne_top (top_unique htop_le)
  obtain ⟨x, hxv, hxw⟩ := Set.not_subset.mp hnotle
  have hvlt :
      NumberField.HeightOneSpectrum.adicAbv K v
        (algebraMap (𝓞 K) K x) < 1 := by
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem (K := K) v x).2 hxv
  have hweq :
      NumberField.HeightOneSpectrum.adicAbv K w
        (algebraMap (𝓞 K) K x) = 1 := by
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_eq_one_iff_notMem (K := K) w x).2 hxw
  exact (ne_of_lt hvlt) (h.eq_one_iff.mpr hweq)

theorem denseRange_finiteApproximationCompletionMap
    (v : HeightOneSpectrum (𝓞 K)) :
    DenseRange
      (fun x :
          WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) =>
        FinitePlace.embedding v
          (WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v) x)) := by
  have hrange :
      Set.range
          (fun x :
              WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) =>
            FinitePlace.embedding v
              (WithAbs.equiv
                (NumberField.HeightOneSpectrum.adicAbv K v) x)) =
        Set.range (algebraMap K (v.adicCompletion K)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact
        ⟨WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v) x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine
        ⟨(WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v)).symm x, ?_⟩
      rfl
  rw [DenseRange, hrange]
  exact v.denseRange_algebraMap K

theorem continuous_finiteApproximationCompletionMap
    (v : HeightOneSpectrum (𝓞 K)) :
    Continuous
      (fun x :
          WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) =>
        FinitePlace.embedding v
          (WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v) x)) := by
  apply Isometry.continuous
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub,
    FinitePlace.norm_embedding]
  rfl

/-- The open set of field elements whose ratio with a fixed unit lies in
a prescribed open unit set. -/
def unitRatioSet
    {F : Type*} [Field F] (a : Fˣ) (U : Subgroup Fˣ) :
    Set F :=
  Units.val '' (fun y : Fˣ => a * y⁻¹) ⁻¹' (U : Set Fˣ)

/-- The unit-ratio set associated to an open set of units is open. -/
theorem isOpen_unitRatioSet
    {F : Type*} [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] [ContinuousInv₀ F] [T1Space F]
    (a : Fˣ) (U : Subgroup Fˣ)
    (hU : IsOpen (U : Set Fˣ)) :
    IsOpen (unitRatioSet a U) := by
  apply IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap
  exact hU.preimage (continuous_const.mul continuous_inv)

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_Theory_ExponentialValuations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-! Provides the public declarations in the `ValuationTheory.AbsoluteValue.Theory.ExponentialValuations` Lean module. -/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace LubinTate
namespace Valuations

/-- The DVR ideal `π^n𝒪`. -/
def uniformizerPowerIdeal {O : Type*} [CommRing O] (π : O) (n : ℕ) : Ideal O :=
  Ideal.span ({π ^ n} : Set O)

end Valuations
end LubinTate
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_Theory_Core
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-! Provides the public declarations in the `ValuationTheory.AbsoluteValue.Theory` Lean module. -/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace LubinTate
namespace Valuations

/-- The graded piece `π^n𝒪 / π^{n+1}𝒪` as an additive quotient. -/
def uniformizerGradedPiece {O : Type*} [CommRing O] (π : O) (n : ℕ) : Type _ :=
  (uniformizerPowerIdeal π n) ⧸
    (Submodule.comap (uniformizerPowerIdeal π n).subtype
      (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
        Submodule O (uniformizerPowerIdeal π n))

/-- A uniformizer graded piece inherits an additive commutative group structure. -/
instance uniformizerGradedPieceAddCommGroup
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    AddCommGroup (uniformizerGradedPiece π n) := by
  change AddCommGroup
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)))
  infer_instance

/-- A uniformizer graded piece is a module over the valuation subring. -/
instance uniformizerGradedPieceModule
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    Module O (uniformizerGradedPiece π n) := by
  change Module O
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)))
  infer_instance

/-- Explicit access to the submodule quotient implementing a uniformizer
graded piece. -/
def uniformizerGradedPieceConcreteLinearEquiv
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    uniformizerGradedPiece π n ≃ₗ[O]
      ((uniformizerPowerIdeal π n) ⧸
        (Submodule.comap (uniformizerPowerIdeal π n).subtype
          (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
            Submodule O (uniformizerPowerIdeal π n))) := by
  change
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n))) ≃ₗ[O]
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)))
  exact LinearEquiv.refl O _

/-- The canonical class map into `π^n𝒪 / π^(n+1)𝒪`. -/
def uniformizerGradedPieceMk
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    uniformizerPowerIdeal π n →ₗ[O] uniformizerGradedPiece π n := by
  change uniformizerPowerIdeal π n →ₗ[O]
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)))
  exact Submodule.mkQ _

/-- The concrete graded-piece equivalence sends a quotient representative to the same coset. -/
@[simp] theorem uniformizerGradedPieceConcreteLinearEquiv_mk
    {O : Type*} [CommRing O] (π : O) (n : ℕ)
    (a : uniformizerPowerIdeal π n) :
    uniformizerGradedPieceConcreteLinearEquiv π n
        (uniformizerGradedPieceMk π n a) =
      Submodule.Quotient.mk a :=
  rfl

/-- Descend a linear map that vanishes on `π^(n+1)𝒪` inside `π^n𝒪`. -/
def uniformizerGradedPieceLinearLift
    {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M]
    (π : O) (n : ℕ)
    (f : uniformizerPowerIdeal π n →ₗ[O] M)
    (h :
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)) ≤ f.ker) :
    uniformizerGradedPiece π n →ₗ[O] M := by
  change
    ((uniformizerPowerIdeal π n) ⧸
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n))) →ₗ[O] M
  exact
    (Submodule.comap (uniformizerPowerIdeal π n).subtype
      (uniformizerPowerIdeal π (n + 1) : Submodule O O)).liftQ f h

/-- A linear lift from the graded piece evaluates on representatives by the supplied map. -/
@[simp] theorem uniformizerGradedPieceLinearLift_mk
    {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M]
    (π : O) (n : ℕ)
    (f : uniformizerPowerIdeal π n →ₗ[O] M)
    (h :
      (Submodule.comap (uniformizerPowerIdeal π n).subtype
        (uniformizerPowerIdeal π (n + 1) : Submodule O O) :
          Submodule O (uniformizerPowerIdeal π n)) ≤ f.ker)
    (a : uniformizerPowerIdeal π n) :
    uniformizerGradedPieceLinearLift π n f h
        (uniformizerGradedPieceMk π n a) = f a :=
  rfl

/-- The higher-unit condition `u ∈ 1 + π^n𝒪`. -/
def HigherUnit {O : Type*} [CommRing O] (π : O) (n : ℕ) (u : Oˣ) : Prop :=
  ∃ a : O, (u : O) = 1 + π ^ n * a

/-- The higher-unit condition is equivalently `u - 1 ∈ π^n𝒪`. -/
theorem higherUnit_iff_sub_one_mem_powerIdeal {O : Type*} [CommRing O]
    (π : O) (n : ℕ) (u : Oˣ) :
    HigherUnit π n u ↔ (u : O) - 1 ∈ uniformizerPowerIdeal π n := by
  constructor
  · rintro ⟨a, ha⟩
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton']
    refine ⟨a, ?_⟩
    rw [ha]
    ring
  · intro hu
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton'] at hu
    rcases hu with ⟨a, ha⟩
    use a
    calc
      (u : O) = 1 + ((u : O) - 1) := by ring
      _ = 1 + a * π ^ n := by rw [← ha]
      _ = 1 + π ^ n * a := by ring

/-- The higher unit group `U⁽ⁿ⁾ = 1 + π^n𝒪`, as an actual subgroup of `Oˣ`. -/
def higherUnitSubgroup {O : Type*} [CommRing O] (π : O) (n : ℕ) : Subgroup Oˣ where
  carrier := {u | HigherUnit π n u}
  one_mem' := by
    use 0
    simp
  mul_mem' := by
    rintro u v ⟨a, ha⟩ ⟨b, hb⟩
    use a + b + π ^ n * a * b
    calc
      ((u * v : Oˣ) : O) = (u : O) * (v : O) := rfl
      _ = (1 + π ^ n * a) * (1 + π ^ n * b) := by rw [ha, hb]
      _ = 1 + π ^ n * (a + b + π ^ n * a * b) := by ring
  inv_mem' := by
    rintro u ⟨a, ha⟩
    use -((u⁻¹ : Oˣ) : O) * a
    have hmul : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := by
      simp
    calc
      ((u⁻¹ : Oˣ) : O) =
          ((u⁻¹ : Oˣ) : O) * (u : O) -
            ((u⁻¹ : Oˣ) : O) * ((u : O) - 1) := by
        ring
      _ = 1 - ((u⁻¹ : Oˣ) : O) * ((u : O) - 1) := by
        rw [hmul]
      _ = 1 + π ^ n * (-((u⁻¹ : Oˣ) : O) * a) := by
        rw [ha]
        ring

/-- Membership in a higher-unit subgroup is characterized by proximity to one at the given level. -/
@[simp]
theorem mem_higherUnitSubgroup {O : Type*} [CommRing O]
    {π : O} {n : ℕ} {u : Oˣ} :
    u ∈ higherUnitSubgroup π n ↔ HigherUnit π n u :=
  Iff.rfl

/-- Membership in the higher-unit subgroup is equivalently `u - 1 ∈ π^n𝒪`. -/
theorem mem_higherUnitSubgroup_iff_sub_one_mem_powerIdeal
    {O : Type*} [CommRing O] {π : O} {n : ℕ} {u : Oˣ} :
    u ∈ higherUnitSubgroup π n ↔ (u : O) - 1 ∈ uniformizerPowerIdeal π n := by
  exact Iff.trans mem_higherUnitSubgroup
    (higherUnit_iff_sub_one_mem_powerIdeal π n u)

/-- The higher-unit filtration is decreasing for arbitrary comparable indices. -/
theorem higherUnitSubgroup_le_of_le {O : Type*} [CommRing O]
    (π : O) {m n : ℕ} (hmn : m ≤ n) :
    higherUnitSubgroup π n ≤ higherUnitSubgroup π m := by
  rintro u ⟨a, ha⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  use π ^ k * a
  calc
    (u : O) = 1 + π ^ (m + k) * a := ha
    _ = 1 + π ^ m * (π ^ k * a) := by
      rw [pow_add]
      ring

/-- Reduction of units modulo an ideal. -/
def unitReduction {O : Type*} [CommRing O] (I : Ideal O) : Oˣ →* (O ⧸ I)ˣ :=
  Units.map (Ideal.Quotient.mk I).toMonoidHom

/-- Unit reduction is the residue of the underlying valuation-ring unit. -/
@[simp]
theorem unitReduction_apply {O : Type*} [CommRing O] (I : Ideal O) (u : Oˣ) :
    (unitReduction I u : O ⧸ I) = Ideal.Quotient.mk I (u : O) :=
  rfl

/-- The kernel of reduction modulo `π^n𝒪` is the higher unit group `1 + π^n𝒪`. -/
theorem unitReduction_ker_powerIdeal {O : Type*} [CommRing O]
    (π : O) (n : ℕ) :
    (unitReduction (uniformizerPowerIdeal π n)).ker = higherUnitSubgroup π n := by
  ext u
  constructor
  · intro hu
    have hval :
        Ideal.Quotient.mk (uniformizerPowerIdeal π n) (u : O) = 1 := by
      simpa [unitReduction] using congrArg Units.val hu
    have hmem : (u : O) - 1 ∈ uniformizerPowerIdeal π n := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp [map_sub, hval]
    rw [uniformizerPowerIdeal, Ideal.mem_span_singleton] at hmem
    rcases hmem with ⟨a, ha⟩
    use a
    calc
      (u : O) = 1 + ((u : O) - 1) := by ring
      _ = 1 + π ^ n * a := by rw [ha]
  · rintro ⟨a, ha⟩
    rw [MonoidHom.mem_ker]
    ext
    change Ideal.Quotient.mk (uniformizerPowerIdeal π n) (u : O) = 1
    rw [ha]
    rw [← (Ideal.Quotient.mk (uniformizerPowerIdeal π n)).map_one]
    apply Ideal.Quotient.eq.mpr
    have hπ : π ^ n ∈ uniformizerPowerIdeal π n :=
      Ideal.subset_span (by simp)
    simpa using (uniformizerPowerIdeal π n).mul_mem_right a hπ

/-- A local quotient map induces a surjection on unit groups. -/
theorem unitReduction_surjective_of_isLocalHom {O : Type*} [CommRing O]
    (I : Ideal O) [IsLocalHom (Ideal.Quotient.mk I)] :
    Function.Surjective (unitReduction I) := by
  exact IsLocalRing.surjective_units_map_of_local_ringHom
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective inferInstance

/-- The first-isomorphism-theorem form of the unit quotient modulo `π^n𝒪`. -/
noncomputable def unitsModPowerIdealEquivOfSurjective {O : Type*} [CommRing O]
    (π : O) (n : ℕ)
    (hsurj : Function.Surjective (unitReduction (uniformizerPowerIdeal π n))) :
    Oˣ ⧸ higherUnitSubgroup π n ≃* (O ⧸ uniformizerPowerIdeal π n)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq
      (unitReduction_ker_powerIdeal π n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (unitReduction (uniformizerPowerIdeal π n)) hsurj)

/-- For `n ≥ 1`, the ideal `π^n𝒪` is contained in `(π)`. -/
theorem uniformizerPowerIdeal_le_span_singleton {O : Type*} [CommRing O]
    {π : O} {n : ℕ} (hn : 1 ≤ n) :
    uniformizerPowerIdeal π n ≤ Ideal.span ({π} : Set O) := by
  cases n with
  | zero => cases hn
  | succ n =>
      rw [uniformizerPowerIdeal, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      exact ⟨π ^ n, by simp [pow_succ, mul_comm]⟩

/-- In a DVR, `π^n𝒪` lies in the Jacobson radical for `n ≥ 1` and `π` irreducible. -/
theorem uniformizerPowerIdeal_le_jacobson_bot {O : Type*}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    uniformizerPowerIdeal π n ≤ Ideal.jacobson (⊥ : Ideal O) := by
  have hmax : (Ideal.span ({π} : Set O)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hπ
  have hspan : Ideal.span ({π} : Set O) = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal hmax
  exact (uniformizerPowerIdeal_le_span_singleton (π := π) hn).trans
    (by rw [hspan]; exact IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal O))

/-- The quotient map modulo `π^n𝒪` is local in a DVR, for `n ≥ 1`. -/
theorem unitReduction_isLocalHom_of_dvr {O : Type*}
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    IsLocalHom (Ideal.Quotient.mk (uniformizerPowerIdeal π n)) :=
  isLocalHom_of_le_jacobson_bot (uniformizerPowerIdeal π n)
    (uniformizerPowerIdeal_le_jacobson_bot hπ hn)

/-- The unit-reduction and graded-piece equivalences, surjectivity part for the reduction map on unit groups. -/
theorem units_reduction_surjective
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    Function.Surjective (unitReduction (uniformizerPowerIdeal π n)) := by
  let : IsLocalHom (Ideal.Quotient.mk (uniformizerPowerIdeal π n)) :=
    unitReduction_isLocalHom_of_dvr hπ hn
  exact unitReduction_surjective_of_isLocalHom (uniformizerPowerIdeal π n)

/-- The unit-reduction and graded-piece equivalences, the named first-isomorphism-theorem equivalence
`Oˣ/U⁽ⁿ⁾ ≃ (O/π^nO)ˣ`. -/
noncomputable def units_quotient_equiv
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    Oˣ ⧸ higherUnitSubgroup π n ≃* (O ⧸ uniformizerPowerIdeal π n)ˣ := by
  exact unitsModPowerIdealEquivOfSurjective π n
    (units_reduction_surjective hπ hn)

/-- The unit-quotient equivalence of the unit-reduction and graded-piece equivalences is induced by
reduction modulo `πⁿO`. -/
@[simp]
theorem units_quotient_equiv_mk
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) (u : Oˣ) :
    units_quotient_equiv hπ hn (QuotientGroup.mk u) =
      unitReduction (uniformizerPowerIdeal π n) u := by
  change QuotientGroup.kerLift (unitReduction (uniformizerPowerIdeal π n))
      ((QuotientGroup.quotientMulEquivOfEq
        (unitReduction_ker_powerIdeal π n).symm) (QuotientGroup.mk u)) =
    unitReduction (uniformizerPowerIdeal π n) u
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk (unitReduction (uniformizerPowerIdeal π n)) u

end Valuations
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_AdicPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Adic completeness and positive powers of an ideal

This file contains small generic source lemmas used to pass from completeness
for a positive power `I ^ n` back to completeness for `I`.
-/

noncomputable section

namespace DiscreteValuationField

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

/-- Adic completeness is preserved by a linear equivalence of modules over the
same base ring and with respect to the same ideal. -/
theorem isAdicComplete_of_linearEquiv
    (I : Ideal R) (e : M ≃ₗ[R] N) [IsAdicComplete I M] :
    IsAdicComplete I N := by
  refine AdicCompletion.of_bijective_iff.mp ?_
  constructor
  · intro x y hxy
    have hpre :
        e.symm x = e.symm y := by
      apply (AdicCompletion.of_bijective I M).1
      apply (AdicCompletion.congr I e).injective
      simpa [AdicCompletion.congr_apply, AdicCompletion.map_of] using hxy
    exact e.symm.injective hpre
  · intro y
    obtain ⟨m, hm⟩ :=
      (AdicCompletion.of_bijective I M).2
        ((AdicCompletion.congr I e).symm y)
    refine ⟨e m, ?_⟩
    calc
      AdicCompletion.of I N (e m) =
          AdicCompletion.congr I e (AdicCompletion.of I M m) := by
        simp [AdicCompletion.congr_apply, AdicCompletion.map_of]
      _ = AdicCompletion.congr I e
          ((AdicCompletion.congr I e).symm y) := by
        rw [hm]
      _ = y := (AdicCompletion.congr I e).apply_symm_apply y

/-- Membership in a power of the extended ideal is the same as membership in
the corresponding base-adic submodule after restricting scalars. -/
theorem mem_map_algebraMap_pow_iff_mem_pow_smul_top
    {S : Type*} [CommRing S] [Algebra R S] (I : Ideal R)
    (n : ℕ) {x : S} :
    x ∈ (I.map (algebraMap R S)) ^ n ↔
      x ∈ I ^ n • (⊤ : Submodule R S) := by
  rw [Ideal.smul_top_eq_map, Ideal.map_pow]
  rfl

/-- The same scalar-restriction comparison as a submodule-membership statement. -/
theorem mem_map_algebraMap_pow_smul_top_iff
    {S : Type*} [CommRing S] [Algebra R S] (I : Ideal R)
    (n : ℕ) {x : S} :
    x ∈ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S S) ↔
      x ∈ I ^ n • (⊤ : Submodule R S) := by
  simpa only [smul_eq_mul, Ideal.mul_top] using
    (mem_map_algebraMap_pow_iff_mem_pow_smul_top
      (R := R) (S := S) I n (x := x))

/-- Congruence modulo powers of an extended ideal is unchanged after
restricting scalars to the base ring. -/
theorem smodEq_map_algebraMap_pow_smul_top_iff
    {S : Type*} [CommRing S] [Algebra R S] (I : Ideal R)
    {x y : S} (n : ℕ) :
    x ≡ y [SMOD ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S S)] ↔
      x ≡ y [SMOD (I ^ n • ⊤ : Submodule R S)] := by
  rw [SModEq.sub_mem, SModEq.sub_mem]
  exact mem_map_algebraMap_pow_smul_top_iff (I := I) n

/-- Restricting scalars along an algebra map does not change precompleteness
for the ideal generated by the base ideal. -/
theorem isPrecomplete_map_algebraMap_iff
    {S : Type*} [CommRing S] [Algebra R S] (I : Ideal R) :
    IsPrecomplete (I.map (algebraMap R S)) S ↔ IsPrecomplete I S := by
  constructor
  · intro h
    refine ⟨fun f hf => ?_⟩
    have hfS :
        ∀ {m n : ℕ}, m ≤ n →
          f m ≡ f n
            [SMOD ((I.map (algebraMap R S)) ^ m • ⊤ : Submodule S S)] := by
      intro m n hmn
      exact (smodEq_map_algebraMap_pow_smul_top_iff (I := I) m).mpr (hf hmn)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec h hfS
    refine ⟨L, fun n => ?_⟩
    exact (smodEq_map_algebraMap_pow_smul_top_iff (I := I) n).mp (hL n)
  · intro h
    refine ⟨fun f hf => ?_⟩
    have hfR :
        ∀ {m n : ℕ}, m ≤ n →
          f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R S)] := by
      intro m n hmn
      exact (smodEq_map_algebraMap_pow_smul_top_iff (I := I) m).mp (hf hmn)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec h hfR
    refine ⟨L, fun n => ?_⟩
    exact (smodEq_map_algebraMap_pow_smul_top_iff (I := I) n).mpr (hL n)

/-- Restricting scalars along an algebra map does not change adic
completeness for the ideal generated by the base ideal. -/
theorem isAdicComplete_map_algebraMap_iff
    {S : Type*} [CommRing S] [Algebra R S] (I : Ideal R) :
    IsAdicComplete (I.map (algebraMap R S)) S ↔ IsAdicComplete I S := by
  constructor
  · intro h
    exact
      { toIsHausdorff := IsHausdorff.map_algebraMap_iff.mp h.toIsHausdorff
        toIsPrecomplete := (isPrecomplete_map_algebraMap_iff
          (R := R) (S := S) I).mp h.toIsPrecomplete }
  · intro h
    exact
      { toIsHausdorff := IsHausdorff.map_algebraMap_iff.mpr h.toIsHausdorff
        toIsPrecomplete := (isPrecomplete_map_algebraMap_iff
          (R := R) (S := S) I).mpr h.toIsPrecomplete }

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Henselian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Henselian discretely valued fields

This file contains the lightweight package for a discretely valued field whose
valuation ring is Henselian at its maximal ideal.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

/-- The idempotent polynomial `X^2 - X` is monic in every nontrivial
coefficient ring. -/
theorem idempotentPolynomial_monic
    {R : Type*} [CommRing R] [Nontrivial R] :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).Monic := by
  exact Polynomial.monic_X_pow_sub (by
    rw [Polynomial.degree_X]
    norm_num)

/-- A quotient idempotent is an approximate root of `X^2 - X`. -/
theorem idempotentPolynomial_eval_mem_of_quotient_idempotent
    {R : Type*} [CommRing R] {I : Ideal R} (a0 : R)
    (ha0 : IsIdempotentElem (Ideal.Quotient.mk I a0)) :
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).eval a0 ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change
    Ideal.Quotient.mk I
      ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).eval a0) = 0
  simpa [pow_two] using sub_eq_zero.mpr ha0.eq

/-- At a quotient idempotent, the derivative of `X^2 - X` is a unit in the
quotient. -/
theorem idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent
    {R : Type*} [CommRing R] {I : Ideal R} (a0 : R)
    (ha0 : IsIdempotentElem (Ideal.Quotient.mk I a0)) :
    IsUnit
      (Ideal.Quotient.mk I
        ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).derivative.eval a0)) := by
  rw [isUnit_iff_exists]
  refine
    ⟨Ideal.Quotient.mk I
      ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).derivative.eval a0),
      ?_, ?_⟩
  · simp [pow_two]
    calc
      (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) *
          (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) =
        1 + (4 * (Ideal.Quotient.mk I a0 * Ideal.Quotient.mk I a0) -
          4 * Ideal.Quotient.mk I a0) := by
          ring
      _ = 1 := by
          rw [ha0.eq]
          ring
  · simp [pow_two]
    calc
      (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) *
          (Ideal.Quotient.mk I a0 + Ideal.Quotient.mk I a0 - 1) =
        1 + (4 * (Ideal.Quotient.mk I a0 * Ideal.Quotient.mk I a0) -
          4 * Ideal.Quotient.mk I a0) := by
          ring
      _ = 1 := by
          rw [ha0.eq]
          ring

/-- Idempotents lift along a surjective ring map whose kernel is a Henselian
ideal.

This is the `X^2 - X` simple-root form of Hensel's lemma.  At an idempotent,
the derivative `2X - 1` is a unit because its square is `1`. -/
theorem exists_idempotent_lift_of_surjective_henselianRing_ker
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f)
    [HenselianRing R (RingHom.ker f)]
    (e : S) (he : IsIdempotentElem e) :
    ∃ e' : R, IsIdempotentElem e' ∧ f e' = e := by
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      have hS : Subsingleton S := by
        constructor
        intro x y
        rcases hf x with ⟨a, rfl⟩
        rcases hf y with ⟨b, rfl⟩
        exact congrArg f (Subsingleton.elim a b)
      exact ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  | inr hR =>
      let : Nontrivial R := hR
      rcases hf e with ⟨a0, ha0⟩
      let p : Polynomial R := Polynomial.X ^ 2 - Polynomial.X
      have hpmonic : p.Monic := by
        dsimp [p]
        exact idempotentPolynomial_monic
      have ha0_quotient :
          IsIdempotentElem
            (Ideal.Quotient.mk (RingHom.ker f) a0) := by
        rw [IsIdempotentElem]
        rw [← map_mul, Ideal.Quotient.eq]
        rw [RingHom.mem_ker]
        simp [ha0, he.eq]
      have hroot : p.eval a0 ∈ RingHom.ker f := by
        simpa [p] using
          idempotentPolynomial_eval_mem_of_quotient_idempotent
            (I := RingHom.ker f) a0 ha0_quotient
      have hsimple :
          IsUnit
            (Ideal.Quotient.mk (RingHom.ker f) (p.derivative.eval a0)) := by
        simpa [p] using
          idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent
            (I := RingHom.ker f) a0 ha0_quotient
      rcases HenselianRing.is_henselian p hpmonic a0 hroot hsimple with
        ⟨a, haroot, hacongr⟩
      refine ⟨a, ?_, ?_⟩
      · change a * a = a
        exact sub_eq_zero.mp (by simpa [p, pow_two] using haroot)
      · have hsub : f (a - a0) = 0 := RingHom.mem_ker.mp hacongr
        rw [map_sub, ha0, sub_eq_zero] at hsub
        exact hsub

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Complete discretely valued fields
-/

noncomputable section

universe u v w

namespace DiscreteValuationField

namespace Valuation

variable {K : Type u} [Field K]
variable {Gamma : Type v} [LinearOrderedCommGroupWithZero Gamma]

/-- In a rank-one discrete valuation ring, membership in the `n`-th power of
the maximal ideal is the same as the corresponding valuation bound against a
chosen uniformizer power. -/
theorem mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
    (val : _root_.Valuation K Gamma) [val.IsRankOneDiscrete]
    {pi x : val.valuationSubring}
    (hpi : val.IsUniformizer (pi : K)) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal val.valuationSubring ^ n ↔
      val (x : K) ≤ val ((pi ^ n : val.valuationSubring) : K) := by
  rw [hpi.is_generator, Ideal.span_singleton_pow]
  simpa [Ideal.mem_span_singleton] using
    (_root_.Valuation.Integers.dvd_iff_le
      (_root_.Valuation.valuationSubring.integers (v := val))
      (x := pi ^ n) (y := x))

end Valuation

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
open OAI

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

/-- The valuation-subring algebra maps are compatible with the ambient field
algebra map for any chosen valuation extension. -/
theorem valuationSubring_isScalarTower_of_hasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] :
    IsScalarTower vK.valuationSubring vL.valuationSubring L := by
  refine ⟨?_⟩
  intro a b z
  simp only [Algebra.smul_def]
  have hmap :
      (algebraMap vL.valuationSubring L)
          ((algebraMap vK.valuationSubring vL.valuationSubring) a) =
        (algebraMap vK.valuationSubring L) a := by
    rfl
  rw [map_mul, hmap, mul_assoc]

end Valuation
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_HenselianFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Finite algebra consequences of Henselian pairs

This file keeps the Nakayama and finite-module completion consequences away
from the lightweight `HenselianDVF` core.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

/-- Same-universe finite modules over a Noetherian adically complete ring are
adically complete. -/
theorem isAdicComplete_of_moduleFinite_sameUniverse
    {R M : Type u} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    [IsAdicComplete I R] :
    IsAdicComplete I M := by
  refine AdicCompletion.of_bijective_iff.mp ?_
  let e : M ≃ₗ[R] AdicCompletion I M :=
    (TensorProduct.lid R M).symm.trans
      ((TensorProduct.congr (AdicCompletion.ofLinearEquiv I R)
        (LinearEquiv.refl R M)).trans
        ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R))
  have heq : (e : M →ₗ[R] AdicCompletion I M) = AdicCompletion.of I M := by
    ext x n
    simp [e]
    exact one_smul (R ⧸ (I ^ n • ⊤ : Ideal R))
      (Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R M)) x)
  have hebij : Function.Bijective (e : M → AdicCompletion I M) := e.bijective
  rw [← heq]
  exact hebij

/-- A finite module over a Noetherian adically complete ring is adically complete.

This is a universe-polymorphic wrapper around mathlib's tensor-product
finite-module completion theorem. -/
theorem isAdicComplete_of_moduleFinite
    {R : Type u} {M : Type v} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    [IsAdicComplete I R] :
    IsAdicComplete I M := by
  let : Small.{u} M := Module.Finite.small R M
  let : Module.Finite R (Shrink.{u} M) :=
    Module.Finite.of_surjective
      ((Shrink.linearEquiv R M).symm : M →ₗ[R] Shrink.{u} M)
      (Shrink.linearEquiv R M).symm.surjective
  have : IsAdicComplete I (Shrink.{u} M) :=
    isAdicComplete_of_moduleFinite_sameUniverse (I := I)
  exact ValuationTheory.DiscreteValuationField.isAdicComplete_of_linearEquiv
    (I := I) (Shrink.linearEquiv R M)

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_IntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Integral closures of valuation rings

This module uses the actual mathlib integral closure
`integralClosure base.toDVF.valuationSubring L`.  It does not introduce a replacement
structure.
-/

noncomputable section

universe u v w x

namespace DiscreteValuationField
namespace ValuedExtension

/-- An Artinian ring whose idempotents are all trivial has at most one prime.

This is the topological/idempotent bridge used in the Henselian frontier:
in an Artinian ring, `Spec` is discrete, so a hypothetical singleton clopen
separating two primes is represented by an idempotent. -/
theorem primeSpectrum_subsingleton_of_isArtinianRing_of_idempotents_trivial
    {A : Type u} [CommRing A] [IsArtinianRing A]
    (hidempotent : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Subsingleton (PrimeSpectrum A) := by
  constructor
  intro P Q
  by_contra hPQ
  have hclopen : IsClopen ({P} : Set (PrimeSpectrum A)) :=
    isClopen_discrete {P}
  rcases PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hclopen with
    ⟨e, heidem, heopen⟩
  rcases hidempotent e heidem with rfl | rfl
  · have hPmem :
        P ∈ (PrimeSpectrum.basicOpen (0 : A) : Set (PrimeSpectrum A)) := by
      rw [← heopen]
      exact Set.mem_singleton P
    simp at hPmem
  · have hQmem : Q ∈ ({P} : Set (PrimeSpectrum A)) := by
      rw [heopen]
      simp
    exact hPQ hQmem.symm

/-- Over a local base ring, the canonical map from an algebra to the fiber over
the maximal ideal is surjective. -/
theorem maximalIdeal_fiber_includeRight_surjective
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [Algebra R S] :
    Function.Surjective
      (Algebra.TensorProduct.includeRight :
        S →ₐ[R] (IsLocalRing.maximalIdeal R).Fiber S) := by
  intro x
  rcases Ideal.Fiber.exists_smul_eq_one_tmul
      (p := IsLocalRing.maximalIdeal R) (S := S) x with
    ⟨r, hr, s, hs⟩
  have hrunit : IsUnit r := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr
    exact Classical.not_not.mp hr
  rcases hrunit with ⟨u, rfl⟩
  refine ⟨(↑u⁻¹ : R) • s, ?_⟩
  have hs' := congrArg (fun y =>
      (↑u⁻¹ : R) • y) hs
  simpa [Algebra.TensorProduct.includeRight_apply, smul_smul,
    Units.inv_mul, one_smul] using hs'.symm

/-- Over a local base ring, the kernel of the canonical map from an algebra to
the fiber over the maximal ideal is the ideal generated by the maximal ideal of
the base.

This is the Ideal.Fiber form of the residue-field tensor kernel calculation:
S -> (maximalIdeal R).Fiber S has kernel maximalIdeal R * S. -/
theorem maximalIdeal_fiber_includeRight_ker_eq_maximalIdeal_map
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [Algebra R S] :
    RingHom.ker ((Algebra.TensorProduct.includeRight :
      S →ₐ[R] (IsLocalRing.maximalIdeal R).Fiber S) :
        S →+* (IsLocalRing.maximalIdeal R).Fiber S) =
      (IsLocalRing.maximalIdeal R).map (algebraMap R S) := by
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let e : (IsLocalRing.maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ I :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField
        (IsLocalRing.maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
      (IsLocalRing.maximalIdeal R)).symm.restrictScalars _)
  have he_apply (s : S) :
      e ((Algebra.TensorProduct.includeRight :
        S →ₐ[R] (IsLocalRing.maximalIdeal R).Fiber S) s) =
        Ideal.Quotient.mk I s := by
    simpa [e, I, Algebra.TensorProduct.includeRight_apply] using
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul
        (B := S) (I := IsLocalRing.maximalIdeal R) s (1 : R))
  ext s
  constructor
  · intro hs
    have hq :
        e ((Algebra.TensorProduct.includeRight :
          S →ₐ[R] (IsLocalRing.maximalIdeal R).Fiber S) s) = 0 := by
      simpa using congrArg e hs
    rw [he_apply s] at hq
    simpa [I, Ideal.Quotient.eq_zero_iff_mem] using hq
  · intro hs
    change (Algebra.TensorProduct.includeRight :
      S →ₐ[R] (IsLocalRing.maximalIdeal R).Fiber S) s = 0
    apply e.injective
    rw [he_apply s, map_zero]
    simpa [I, Ideal.Quotient.eq_zero_iff_mem] using hs

end ValuedExtension

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_HenselLemma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Factorization-shaped Hensel consequences

Mathlib exposes the simple-root form of Hensel's lemma.  The statements below
turn it into a linear-factor lifting API for a simple residual linear factor.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

/-- The cofactor obtained by dividing by `X - C a` evaluates to the derivative
value at `a`.  This is the polynomial identity behind the simple-root
decomposition over the residual algebra. -/
theorem divByMonic_X_sub_C_eval_eq_derivative_eval
    {S : Type*} [CommRing S] (p : Polynomial S) (a : S) :
    (p /ₘ (Polynomial.X - Polynomial.C a)).eval a =
      p.derivative.eval a := by
  have h :=
    Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
      p a
  have heval := congrArg (fun q : Polynomial S => q.eval a) h
  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub] using
    heval

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_FiniteProductNormTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms and traces on finite dependent products

These algebraic lemmas are the finite-product linear algebra used in
tensor-product norm and trace formulas.  Mathlib has the binary trace formula and the
determinant of a binary product map; the dependent finite-product versions
are recorded here so that the local factors are allowed to have different
field degrees.
-/

noncomputable section

namespace ValuationTheory
namespace Completion

universe u v w

open Module

/-- Reindexing a dependent product is an algebra equivalence. -/
noncomputable def piCongrLeftAlgEquiv
    {R : Type*} [CommSemiring R]
    {ι ι' : Type*} (A : ι' → Type*) [∀ i, Semiring (A i)]
    [∀ i, Algebra R (A i)] (e : ι ≃ ι') :
    ((i : ι) → A (e i)) ≃ₐ[R] ((i' : ι') → A i') where
  __ := RingEquiv.piCongrLeft A e
  commutes' r := by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    change (Equiv.piCongrLeft A e
      (fun i => algebraMap R (A (e i)) r)) (e i) =
        algebraMap R (A (e i)) r
    exact Equiv.piCongrLeft_apply_apply A e _ i

/-- Splitting the `none` coordinate from an `Option`-indexed dependent
product is an algebra equivalence. -/
noncomputable def piOptionEquivProdAlgEquiv
    {R : Type*} [CommSemiring R]
    {ι : Type*} (A : Option ι → Type*) [∀ i, Semiring (A i)]
    [∀ i, Algebra R (A i)] :
    ((i : Option ι) → A i) ≃ₐ[R] (A none × ((i : ι) → A (some i))) where
  __ := RingEquiv.piOptionEquivProd
  commutes' _ := rfl

/-- The algebra trace of an element of a finite dependent product is the
sum of its component traces. -/
theorem algebra_trace_pi_apply
    {R : Type u} [CommRing R]
    {ι : Type v} [Fintype ι]
    (A : ι → Type w) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (x : ∀ i, A i) :
    Algebra.trace R (∀ i, A i) x = ∑ i, Algebra.trace R (A i) (x i) := by
  classical
  let P : ∀ (ι : Type v) [Fintype ι], Prop :=
    fun ι _ =>
      ∀ (A : ι → Type w) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
        [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
        (x : ∀ i, A i),
        Algebra.trace R (∀ i, A i) x =
          ∑ i, Algebra.trace R (A i) (x i)
  apply Fintype.induction_empty_option (P := P)
  · intro α β _ e h A _ _ _ _ x
    let : Fintype α := Fintype.ofEquiv β e.symm
    let E := piCongrLeftAlgEquiv (R := R) A e
    let x' : ∀ i : α, A (e i) := fun i => x (e i)
    have hEx : E x' = x := by
      apply E.symm.injective
      rw [E.symm_apply_apply]
      funext i
      rfl
    calc
      Algebra.trace R (∀ j : β, A j) x =
          Algebra.trace R (∀ i : α, A (e i)) x' := by
        rw [← Algebra.trace_eq_of_algEquiv E x']
        rw [hEx]
      _ = ∑ i : α, Algebra.trace R (A (e i)) (x' i) := h _ _
      _ = ∑ j : β, Algebra.trace R (A j) (x j) := by
        exact Fintype.sum_equiv e _ _ (fun i => rfl)
  · intro A _ _ _ _ x
    simp only [Fintype.sum_empty]
    rw [Algebra.trace_apply]
    let b : Basis (Fin 0) R ((i : PEmpty) → A i) := Basis.empty _
    rw [LinearMap.trace_eq_matrix_trace R b]
    simp [Matrix.trace]
  · intro α _ h A _ _ _ _ x
    let E := piOptionEquivProdAlgEquiv (R := R) A
    let y : A none × ((i : α) → A (some i)) := E x
    calc
      Algebra.trace R (∀ i : Option α, A i) x =
          Algebra.trace R (A none × ((i : α) → A (some i))) y :=
        (Algebra.trace_eq_of_algEquiv E x).symm
      _ = Algebra.trace R (A none) y.1 +
          Algebra.trace R ((i : α) → A (some i)) y.2 :=
        Algebra.trace_prod_apply y
      _ = Algebra.trace R (A none) (x none) +
          ∑ i : α, Algebra.trace R (A (some i)) (x (some i)) := by
        rw [h]
        rfl
      _ = ∑ i : Option α, Algebra.trace R (A i) (x i) := by
        rw [Fintype.sum_option]

end Completion
end ValuationTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_ValuedAdicComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u v

namespace ValuationTheory

/-!
# Adic completeness of complete rank-one discrete valued fields

This file supplies the common source used in the valuation-topology and adic-completeness arguments: on a
rank-one discrete valued field with archimedean ambient value group, the
native topology of the valuation ring is its maximal-ideal adic topology.
Consequently a complete valued field has an adically complete valuation ring.
-/

noncomputable section

namespace Valuations

open _root_.ValuationTheory.DiscreteValuationField

/-- The native subtype topology on the valuation ring of a rank-one discrete
valued field is its maximal-ideal adic topology. -/
theorem rankOneDiscreteValuationSubring_isAdic
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete] :
    IsAdic
      (IsLocalRing.maximalIdeal
        (Valued.v : Valuation K Gamma).valuationSubring) := by
  let val := (Valued.v : Valuation K Gamma)
  let : IsTopologicalRing val.valuationSubring :=
    Subring.instIsTopologicalRing val.valuationSubring.toSubring
  rcases Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial val with
    ⟨pi, hpi⟩
  rw [isAdic_iff]
  constructor
  · intro n
    have h_radius_ne :
        val (((pi ^ n : val.valuationSubring) : K)) ≠ 0 := by
      change val ((pi : K) ^ n) ≠ 0
      rw [map_pow]
      exact pow_ne_zero n hpi.val_ne_zero
    have h_restrict_radius_ne :
        val.restrict (((pi ^ n : val.valuationSubring) : K)) ≠ 0 := by
      simpa using h_radius_ne
    have h_open_ball_restrict : IsOpen
        {x : K |
          val.restrict x ≤
            val.restrict (((pi ^ n : val.valuationSubring) : K))} :=
      Valued.isOpen_closedBall K h_restrict_radius_ne
    have h_open_ball : IsOpen
        {x : K |
          val x ≤ val (((pi ^ n : val.valuationSubring) : K))} := by
      simpa only [val.restrict_le_iff] using h_open_ball_restrict
    have h_preimage_open : IsOpen
        {x : val.valuationSubring |
          val (x : K) ≤ val (((pi ^ n : val.valuationSubring) : K))} :=
      h_open_ball.preimage continuous_subtype_val
    convert h_preimage_open using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact
      (ValuationTheory.DiscreteValuationField.Valuation.mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
          (val := val) (pi := pi) hpi n)
  · intro s hs
    rcases
        (mem_nhds_subtype (val.valuationSubring : Set K)
          (0 : val.valuationSubring) s).1 hs with
      ⟨t, ht, hts⟩
    rcases (Valued.hasBasis_nhds_zero K Gamma).mem_iff.mp ht with
      ⟨gamma, _hgamma, hgamma_t⟩
    let gamma' : Gammaˣ :=
      Units.map
        (MonoidWithZeroHom.ValueGroup₀.embedding (f := (.ofClass val)))
        gamma
    rcases exists_pow_lt
        (Valuation.IsRankOneDiscrete.generator_lt_one val)
        gamma' with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro x hx
    apply hts
    apply hgamma_t
    change val.restrict (x : K) < gamma.1
    rw [Valuation.restrict_lt_iff_lt_embedding]
    have hx_le :=
      (ValuationTheory.DiscreteValuationField.Valuation.mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
          (val := val) (pi := pi) hpi n).1 hx
    calc
      val (x : K) ≤ val (((pi ^ n : val.valuationSubring) : K)) := hx_le
      _ = ((Valuation.IsRankOneDiscrete.generator val) ^ n : Gamma) := by
            simp [map_pow, hpi.val]
      _ < MonoidWithZeroHom.ValueGroup₀.embedding (f := (.ofClass val)) gamma.1 := by
        have hn_coe := Units.val_lt_val.mp hn
        change
          ((Valuation.IsRankOneDiscrete.generator val : Gammaˣ) : Gamma) ^ n <
            MonoidWithZeroHom.ValueGroup₀.embedding
              (f := (.ofClass val)) gamma.1 at hn_coe
        exact hn_coe

/-- Completeness of a rank-one discrete valued field produces adic
completeness of its valuation ring; no adic-completeness assumption is
exposed. -/
theorem rankOneDiscreteValuationSubring_isAdicComplete
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma] [MulArchimedean Gamma]
    [Valued K Gamma]
    [(Valued.v : Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K] :
    IsAdicComplete
      (IsLocalRing.maximalIdeal
        (Valued.v : Valuation K Gamma).valuationSubring)
      (Valued.v : Valuation K Gamma).valuationSubring := by
  let val := (Valued.v : Valuation K Gamma)
  let : IsUniformAddGroup val.valuationSubring :=
    val.valuationSubring.toAddSubgroup.isUniformAddGroup
  let : IsTopologicalRing val.valuationSubring :=
    Subring.instIsTopologicalRing val.valuationSubring.toSubring
  let : CompleteSpace val.valuationSubring :=
    (Valued.isClosed_valuationSubring K).completeSpace_coe
  exact rankOneDiscreteValuationSubring_isAdic.isAdicComplete_iff.2
    ⟨inferInstance, inferInstance⟩

end Valuations
end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral lattices in relative tensor coordinates

This module chooses a common integral scale for a field basis, constructs the
associated integer lattice, and isolates the finite set of primes where its
local integrality properties can fail.
-/

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The canonical `𝓞 K`-linear inclusion `𝓞 L → L`. -/
noncomputable def ringOfIntegersToFieldLinearMap :
    𝓞 L →ₗ[𝓞 K] L :=
  (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- The inclusion `𝓞 L → L` used above is injective. -/
theorem ringOfIntegersToFieldLinearMap_injective :
    Function.Injective
      (ringOfIntegersToFieldLinearMap
        (K := K) (L := L)) := by
  intro x y h
  exact NumberField.RingOfIntegers.ext h
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_FinitePlaceCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place completion maps for relative tensor factors

This module compares the absolute-value and adic-completion models at finite
places and records how the resulting maps preserve norms and integrality.
-/

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Membership in the concrete finite-place valuation ring implies the
usual norm bound. -/
theorem norm_le_one_of_mem_adicCompletionIntegers
    (w : HeightOneSpectrum (𝓞 K))
    {x : w.adicCompletion K}
    (hx : x ∈ w.adicCompletionIntegers K) :
    ‖x‖ ≤ 1 := by
  rw [FinitePlace.norm_def]
  exact_mod_cast
    (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w)).2 hx

/-- The concrete adic completion integers are exactly the elements of
norm at most one. -/
theorem mem_adicCompletionIntegers_of_norm_le_one
    (w : HeightOneSpectrum (𝓞 K))
    {x : w.adicCompletion K}
    (hx : ‖x‖ ≤ 1) :
    x ∈ w.adicCompletionIntegers K := by
  rw [FinitePlace.norm_def] at hx
  exact_mod_cast
    (WithZeroMulInt.toNNReal_le_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w)).1 hx

omit [NumberField L] in
/-- The trace matrix of the tensor-product basis is obtained from the
original trace matrix by scalar extension. -/
theorem trace_tensorProduct_basis_mul
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K L)
    (A : Type*) [Field A] [Algebra K A]
    (i j : ι) :
    Algebra.trace A (A ⊗[K] L)
        ((Algebra.TensorProduct.basis A b i) *
          (Algebra.TensorProduct.basis A b j)) =
      algebraMap K A (Algebra.trace K L (b i * b j)) := by
  simp only [Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  change LinearMap.trace A (A ⊗[K] L)
      (Algebra.lmul A (A ⊗[K] L) (1 ⊗ₜ[K] (b i * b j))) =
    _
  rw [← Algebra.baseChange_lmul]
  exact LinearMap.trace_baseChange (Algebra.lmul K L (b i * b j)) A

omit [NumberField L] in
/-- Discriminants of tensor-product bases commute with scalar
extension. -/
theorem discr_tensorProduct_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L)
    (A : Type*) [Field A] [Algebra K A] :
    Algebra.discr A (Algebra.TensorProduct.basis A b) =
      algebraMap K A (Algebra.discr K b) := by
  rw [Algebra.discr_def, Algebra.discr_def]
  rw [(algebraMap K A).map_det]
  congr 1
  ext i j
  exact trace_tensorProduct_basis_mul b A i j
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_RestrictedAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Galois action on the restricted local product

The Galois action on `𝔸_K ⊗[K] L` commutes with evaluation at every
place.  Consequently the exact restricted-product equivalence for
relative ideles is equivariant, and the transported action is the
coordinatewise tensor-conjugation action.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


universe u v w

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

section ScalarTensor

variable
    {A : Type w} [CommRing A] [Algebra K A]

/-- Conjugation on the second factor of an arbitrary scalar extension
`A ⊗[K] L`. -/
noncomputable def scalarTensorConjugation
    (σ : L ≃ₐ[K] L) :
    A ⊗[K] L ≃ₐ[A] A ⊗[K] L := by
  let f : A ⊗[K] L →ₐ[A] A ⊗[K] L :=
    Algebra.TensorProduct.map
      (AlgHom.id A A) σ.toAlgHom
  let g : A ⊗[K] L →ₐ[A] A ⊗[K] L :=
    Algebra.TensorProduct.map
      (AlgHom.id A A) σ.symm.toAlgHom
  exact AlgEquiv.ofAlgHom f g
    (by ext x; simp [f, g])
    (by ext x; simp [f, g])

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
@[simp]
theorem scalarTensorConjugation_tmul
    (σ : L ≃ₐ[K] L) (a : A) (x : L) :
    scalarTensorConjugation
        (K := K) (L := L) (A := A) σ
        (a ⊗ₜ[K] x) =
      a ⊗ₜ[K] σ x :=
  rfl

end ScalarTensor
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_NormalClosure
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

/-- The normal closure of `L / K`, constructed inside a fixed
algebraic closure of `K`. -/
abbrev finiteNormalClosure :=
  IntermediateField.normalClosure K L (AlgebraicClosure K)

noncomputable instance finiteNormalClosure_numberField :
    NumberField (finiteNormalClosure K L) :=
  NumberField.of_module_finite K (finiteNormalClosure K L)

noncomputable instance finiteNormalClosure_isGalois :
    IsGalois K (finiteNormalClosure K L) := by
  let f : L →ₐ[K] AlgebraicClosure K :=
    IsAlgClosed.lift
  let : Algebra L (AlgebraicClosure K) :=
    f.toRingHom.toAlgebra
  let : IsScalarTower K L (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq'
      f.comp_algebraMap.symm
  infer_instance

/-- A fixed embedding of `L` into its normal closure. -/
noncomputable def finiteNormalClosureEmbedding :
    L →ₐ[K] finiteNormalClosure K L :=
  let f : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  f.codRestrict
    (IntermediateField.normalClosure K L
      (AlgebraicClosure K)).toSubalgebra
    (fun x =>
      f.fieldRange_le_normalClosure
        (show f x ∈ f.fieldRange from ⟨x, rfl⟩))
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_GaloisAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Galois actions on `S`-units and their logarithmic lattice

This file supplies the equivariant input for the `S`-unit calculation. A Galois
automorphism acts on finite places through its restriction to the ring of
integers, on infinite places by precomposition, and on field units in the
usual way.  For a stable finite set of finite places these actions restrict
to the actual `S`-unit group.
-/

open scoped BigOperators Classical NumberField nonZeroDivisors
open IsDedekindDomain Module

noncomputable section

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The permutation of finite places induced by a Galois automorphism. -/
noncomputable def finitePlaceEquiv
    (σ : L ≃ₐ[K] L) :
    HeightOneSpectrum (𝓞 L) ≃
      HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.equivOfRingEquiv
    (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv

/-- Transport of ideals along a ring automorphism, as a multiplicative
equivalence. -/
noncomputable def idealMapMulEquiv
    {R : Type*} [CommRing R]
    (e : R ≃+* R) : Ideal R ≃* Ideal R where
  toFun I := I.map e
  invFun I := I.map e.symm
  left_inv _ := Ideal.map_of_equiv e
  right_inv _ := Ideal.map_of_equiv e.symm
  map_mul' I J := Ideal.map_mul e I J

@[simp]
theorem idealMapMulEquiv_apply
    {R : Type*} [CommRing R]
    (e : R ≃+* R) (I : Ideal R) :
    idealMapMulEquiv e I = I.map e :=
  rfl

omit [NumberField K] [NumberField L] in
@[simp]
theorem finitePlaceEquiv_asIdeal
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L)) :
    (finitePlaceEquiv K L σ v).asIdeal =
      v.asIdeal.map
        (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv := by
  ext x
  exact Ideal.symm_apply_mem_of_equiv_iff

omit [NumberField K] [NumberField L] in
@[simp]
theorem finitePlaceEquiv_one
    (v : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv K L (1 : L ≃ₐ[K] L) v = v := by
  apply HeightOneSpectrum.ext
  ext x
  change
    NumberField.RingOfIntegers.mapRingHom (1 : L ≃ₐ[K] L).symm.toRingHom x ∈
        v.asIdeal ↔
      x ∈ v.asIdeal
  have hx :
      NumberField.RingOfIntegers.mapRingHom (1 : L ≃ₐ[K] L).symm.toRingHom x =
        x := by
    apply NumberField.RingOfIntegers.ext
    rfl
  rw [hx]

omit [NumberField K] [NumberField L] in
@[simp]
theorem finitePlaceEquiv_mul
    (σ τ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv K L (σ * τ) v =
      finitePlaceEquiv K L σ
        (finitePlaceEquiv K L τ v) := by
  apply HeightOneSpectrum.ext
  ext x
  change
    NumberField.RingOfIntegers.mapRingHom (σ * τ).symm.toRingHom x ∈
        v.asIdeal ↔
      NumberField.RingOfIntegers.mapRingHom τ.symm.toRingHom
          (NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom x) ∈
        v.asIdeal
  have hx :
      NumberField.RingOfIntegers.mapRingHom (σ * τ).symm.toRingHom x =
        NumberField.RingOfIntegers.mapRingHom τ.symm.toRingHom
          (NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom x) := by
    apply NumberField.RingOfIntegers.ext
    rfl
  rw [hx]

omit [NumberField K] [NumberField L] in
@[simp]
theorem finitePlaceEquiv_inv_apply
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L)) :
    finitePlaceEquiv K L σ
        (finitePlaceEquiv K L σ⁻¹ v) = v := by
  rw [← finitePlaceEquiv_mul]
  simp

/-- The actual Galois action on finite places of `L`. -/
@[reducible]
noncomputable def finitePlaceMulAction :
    MulAction (L ≃ₐ[K] L)
      (HeightOneSpectrum (𝓞 L)) where
  smul σ v := finitePlaceEquiv K L σ v
  one_smul := finitePlaceEquiv_one K L
  mul_smul := finitePlaceEquiv_mul K L

section FinitePlaceAction

local instance instMulActionAlgEquivHeightOneSpectrumRingOfIntegers_solutions :
    MulAction (L ≃ₐ[K] L)
      (HeightOneSpectrum (𝓞 L)) :=
  finitePlaceMulAction K L

omit [NumberField K] [NumberField L] in
@[simp]
theorem finitePlace_smul_def
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L)) :
    σ • v = finitePlaceEquiv K L σ v :=
  rfl

end FinitePlaceAction
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_Dedekind_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Hilbert ramification theory: Dedekind-domain layer

This file manages the Dedekind-domain part of Hilbert ramification theory in
prime-decomposition theory.

The implementation uses mathlib's ramification/inertia theorems where those
are already the source proof, but the decomposition/inertia/residue-action
interface is proved here: membership criteria, residue-action formula,
normality of inertia in the decomposition group, exactness, and quotient form.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open scoped Pointwise
open Algebra Module

attribute [local instance] Ideal.Quotient.field

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The valuation-conjugacy theorem:
the Galois group acts transitively on primes over a fixed prime. -/
theorem exists_smul_eq_of_isGaloisGroup
    (p : Ideal A) (P Q : Ideal B)
    [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    ∃ σ : G, σ • P = Q := by
  exact Ideal.exists_smul_eq_of_isGaloisGroup p P Q G

end Dedekind
end HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_Dedekind_PrimeContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Hilbert ramification theory: number-field prime contractions

This file specializes the fixed fields `Z_P` and `T_P` to rings of integers
of number fields and defines the contracted primes `p`, `P_Z`, and `P_T`.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open Algebra NumberField
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

variable {K L : Type*}
variable [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (G : Type*) [Group G] [MulSemiringAction G L] [SMulCommClass G K L]

/-- The contraction of a maximal finite prime of a number-field ring of
integers to a subfield ring of integers is nonzero. -/
theorem ringOfIntegers_under_ne_bot
    {E F : Type*} [Field E] [Field F] [NumberField E] [NumberField F]
    [Algebra E F] (P : Ideal (𝓞 F)) [P.IsMaximal] :
    P.under (𝓞 E) ≠ ⊥ := by
  exact
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := P.under (𝓞 E)) inferInstance
      (RingOfIntegers.not_isField E)

/-- prime-decomposition theory:
`p = P ∩ O_K`, the prime ideal of the base number field below `P`. -/
abbrev basePrime
    (P : Ideal (𝓞 L)) :
    Ideal (𝓞 K) :=
  P.under (𝓞 K)

/-- The contracted base prime is prime. -/
instance basePrime_isPrime
    (P : Ideal (𝓞 L)) [P.IsPrime] :
    (basePrime (K := K) P).IsPrime :=
  inferInstance

end Dedekind
end HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_ExtensionIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite places in a number-field extension

This file supplies the finite-place index comparison needed to pass from
the relative adelic tensor product to the ordinary adeles of the extension
field.  It is deliberately independent of the restricted-product
construction.

For a finite place `W` of `L`, `finitePlaceBelow W` is its contraction to
`K`.  Conversely, an exact extension of the normalized absolute value at
`v` has a canonical centre in `𝓞 L`.  Passing through the finite normal
closure shows that the centres are precisely the finite places above `v`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

universe u v w

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- Contraction of a finite place of `L` to a finite place of `K`. -/
noncomputable def finitePlaceBelow
    (W : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum (𝓞 K) where
  asIdeal := W.asIdeal.under (𝓞 K)
  isPrime := inferInstance
  ne_bot :=
    HilbertRamification.Dedekind.ringOfIntegers_under_ne_bot
      (E := K) (F := L) W.asIdeal

@[simp]
theorem finitePlaceBelow_asIdeal
    (W : HeightOneSpectrum (𝓞 L)) :
    (finitePlaceBelow (K := K) W).asIdeal =
      W.asIdeal.under (𝓞 K) :=
  rfl

/-- Contracting a finite place along the identity extension fixes it. -/
@[simp]
theorem finitePlaceBelow_self
    (W : HeightOneSpectrum (𝓞 K)) :
    finitePlaceBelow (K := K) W = W := by
  apply HeightOneSpectrum.ext
  change
    W.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K)) =
      W.asIdeal
  rw [Algebra.algebraMap_self, Ideal.comap_id]

section Tower

variable {M : Type w}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]

/-- Contraction of finite places is transitive in a tower of number
fields. -/
@[simp]
theorem finitePlaceBelow_finitePlaceBelow
    (W : HeightOneSpectrum (𝓞 L)) :
    finitePlaceBelow (K := K)
        (finitePlaceBelow (K := M) W) =
      finitePlaceBelow (K := K) W := by
  apply HeightOneSpectrum.ext
  exact
    Ideal.under_under
      (A := 𝓞 K) (B := 𝓞 M) (C := 𝓞 L) W.asIdeal

end Tower
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_FiniteRestrictedProductBaseChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite restricted products under scalar extension

This file flattens the finite local tensor factors of a relative idele over
`K` into the ordinary finite-place factors of `L`.  The local map is
The canonical local tensor decomposition followed by the comparison between an exact-extension
completion and the concrete adic completion at its centre.

The main point is restrictedness: coefficientwise restrictedness in a fixed
`K`-basis of `L` is equivalent, up to the already isolated finite comparison
set, to the usual valuation-ring-unit condition at almost every finite place
of `L`.
-/

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Reindex a dependent product along an equivalence, retaining its
coordinatewise multiplicative structure. -/
noncomputable def piCongrLeftMulEquiv
    {ι ι' : Type*} (M : ι' → Type*)
    [∀ i, Mul (M i)] (e : ι ≃ ι') :
    (∀ i, M (e i)) ≃* ∀ j, M j where
  toEquiv := Equiv.piCongrLeft M e
  map_mul' f g := by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    change
      Equiv.piCongrLeft M e (f * g) (e i) =
        Equiv.piCongrLeft M e f (e i) *
          Equiv.piCongrLeft M e g (e i)
    rw [Equiv.piCongrLeft_apply_apply,
      Equiv.piCongrLeft_apply_apply,
      Equiv.piCongrLeft_apply_apply]
    rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_InfinitePlaceTensorBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Archimedean relative-idele factors as induced local blocks

The concrete archimedean completion `w.Completion` used by the adele
library is canonically the completion of the underlying absolute value
`w.1`.  Base change along this equivalence connects the actual
archimedean component of a relative idele to the local tensor block of
the local tensor decomposition, equivariantly for the full Galois action.
-/

open scoped NumberField TensorProduct NumberField.LiesOver
open NumberField

noncomputable section

open HilbertRamification

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The wrapper completion at an infinite place as a `K`-algebra
equivalence with the underlying absolute-value completion. -/
def infinitePlaceCompletionAlgEquiv
    (w : InfinitePlace K) :
    w.Completion ≃ₐ[K] w.1.Completion where
  __ := InfinitePlace.Completion.equiv w
  commutes' _ := rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCoreBase_ProductArgument
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The two-variable formal logarithm product argument

This module defines `X + Y + XY`, its logarithmic substitution, and the
support description needed for the formal product formula.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- The two-variable argument of the product formula:
`(1 + X) * (1 + Y) - 1 = X + Y + X*Y`. -/
def formalLogOnePlusProductArgument
    (A : Type*) [CommRing A] : MvPowerSeries (Fin 2) A :=
  MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2) +
    MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)

/--
Establishes the identity `formalLogOnePlusProductArgument A = (1 + MvPowerSeries.X (0 : Fin 2)) *
(1 + MvPowerSeries.X (1 : Fin 2)) - 1`.
-/
theorem formalLogOnePlusProductArgument_eq_mul_sub_one
    (A : Type*) [CommRing A] :
    formalLogOnePlusProductArgument A =
      (1 + MvPowerSeries.X (0 : Fin 2)) *
          (1 + MvPowerSeries.X (1 : Fin 2)) - 1 := by
  let X0 : MvPowerSeries (Fin 2) A := MvPowerSeries.X (0 : Fin 2)
  let X1 : MvPowerSeries (Fin 2) A := MvPowerSeries.X (1 : Fin 2)
  change X0 + X1 + X0 * X1 = (1 + X0) * (1 + X1) - 1
  ring

/--
Establishes the identity `MvPowerSeries.constantCoeff (formalLogOnePlusProductArgument A) = 0`.
-/
theorem formalLogOnePlusProductArgument_constantCoeff
    (A : Type*) [CommRing A] :
    MvPowerSeries.constantCoeff (formalLogOnePlusProductArgument A) = 0 := by
  rw [formalLogOnePlusProductArgument_eq_mul_sub_one]
  simp [MvPowerSeries.constantCoeff_X]

/--
The formal product argument has zero constant coefficient, so it admits substitution into the
logarithm power series.
-/
theorem formalLogOnePlusProductArgument_hasSubst
    (A : Type*) [CommRing A] :
    PowerSeries.HasSubst (formalLogOnePlusProductArgument A) :=
  PowerSeries.HasSubst.of_constantCoeff_zero
    (formalLogOnePlusProductArgument_constantCoeff A)

/--
Establishes the identity `MvPowerSeries.coeff e (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1
: Fin 2) : MvPowerSeries (Fin 2) A) = if e = Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 :
Fin 2) 1 then 1 else 0`.
-/
theorem formalLogOnePlusProductArgument_mulVariables_coeff
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
        (MvPowerSeries.X (0 : Fin 2) *
          MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) =
      if e =
          Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1
      then 1 else 0 := by
  change MvPowerSeries.coeff e
      (MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) 1) (1 : A) *
        MvPowerSeries.monomial (Finsupp.single (1 : Fin 2) 1) (1 : A)) =
    if e =
        Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1
    then 1 else 0
  rw [MvPowerSeries.monomial_mul_monomial]
  simp [MvPowerSeries.coeff_monomial]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductArgument A) = (if e =
Finsupp.single (0 : Fin 2) 1 then 1 else 0) + (if e = Finsupp.single (1 : Fin 2) 1 then 1 else 0)
+ (if e = Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 then 1 else 0)`.
-/
theorem formalLogOnePlusProductArgument_coeff
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (formalLogOnePlusProductArgument A) =
      (if e = Finsupp.single (0 : Fin 2) 1 then 1 else 0) +
        (if e = Finsupp.single (1 : Fin 2) 1 then 1 else 0) +
          (if e =
              Finsupp.single (0 : Fin 2) 1 +
                Finsupp.single (1 : Fin 2) 1
            then 1 else 0) := by
  simp [formalLogOnePlusProductArgument, MvPowerSeries.coeff_X,
    formalLogOnePlusProductArgument_mulVariables_coeff]

/-- Establishes the inequality `Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single (1 : Fin 2) 1`. -/
theorem finsupp_fin_two_single_left_ne_single_right :
    Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single (1 : Fin 2) 1 := by
  intro h
  have hcoord := congrArg (fun e : Fin 2 →₀ ℕ => e (0 : Fin 2)) h
  simp at hcoord

/--
Establishes the inequality `Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single (0 : Fin 2) 1 +
Finsupp.single (1 : Fin 2) 1`.
-/
theorem finsupp_fin_two_single_left_ne_mixed :
    Finsupp.single (0 : Fin 2) 1 ≠
      Finsupp.single (0 : Fin 2) 1 +
        Finsupp.single (1 : Fin 2) 1 := by
  intro h
  have hcoord := congrArg (fun e : Fin 2 →₀ ℕ => e (1 : Fin 2)) h
  simp at hcoord

/--
Establishes the inequality `Finsupp.single (1 : Fin 2) 1 ≠ Finsupp.single (0 : Fin 2) 1 +
Finsupp.single (1 : Fin 2) 1`.
-/
theorem finsupp_fin_two_single_right_ne_mixed :
    Finsupp.single (1 : Fin 2) 1 ≠
      Finsupp.single (0 : Fin 2) 1 +
        Finsupp.single (1 : Fin 2) 1 := by
  intro h
  have hcoord := congrArg (fun e : Fin 2 →₀ ℕ => e (0 : Fin 2)) h
  simp at hcoord

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)
(formalLogOnePlusProductArgument A) = 1`.
-/
@[simp] theorem formalLogOnePlusProductArgument_coeff_single_left
    (A : Type*) [CommRing A] :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)
        (formalLogOnePlusProductArgument A) = 1 := by
  rw [formalLogOnePlusProductArgument_coeff]
  simp [finsupp_fin_two_single_left_ne_single_right]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)
(formalLogOnePlusProductArgument A) = 1`.
-/
@[simp] theorem formalLogOnePlusProductArgument_coeff_single_right
    (A : Type*) [CommRing A] :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)
        (formalLogOnePlusProductArgument A) = 1 := by
  rw [formalLogOnePlusProductArgument_coeff]
  have hrightLeft :
      Finsupp.single (1 : Fin 2) 1 ≠
        Finsupp.single (0 : Fin 2) 1 :=
    finsupp_fin_two_single_left_ne_single_right.symm
  simp [hrightLeft]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 :
Fin 2) 1) (formalLogOnePlusProductArgument A) = 1`.
-/
@[simp] theorem formalLogOnePlusProductArgument_coeff_mixed
    (A : Type*) [CommRing A] :
    MvPowerSeries.coeff
        (Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1)
        (formalLogOnePlusProductArgument A) = 1 := by
  rw [formalLogOnePlusProductArgument_coeff]
  have hmixedLeft :
      Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1 ≠
        Finsupp.single (0 : Fin 2) 1 :=
    finsupp_fin_two_single_left_ne_mixed.symm
  have hmixedRight :
      Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1 ≠
        Finsupp.single (1 : Fin 2) 1 :=
    finsupp_fin_two_single_right_ne_mixed.symm
  simp [hmixedLeft, hmixedRight]


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCoreBase_BasicFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Basic factors in the formal logarithm product argument

This module packages the three possible nonzero monomial factors and their
finite choice spaces.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- The three exponent vectors with nonzero coefficient in `X + Y + XY`. -/
def formalLogOnePlusProductArgumentBasicFactor
    (m : Fin 2 →₀ ℕ) : Prop :=
  m = Finsupp.single (0 : Fin 2) 1 ∨
    m = Finsupp.single (1 : Fin 2) 1 ∨
      m =
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1

/-- The finite set of the left, right, and mixed basic exponent vectors. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorFinset :
    Finset (Fin 2 →₀ ℕ) := by
  classical
  exact
    {Finsupp.single (0 : Fin 2) 1,
      Finsupp.single (1 : Fin 2) 1,
      Finsupp.single (0 : Fin 2) 1 +
        Finsupp.single (1 : Fin 2) 1}

/--
Characterizes `m ∈ formalLogOnePlusProductArgumentBasicFactorFinset` by the equivalent condition
`formalLogOnePlusProductArgumentBasicFactor m`.
-/
theorem mem_formalLogOnePlusProductArgumentBasicFactorFinset
    {m : Fin 2 →₀ ℕ} :
    m ∈ formalLogOnePlusProductArgumentBasicFactorFinset ↔
      formalLogOnePlusProductArgumentBasicFactor m := by
  classical
  simp [formalLogOnePlusProductArgumentBasicFactorFinset,
    formalLogOnePlusProductArgumentBasicFactor]

/-- Establishes the identity `formalLogOnePlusProductArgumentBasicFactorFinset.card = 3`. -/
@[simp] theorem formalLogOnePlusProductArgumentBasicFactorFinset_card :
    formalLogOnePlusProductArgumentBasicFactorFinset.card = 3 := by
  classical
  simp [formalLogOnePlusProductArgumentBasicFactorFinset,
    finsupp_fin_two_single_left_ne_single_right]

/-- Labels the left, right, and mixed basic factors by `0`, `1`, and `2`.
Non-basic inputs receive the mixed label; all uses that recover a factor from
its label therefore carry a basic-factor hypothesis. -/
def formalLogOnePlusProductArgumentBasicFactorLabel
    (m : Fin 2 →₀ ℕ) : Fin 3 :=
  if m = Finsupp.single (0 : Fin 2) 1 then 0
  else if m = Finsupp.single (1 : Fin 2) 1 then 1
  else 2

/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabel (Finsupp.single (0 : Fin
2) 1) = 0`.
-/
@[simp] theorem formalLogOnePlusProductArgumentBasicFactorLabel_left :
    formalLogOnePlusProductArgumentBasicFactorLabel
        (Finsupp.single (0 : Fin 2) 1) = 0 := by
  simp [formalLogOnePlusProductArgumentBasicFactorLabel]

/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabel (Finsupp.single (1 : Fin
2) 1) = 1`.
-/
@[simp] theorem formalLogOnePlusProductArgumentBasicFactorLabel_right :
    formalLogOnePlusProductArgumentBasicFactorLabel
        (Finsupp.single (1 : Fin 2) 1) = 1 := by
  simp [formalLogOnePlusProductArgumentBasicFactorLabel,
    finsupp_fin_two_single_left_ne_single_right.symm]

/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabel (Finsupp.single (0 : Fin
2) 1 + Finsupp.single (1 : Fin 2) 1) = 2`.
-/
@[simp] theorem formalLogOnePlusProductArgumentBasicFactorLabel_mixed :
    formalLogOnePlusProductArgumentBasicFactorLabel
        (Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1) = 2 := by
  simp [formalLogOnePlusProductArgumentBasicFactorLabel,
    finsupp_fin_two_single_left_ne_mixed.symm,
    finsupp_fin_two_single_right_ne_mixed.symm]

/--
Characterizes `formalLogOnePlusProductArgumentBasicFactorLabel m = (0 : Fin 3)` by the equivalent
condition `m = Finsupp.single (0 : Fin 2) 1`.
-/
theorem formalLogOnePlusProductArgumentBasicFactorLabel_eq_zero
    {m : Fin 2 →₀ ℕ} :
    formalLogOnePlusProductArgumentBasicFactorLabel m = (0 : Fin 3) ↔
      m = Finsupp.single (0 : Fin 2) 1 := by
  unfold formalLogOnePlusProductArgumentBasicFactorLabel
  by_cases hleft : m = Finsupp.single (0 : Fin 2) 1
  · simp [hleft]
  · by_cases hright : m = Finsupp.single (1 : Fin 2) 1
    · simp [hright]
    · simp [hleft, hright]

/-- Finitely supported sequences of `q` basic factors. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorProductChoices
    (q : ℕ) : Finset (ℕ →₀ (Fin 2 →₀ ℕ)) := by
  classical
  exact
    (Finset.range q).finsupp
      (fun _ => formalLogOnePlusProductArgumentBasicFactorFinset)

/-- Sequences of `q` basic factors whose exponent-vector sum is `e`. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorChoices
    (q : ℕ) (e : Fin 2 →₀ ℕ) :
    Finset (ℕ →₀ (Fin 2 →₀ ℕ)) := by
  classical
  exact
    (Finset.finsuppAntidiag (Finset.range q) e).filter
      (fun l : ℕ →₀ (Fin 2 →₀ ℕ) =>
        ∀ i ∈ Finset.range q,
          formalLogOnePlusProductArgumentBasicFactor (l i))

/-- The number of left factors among the first `q` entries of `l`. -/
def formalLogOnePlusProductArgumentLeftChoiceCount
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : ℕ :=
  ∑ i ∈ Finset.range q,
    if l i = Finsupp.single (0 : Fin 2) 1 then 1 else 0

/-- The number of right factors among the first `q` entries of `l`. -/
def formalLogOnePlusProductArgumentRightChoiceCount
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : ℕ :=
  ∑ i ∈ Finset.range q,
    if l i = Finsupp.single (1 : Fin 2) 1 then 1 else 0

/-- The number of mixed factors among the first `q` entries of `l`. -/
def formalLogOnePlusProductArgumentMixedChoiceCount
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : ℕ :=
  ∑ i ∈ Finset.range q,
    if l i =
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1
    then 1 else 0

/-- The number of entries among the first `q` positions with label `j`. -/
def formalLogOnePlusProductArgumentBasicFactorLabelCount
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) (j : Fin 3) : ℕ :=
  ∑ i ∈ Finset.range q,
    if formalLogOnePlusProductArgumentBasicFactorLabel (l i) = j
    then 1 else 0

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l =
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0`.
-/
theorem formalLogOnePlusProductArgument_leftChoiceCount_eq_labelCount_zero
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) :
    formalLogOnePlusProductArgumentLeftChoiceCount q l =
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 := by
  classical
  rw [formalLogOnePlusProductArgumentLeftChoiceCount,
    formalLogOnePlusProductArgumentBasicFactorLabelCount]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hleft : l i = Finsupp.single (0 : Fin 2) 1
  · simp [hleft]
  · have hlabel :
        formalLogOnePlusProductArgumentBasicFactorLabel (l i) ≠
          (0 : Fin 3) := by
      intro hzero
      exact hleft
        (formalLogOnePlusProductArgumentBasicFactorLabel_eq_zero.1 hzero)
    simp [hleft, hlabel]


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCoreBase_ChoiceCountSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Coordinate equations for basic-factor choices

This module derives the three coordinate and total-count equations satisfied by
a choice of the basic factors in `X + Y + XY`.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- Basic-factor sequences with the three label counts forced by `q` and the
target exponent vector `e`. -/
noncomputable def formalLogOnePlusProductArgumentBasicFactorLabelCountChoices
    (q : ℕ) (e : Fin 2 →₀ ℕ) :
    Finset (ℕ →₀ (Fin 2 →₀ ℕ)) :=
  (formalLogOnePlusProductArgumentBasicFactorProductChoices q).filter
    (fun l =>
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 =
          q - e (1 : Fin 2) ∧
        formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 =
          q - e (0 : Fin 2) ∧
          formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 =
            e (0 : Fin 2) + e (1 : Fin 2) - q)

/--
Establishes the identity `m (0 : Fin 2) = (if m = Finsupp.single (0 : Fin 2) 1 then 1 else 0) +
(if m = Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 then 1 else 0)`.
-/
theorem formalLogOnePlusProductArgumentBasicFactor_left_coord
    {m : Fin 2 →₀ ℕ}
    (hm : formalLogOnePlusProductArgumentBasicFactor m) :
    m (0 : Fin 2) =
      (if m = Finsupp.single (0 : Fin 2) 1 then 1 else 0) +
        (if m =
            Finsupp.single (0 : Fin 2) 1 +
              Finsupp.single (1 : Fin 2) 1
          then 1 else 0) := by
  rcases hm with hleft | hright | hmixed
  · simp [hleft]
  · have hrightLeft :
        Finsupp.single (1 : Fin 2) 1 ≠
          Finsupp.single (0 : Fin 2) 1 :=
      finsupp_fin_two_single_left_ne_single_right.symm
    simp [hright, hrightLeft]
  · have hmixedLeft :
        Finsupp.single (0 : Fin 2) 1 +
            Finsupp.single (1 : Fin 2) 1 ≠
          Finsupp.single (0 : Fin 2) 1 :=
      finsupp_fin_two_single_left_ne_mixed.symm
    simp [hmixed, hmixedLeft]

/--
Establishes the identity `m (1 : Fin 2) = (if m = Finsupp.single (1 : Fin 2) 1 then 1 else 0) +
(if m = Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 then 1 else 0)`.
-/
theorem formalLogOnePlusProductArgumentBasicFactor_right_coord
    {m : Fin 2 →₀ ℕ}
    (hm : formalLogOnePlusProductArgumentBasicFactor m) :
    m (1 : Fin 2) =
      (if m = Finsupp.single (1 : Fin 2) 1 then 1 else 0) +
        (if m =
            Finsupp.single (0 : Fin 2) 1 +
              Finsupp.single (1 : Fin 2) 1
          then 1 else 0) := by
  rcases hm with hleft | hright | hmixed
  · simp [hleft, finsupp_fin_two_single_left_ne_single_right]
  · simp [hright]
  · have hmixedRight :
        Finsupp.single (0 : Fin 2) 1 +
            Finsupp.single (1 : Fin 2) 1 ≠
          Finsupp.single (1 : Fin 2) 1 :=
      finsupp_fin_two_single_right_ne_mixed.symm
    simp [hmixed, hmixedRight]

/--
Establishes the identity `(if m = Finsupp.single (0 : Fin 2) 1 then 1 else 0) + (if m =
Finsupp.single (1 : Fin 2) 1 then 1 else 0) + (if m = Finsupp.single (0 : Fin 2) 1 +
Finsupp.single (1 : Fin 2) 1 then 1 else 0) = 1`.
-/
theorem formalLogOnePlusProductArgumentBasicFactor_total_indicator
    {m : Fin 2 →₀ ℕ}
    (hm : formalLogOnePlusProductArgumentBasicFactor m) :
    (if m = Finsupp.single (0 : Fin 2) 1 then 1 else 0) +
          (if m = Finsupp.single (1 : Fin 2) 1 then 1 else 0) +
        (if m =
            Finsupp.single (0 : Fin 2) 1 +
              Finsupp.single (1 : Fin 2) 1
          then 1 else 0) =
      1 := by
  rcases hm with hleft | hright | hmixed
  · simp [hleft, finsupp_fin_two_single_left_ne_single_right]
  · have hrightLeft :
        Finsupp.single (1 : Fin 2) 1 ≠
          Finsupp.single (0 : Fin 2) 1 :=
      finsupp_fin_two_single_left_ne_single_right.symm
    simp [hright, hrightLeft]
  · have hmixedLeft :
        Finsupp.single (0 : Fin 2) 1 +
            Finsupp.single (1 : Fin 2) 1 ≠
          Finsupp.single (0 : Fin 2) 1 :=
      finsupp_fin_two_single_left_ne_mixed.symm
    have hmixedRight :
        Finsupp.single (0 : Fin 2) 1 +
            Finsupp.single (1 : Fin 2) 1 ≠
          Finsupp.single (1 : Fin 2) 1 :=
      finsupp_fin_two_single_right_ne_mixed.symm
    simp [hmixed, hmixedLeft, hmixedRight]

/--
Establishes the identity `(∑ i ∈ Finset.range q, l i (0 : Fin 2)) =
formalLogOnePlusProductArgumentLeftChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l`.
-/
theorem formalLogOnePlusProductArgument_leftCoord_sum_eq_choiceCounts
    {q : ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    (∑ i ∈ Finset.range q, l i (0 : Fin 2)) =
      formalLogOnePlusProductArgumentLeftChoiceCount q l +
        formalLogOnePlusProductArgumentMixedChoiceCount q l := by
  rw [formalLogOnePlusProductArgumentLeftChoiceCount,
    formalLogOnePlusProductArgumentMixedChoiceCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact formalLogOnePlusProductArgumentBasicFactor_left_coord (hbasic i hi)

/--
Establishes the identity `(∑ i ∈ Finset.range q, l i (1 : Fin 2)) =
formalLogOnePlusProductArgumentRightChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l`.
-/
theorem formalLogOnePlusProductArgument_rightCoord_sum_eq_choiceCounts
    {q : ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    (∑ i ∈ Finset.range q, l i (1 : Fin 2)) =
      formalLogOnePlusProductArgumentRightChoiceCount q l +
        formalLogOnePlusProductArgumentMixedChoiceCount q l := by
  rw [formalLogOnePlusProductArgumentRightChoiceCount,
    formalLogOnePlusProductArgumentMixedChoiceCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact formalLogOnePlusProductArgumentBasicFactor_right_coord (hbasic i hi)

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l +
formalLogOnePlusProductArgumentRightChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l = q`.
-/
theorem formalLogOnePlusProductArgument_totalChoiceCount_eq
    {q : ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentLeftChoiceCount q l +
        formalLogOnePlusProductArgumentRightChoiceCount q l +
      formalLogOnePlusProductArgumentMixedChoiceCount q l =
    q := by
  rw [formalLogOnePlusProductArgumentLeftChoiceCount,
    formalLogOnePlusProductArgumentRightChoiceCount,
    formalLogOnePlusProductArgumentMixedChoiceCount,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    (∑ i ∈ Finset.range q,
        (((if l i = Finsupp.single (0 : Fin 2) 1 then 1 else 0) +
            (if l i = Finsupp.single (1 : Fin 2) 1 then 1 else 0)) +
          (if l i =
              Finsupp.single (0 : Fin 2) 1 +
                Finsupp.single (1 : Fin 2) 1
          then 1 else 0))) =
        (∑ i ∈ Finset.range q, (1 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact formalLogOnePlusProductArgumentBasicFactor_total_indicator
        (hbasic i hi)
    _ = q := by simp

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_left_add_mixed_eq
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentLeftChoiceCount q l +
      formalLogOnePlusProductArgumentMixedChoiceCount q l =
        e (0 : Fin 2) := by
  rw [← formalLogOnePlusProductArgument_leftCoord_sum_eq_choiceCounts hbasic]
  have hsum := (Finset.mem_finsuppAntidiag.mp hl).1
  simpa [Finsupp.finsetSum_apply] using
    congrArg (fun m : Fin 2 →₀ ℕ => m (0 : Fin 2)) hsum

/--
Establishes the identity `formalLogOnePlusProductArgumentRightChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l = e (1 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_right_add_mixed_eq
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentRightChoiceCount q l +
      formalLogOnePlusProductArgumentMixedChoiceCount q l =
        e (1 : Fin 2) := by
  rw [← formalLogOnePlusProductArgument_rightCoord_sum_eq_choiceCounts hbasic]
  have hsum := (Finset.mem_finsuppAntidiag.mp hl).1
  simpa [Finsupp.finsetSum_apply] using
    congrArg (fun m : Fin 2 →₀ ℕ => m (1 : Fin 2)) hsum

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2) ∧
formalLogOnePlusProductArgumentRightChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l = e (1 : Fin 2) ∧
formalLogOnePlusProductArgumentLeftChoiceCount q l +
formalLogOnePlusProductArgumentRightChoiceCount q l +
formalLogOnePlusProductArgumentMixedChoiceCount q l = q`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_system
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentLeftChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l =
        e (0 : Fin 2) ∧
      formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l =
        e (1 : Fin 2) ∧
      formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l =
        q := by
  exact
    ⟨formalLogOnePlusProductArgument_choiceCounts_left_add_mixed_eq
        hl hbasic,
      formalLogOnePlusProductArgument_choiceCounts_right_add_mixed_eq
        hl hbasic,
      formalLogOnePlusProductArgument_totalChoiceCount_eq hbasic⟩


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCoreBase_ExplicitChoiceCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Explicit counts for basic-factor choices

This module solves the coordinate-count system and relates its solution to the
label-count and multinomial choice spaces.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/--
Establishes the identity `q + formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2)
+ e (1 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_total_add_mixed_eq_coord_sum
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    q + formalLogOnePlusProductArgumentMixedChoiceCount q l =
      e (0 : Fin 2) + e (1 : Fin 2) := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨hleft, hright, htotal⟩
  calc
    q + formalLogOnePlusProductArgumentMixedChoiceCount q l =
        (formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
            formalLogOnePlusProductArgumentMixedChoiceCount q l := by
      exact (congrArg
        (fun t : ℕ => t + formalLogOnePlusProductArgumentMixedChoiceCount q l)
        htotal).symm
    _ =
        (formalLogOnePlusProductArgumentLeftChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
        (formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = e (0 : Fin 2) + e (1 : Fin 2) := by
      rw [hleft, hright]

/--
Establishes the identity `formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2) + e
(1 : Fin 2) - q`.
-/
theorem formalLogOnePlusProductArgument_mixedChoiceCount_eq_coord_sum_sub_q
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentMixedChoiceCount q l =
      e (0 : Fin 2) + e (1 : Fin 2) - q := by
  have hsum :=
    formalLogOnePlusProductArgument_choiceCounts_total_add_mixed_eq_coord_sum
      hl hbasic
  calc
    formalLogOnePlusProductArgumentMixedChoiceCount q l =
        q + formalLogOnePlusProductArgumentMixedChoiceCount q l - q := by
      rw [Nat.add_sub_cancel_left]
    _ = e (0 : Fin 2) + e (1 : Fin 2) - q := by
      rw [hsum]

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l = q - e (1 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_leftChoiceCount_eq_q_sub_right_coord
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentLeftChoiceCount q l =
      q - e (1 : Fin 2) := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨_hleft, hright, htotal⟩
  have hq :
      e (1 : Fin 2) +
          formalLogOnePlusProductArgumentLeftChoiceCount q l =
        q := by
    calc
      e (1 : Fin 2) +
          formalLogOnePlusProductArgumentLeftChoiceCount q l =
        (formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
            formalLogOnePlusProductArgumentLeftChoiceCount q l := by
        rw [hright]
      _ =
        formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l := by
        simp only [Nat.add_left_comm, Nat.add_comm]
      _ = q := htotal
  calc
    formalLogOnePlusProductArgumentLeftChoiceCount q l =
        e (1 : Fin 2) +
            formalLogOnePlusProductArgumentLeftChoiceCount q l -
          e (1 : Fin 2) := by
      rw [Nat.add_sub_cancel_left]
    _ = q - e (1 : Fin 2) := by
      rw [hq]

/--
Establishes the identity `formalLogOnePlusProductArgumentRightChoiceCount q l = q - e (0 : Fin
2)`.
-/
theorem formalLogOnePlusProductArgument_rightChoiceCount_eq_q_sub_left_coord
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentRightChoiceCount q l =
      q - e (0 : Fin 2) := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨hleft, _hright, htotal⟩
  have hq :
      e (0 : Fin 2) +
          formalLogOnePlusProductArgumentRightChoiceCount q l =
        q := by
    calc
      e (0 : Fin 2) +
          formalLogOnePlusProductArgumentRightChoiceCount q l =
        (formalLogOnePlusProductArgumentLeftChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
            formalLogOnePlusProductArgumentRightChoiceCount q l := by
        rw [hleft]
      _ =
        formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l := by
        simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = q := htotal
  calc
    formalLogOnePlusProductArgumentRightChoiceCount q l =
        e (0 : Fin 2) +
            formalLogOnePlusProductArgumentRightChoiceCount q l -
          e (0 : Fin 2) := by
      rw [Nat.add_sub_cancel_left]
    _ = q - e (0 : Fin 2) := by
      rw [hq]

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftChoiceCount q l = q - e (1 : Fin 2) ∧
formalLogOnePlusProductArgumentRightChoiceCount q l = q - e (0 : Fin 2) ∧
formalLogOnePlusProductArgumentMixedChoiceCount q l = e (0 : Fin 2) + e (1 : Fin 2) - q`.
-/
theorem formalLogOnePlusProductArgument_choiceCounts_explicit
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentLeftChoiceCount q l =
          q - e (1 : Fin 2) ∧
      formalLogOnePlusProductArgumentRightChoiceCount q l =
          q - e (0 : Fin 2) ∧
        formalLogOnePlusProductArgumentMixedChoiceCount q l =
          e (0 : Fin 2) + e (1 : Fin 2) - q := by
  exact
    ⟨formalLogOnePlusProductArgument_leftChoiceCount_eq_q_sub_right_coord
        hl hbasic,
      formalLogOnePlusProductArgument_rightChoiceCount_eq_q_sub_left_coord
        hl hbasic,
      formalLogOnePlusProductArgument_mixedChoiceCount_eq_coord_sum_sub_q
        hl hbasic⟩


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Proves the formal combinatorial identities behind additivity of the logarithm on products of
principal units.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/--
Establishes the divisibility statement `(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
formalLogOnePlusProductArgument A - MvPowerSeries.X (1 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_sub_rightVariable_dvd_leftVariable
    (A : Type*) [CommRing A] :
    (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
      formalLogOnePlusProductArgument A -
        MvPowerSeries.X (1 : Fin 2) := by
  let X0 : MvPowerSeries (Fin 2) A := MvPowerSeries.X (0 : Fin 2)
  let X1 : MvPowerSeries (Fin 2) A := MvPowerSeries.X (1 : Fin 2)
  refine ⟨1 + X1, ?_⟩
  change formalLogOnePlusProductArgument A - X1 = X0 * (1 + X1)
  simp [formalLogOnePlusProductArgument]
  ring

/--
Establishes the divisibility statement `(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
(formalLogOnePlusProductArgument A) ^ d - (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A)
^ d`.
-/
theorem formalLogOnePlusProductArgument_pow_sub_rightVariable_pow_dvd_leftVariable
    (A : Type*) [CommRing A] (d : ℕ) :
    (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
      (formalLogOnePlusProductArgument A) ^ d -
        (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d := by
  exact
    (formalLogOnePlusProductArgument_sub_rightVariable_dvd_leftVariable A).trans
      (sub_dvd_pow_sub_pow
        (formalLogOnePlusProductArgument A)
        (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) d)

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
((formalLogOnePlusProductArgument A) ^ d) = MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d)`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_single_right
    (A : Type*) [CommRing A] (d n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        ((formalLogOnePlusProductArgument A) ^ d) =
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d) := by
  have hdiv :=
    formalLogOnePlusProductArgument_pow_sub_rightVariable_pow_dvd_leftVariable
      A d
  have hcoeffSub :
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        ((formalLogOnePlusProductArgument A) ^ d -
          (MvPowerSeries.X (1 : Fin 2) :
            MvPowerSeries (Fin 2) A) ^ d) = 0 := by
    have hvanish :=
      (MvPowerSeries.X_pow_dvd_iff
        (s := (0 : Fin 2)) (n := 1)
        (φ := (formalLogOnePlusProductArgument A) ^ d -
          (MvPowerSeries.X (1 : Fin 2) :
            MvPowerSeries (Fin 2) A) ^ d)).1
        (by simpa using hdiv)
    exact hvanish (Finsupp.single (1 : Fin 2) n) (by
      have h01 : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
      simp [Finsupp.single_eq_of_ne h01])
  rw [map_sub] at hcoeffSub
  exact sub_eq_zero.mp hcoeffSub

/--
Establishes the identity `MvPowerSeries.coeff e ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin
2) A) ^ d) = if e = Finsupp.single (1 : Fin 2) d then 1 else 0`.
-/
theorem formalLogOnePlusRightVariable_pow_coeff
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ) (d : ℕ) :
    MvPowerSeries.coeff e
        ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d) =
      if e = Finsupp.single (1 : Fin 2) d then 1 else 0 := by
  simpa using
    MvPowerSeries.coeff_X_pow (R := A) e (1 : Fin 2) d

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
(PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) = PowerSeries.coeff n
(PowerSeries.log A)`.
-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_single_right
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      PowerSeries.coeff n (PowerSeries.log A) := by
  rw [PowerSeries.coeff_subst
    (formalLogOnePlusProductArgument_hasSubst A) (PowerSeries.log A)
    (Finsupp.single (1 : Fin 2) n)]
  rw [finsum_eq_single _ n]
  · rw [formalLogOnePlusProductArgument_pow_coeff_single_right]
    simp [formalLogOnePlusRightVariable_pow_coeff]
  · intro d hd
    rw [formalLogOnePlusProductArgument_pow_coeff_single_right]
    rw [formalLogOnePlusRightVariable_pow_coeff]
    have hsingle :
        Finsupp.single (1 : Fin 2) n ≠ Finsupp.single (1 : Fin 2) d := by
      intro h
      apply hd
      have hcoord := congrArg (fun e : Fin 2 →₀ ℕ => e (1 : Fin 2)) h
      simpa using hcoord.symm
    simp [hsingle]

/-- The formal logarithm `log(1 + X)`, viewed as a two-variable series in the
left variable. -/
noncomputable def formalLogOnePlusLeftVariableLogSubst
    (A : Type*) [CommRing A] [Algebra ℚ A] : MvPowerSeries (Fin 2) A :=
  PowerSeries.subst
    (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A)
    (PowerSeries.log A)

/-- The formal logarithm `log(1 + Y)`, viewed as a two-variable series in the
right variable. -/
noncomputable def formalLogOnePlusRightVariableLogSubst
    (A : Type*) [CommRing A] [Algebra ℚ A] : MvPowerSeries (Fin 2) A :=
  PowerSeries.subst
    (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A)
    (PowerSeries.log A)

/-- The formal right-hand side `log(1 + X) + log(1 + Y)` of the logarithm
product formula. -/
noncomputable def formalLogOnePlusProductRightSide
    (A : Type*) [CommRing A] [Algebra ℚ A] : MvPowerSeries (Fin 2) A :=
  formalLogOnePlusLeftVariableLogSubst A +
    formalLogOnePlusRightVariableLogSubst A

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
(formalLogOnePlusLeftVariableLogSubst A) = PowerSeries.coeff n (PowerSeries.log A)`.
-/
theorem formalLogOnePlusLeftVariableLogSubst_coeff_single
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        (formalLogOnePlusLeftVariableLogSubst A) =
      PowerSeries.coeff n (PowerSeries.log A) := by
  simp [formalLogOnePlusLeftVariableLogSubst, PowerSeries.coeff_subst_single]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
(formalLogOnePlusRightVariableLogSubst A) = PowerSeries.coeff n (PowerSeries.log A)`.
-/
theorem formalLogOnePlusRightVariableLogSubst_coeff_single
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        (formalLogOnePlusRightVariableLogSubst A) =
      PowerSeries.coeff n (PowerSeries.log A) := by
  simp [formalLogOnePlusRightVariableLogSubst, PowerSeries.coeff_subst_single]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusLeftVariableLogSubst A) = 0`.
-/
theorem formalLogOnePlusLeftVariableLogSubst_coeff_of_ne_axis
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : ∀ d : ℕ, e ≠ Finsupp.single (0 : Fin 2) d) :
    MvPowerSeries.coeff e (formalLogOnePlusLeftVariableLogSubst A) = 0 := by
  simp [formalLogOnePlusLeftVariableLogSubst, PowerSeries.coeff_subst_single, he]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) =
MvPowerSeries.coeff e (formalLogOnePlusLeftVariableLogSubst A) + MvPowerSeries.coeff e
(formalLogOnePlusRightVariableLogSubst A)`.
-/
theorem formalLogOnePlusProductRightSide_coeff
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) =
      MvPowerSeries.coeff e (formalLogOnePlusLeftVariableLogSubst A) +
        MvPowerSeries.coeff e (formalLogOnePlusRightVariableLogSubst A) := by
  simp [formalLogOnePlusProductRightSide]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
(formalLogOnePlusProductRightSide A) = PowerSeries.coeff n (PowerSeries.log A)`.
-/
theorem formalLogOnePlusProductRightSide_coeff_single_right
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        (formalLogOnePlusProductRightSide A) =
      PowerSeries.coeff n (PowerSeries.log A) := by
  rw [formalLogOnePlusProductRightSide_coeff,
    formalLogOnePlusRightVariableLogSubst_coeff_single]
  have hleft :
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
          (formalLogOnePlusLeftVariableLogSubst A) = 0 := by
    by_cases hn : n = 0
    · subst n
      simpa [Finsupp.single_zero] using
        formalLogOnePlusLeftVariableLogSubst_coeff_single A 0
    · exact
        formalLogOnePlusLeftVariableLogSubst_coeff_of_ne_axis A
          (Finsupp.single (1 : Fin 2) n)
          (fun d h => by
            apply hn
            have hcoord :=
              congrArg (fun e : Fin 2 →₀ ℕ => e (1 : Fin 2)) h
            simpa using hcoord)
  abel_nf
  simp [hleft]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
(PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) = MvPowerSeries.coeff
(Finsupp.single (1 : Fin 2) n) (formalLogOnePlusProductRightSide A)`.
-/
theorem formalLogOnePlusProductFormula_coeff_single_right
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        (formalLogOnePlusProductRightSide A) := by
  rw [formalLogOnePlusProductArgument_logSubst_coeff_single_right,
    formalLogOnePlusProductRightSide_coeff_single_right]

/-- Establishes the identity `e = Finsupp.single (1 : Fin 2) (e (1 : Fin 2))`. -/
theorem finsupp_fin_two_eq_single_right_of_left_eq_zero
    (e : Fin 2 →₀ ℕ) (he : e (0 : Fin 2) = 0) :
    e = Finsupp.single (1 : Fin 2) (e (1 : Fin 2)) := by
  ext i
  fin_cases i <;> simp [he]

/-- On the right coordinate axis, the substituted logarithm and the proposed
right-hand side have the same coefficient. -/
theorem formalLogOnePlusProductFormula_coeff_of_left_coord_zero
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : e (0 : Fin 2) = 0) :
    MvPowerSeries.coeff e
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) := by
  rw [finsupp_fin_two_eq_single_right_of_left_eq_zero e he]
  exact formalLogOnePlusProductFormula_coeff_single_right A (e (1 : Fin 2))

/-- Difference between the two formal sides of the logarithm product formula.
The remaining proof of the formal identity is exactly the vanishing of this
series on mixed monomials. -/
noncomputable def formalLogOnePlusProductFormulaDefect
    (A : Type*) [CommRing A] [Algebra ℚ A] : MvPowerSeries (Fin 2) A :=
  PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A) -
      formalLogOnePlusProductRightSide A

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = 0`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_of_left_coord_zero
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : e (0 : Fin 2) = 0) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) = 0 := by
  simp [formalLogOnePlusProductFormulaDefect,
    formalLogOnePlusProductFormula_coeff_of_left_coord_zero A e he]

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_CyclicValueGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Cyclic value groups and normalized uniformizers

This file supplies the ordered-group and rank-one facts used for actual
multiplicative valuation ranges, together with normalized uniformizer results
for `ℤᵐ⁰`-valued valuations.
-/

noncomputable section

universe u x

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace WithZeroValuation

variable {R : Type u}
variable {Gamma : Type x} [LinearOrderedCommGroupWithZero Gamma]

/-- A cyclic linearly ordered commutative group is multiplicatively
Archimedean.  Mathlib supplies the valuation-theoretic equivalence
`RankOne <-> MulArchimedean`; this lemma supplies the missing ordered-group
input for actual valuation ranges whose unit group has already been proved
cyclic. -/
theorem isCyclic_mulArchimedean
    (G : Type*) [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    [IsCyclic G] :
    MulArchimedean G := by
  classical
  by_cases hsub : Subsingleton G
  · refine ⟨fun _ y hy => ?_⟩
    exact (hy.ne' (Subsingleton.elim y 1)).elim
  have : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
  let a : G := LinearOrderedCommGroup.Subgroup.genLTOne (⊤ : Subgroup G)
  let b : G := a⁻¹
  have hb : 1 < b := by
    have ha : a < 1 := by
      simpa [a] using
      LinearOrderedCommGroup.Subgroup.genLTOne_lt_one (⊤ : Subgroup G)
    simpa [b] using (one_lt_inv'.2 ha)
  have hbtop : Subgroup.zpowers b = (⊤ : Subgroup G) := by
    have hatop : Subgroup.zpowers a = (⊤ : Subgroup G) := by
      simp [a]
    simpa [b, Subgroup.zpowers_inv] using hatop
  refine ⟨fun x y hy => ?_⟩
  have hxmem : x ∈ Subgroup.zpowers b := by
    rw [hbtop]
    trivial
  have hymem : y ∈ Subgroup.zpowers b := by
    rw [hbtop]
    trivial
  rw [Subgroup.mem_zpowers_iff] at hxmem hymem
  rcases hxmem with ⟨m, rfl⟩
  rcases hymem with ⟨l, hy_eq⟩
  rw [← hy_eq] at hy
  have hlpos : 0 < l :=
    (zpow_lt_zpow_iff_right hb).1 (by simpa using hy)
  obtain ⟨n, hn⟩ := Archimedean.arch m hlpos
  refine ⟨n, ?_⟩
  rw [← hy_eq]
  have hmn : m ≤ l * (n : ℤ) := by
    simpa [nsmul_eq_mul, mul_comm] using hn
  calc
    b ^ m ≤ b ^ (l * (n : ℤ)) :=
      (zpow_le_zpow_iff_right hb).2 hmn
    _ = (b ^ l) ^ n := by
      rw [zpow_mul, zpow_natCast]

/-- If the nonzero part of a value group is cyclic, the value group is
multiplicatively Archimedean. -/
theorem units_isCyclic_mulArchimedean
    (Gamma : Type x) [LinearOrderedCommGroupWithZero Gamma]
    [IsCyclic Gammaˣ] :
    MulArchimedean Gamma := by
  have : MulArchimedean Gammaˣ :=
    isCyclic_mulArchimedean Gammaˣ
  exact (Units.mulArchimedean_iff (G₀ := Gamma)).1 inferInstance

/-- A nontrivial valuation whose ambient value group has cyclic unit group is
rank one.  This is used only after restricting an abstract complete-DVF
valuation to its actual range. -/
@[implicit_reducible]
noncomputable def rankOneOfUnitsIsCyclic
    [Ring R]
    (v : _root_.Valuation R Gamma) [v.IsNontrivial] [IsCyclic Gammaˣ] :
    v.RankOne := by
  haveI : MulArchimedean Gamma :=
    units_isCyclic_mulArchimedean Gamma
  haveI :
      MulArchimedean
        (MonoidWithZeroHom.ValueGroup₀
          (MonoidWithZeroHom.ofClass v)) :=
    MulArchimedean.comap
      MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exact
    Classical.choice
      ((_root_.Valuation.nonempty_rankOne_iff_mulArchimedean
        (v := v)).2 inferInstance)

open LinearOrderedCommGroup


end WithZeroValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_RangeRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Restricting a valuation to its multiplicative range

The restricted valuation has the same valuation ring, maximal ideal, and
residue field as the original valuation.
-/

noncomputable section

universe u x

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace WithZeroValuation

variable {R : Type u}
variable {Gamma : Type x} [LinearOrderedCommGroupWithZero Gamma]

section Field

variable [Field R]

/-- Restrict a valuation's codomain to its actual multiplicative range.

This removes irrelevant ambient value-group elements.  It is the value-group
normalization needed before finite-dimensional closedness can be used for an
abstract chosen local-field valuation. -/
def mrangeRestrict (v : _root_.Valuation R Gamma) :
    _root_.Valuation R (MonoidHom.mrange v.toMonoidWithZeroHom) where
  toFun r := ⟨v r, ⟨r, rfl⟩⟩
  map_one' := by
    ext
    exact map_one v
  map_zero' := by
    ext
    exact map_zero v
  map_mul' x y := by
    ext
    exact map_mul v x y
  map_add_le_max' x y := by
    rw [← Subtype.coe_le_coe]
    exact map_add_le_max v x y

/-- The defining evaluation formula for `mrangeRestrict` is `(mrangeRestrict v x : Gamma) = v x`. -/
@[simp]
theorem mrangeRestrict_apply (v : _root_.Valuation R Gamma) (x : R) :
    (mrangeRestrict v x : Gamma) = v x :=
  rfl

/-- Passing to the actual multiplicative range does not change the valuation
subring predicate. -/
theorem mem_mrangeRestrict_valuationSubring_iff
    (v : _root_.Valuation R Gamma) (x : R) :
    x ∈ (mrangeRestrict v).valuationSubring ↔ x ∈ v.valuationSubring := by
  rw [_root_.Valuation.mem_valuationSubring_iff,
    _root_.Valuation.mem_valuationSubring_iff]
  rw [← Subtype.coe_le_coe]
  rfl

/-- The valuation subring is unchanged after restricting the value group to
the actual multiplicative range. -/
noncomputable def valuationSubringEquivMrangeRestrict
    (v : _root_.Valuation R Gamma) :
    v.valuationSubring ≃+* (mrangeRestrict v).valuationSubring where
  toFun x :=
    ⟨x, (mem_mrangeRestrict_valuationSubring_iff v x).2 x.2⟩
  invFun x :=
    ⟨x, (mem_mrangeRestrict_valuationSubring_iff v x).1 x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_mul' x y := by ext; rfl
  map_add' x y := by ext; rfl

/--
Establishes the identity `((valuationSubringEquivMrangeRestrict v x : (mrangeRestrict
v).valuationSubring) : R) = x`.
-/
@[simp]
theorem valuationSubringEquivMrangeRestrict_apply_coe
    (v : _root_.Valuation R Gamma) (x : v.valuationSubring) :
    ((valuationSubringEquivMrangeRestrict v x :
      (mrangeRestrict v).valuationSubring) : R) = x :=
  rfl

variable {K : Type u} [Field K]

/-- Restricting a valuation to its actual multiplicative range induces the
same residue field. -/
noncomputable def residueFieldEquivMrangeRestrict
    (v : _root_.Valuation K Gamma) :
    IsLocalRing.ResidueField v.valuationSubring ≃+*
      IsLocalRing.ResidueField (mrangeRestrict v).valuationSubring := by
  let e := valuationSubringEquivMrangeRestrict v
  letI : IsLocalHom
      (e : v.valuationSubring →+* (mrangeRestrict v).valuationSubring) :=
    IsLocalHom.of_surjective
      (e : v.valuationSubring →+* (mrangeRestrict v).valuationSubring)
      e.surjective
  exact IsLocalRing.ResidueField.mapEquiv e

end Field

end WithZeroValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_Arithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Arithmetic lemmas for local-field index calculations

This file contains the pure natural-number cancellation steps used after local-field
norm and value-group arguments have produced an lcm divisibility.

It also contains the elementary `p`-adic valuation estimates used in the local-field structure development,
the logarithm and exponential estimates for the convergence and valuation behavior of the
logarithm and exponential series.
-/

namespace LocalFieldTheory.DiscreteValuationField

open Filter

section PadicLogArithmetic

variable {p n : ℕ}

/-- Arithmetic estimate for the field-unit logarithm in real logarithmic
form: `v_p(n) <= log_p(n)`. -/
theorem padicValNat_le_real_logb
    [Fact p.Prime] (n : ℕ) :
    (padicValNat p n : ℝ) ≤ Real.logb p n := by
  exact
    (Nat.cast_le.mpr (padicValNat_le_nat_log (p := p) n)).trans
      (Real.natLog_le_logb n p)

/-- Asymptotic estimate for the field-unit logarithm:
for every positive slope `c`, the linear term `n * c` eventually dominates
the logarithmic denominator contribution `log_p(n)`. -/
theorem tendsto_nat_mul_const_sub_logb_atTop
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * c - Real.logb p n) atTop atTop := by
  have hhalf : 0 < c / 2 := by positivity
  have hsmall :
      (fun n : ℕ => Real.logb (p : ℝ) (n : ℝ)) =o[atTop]
        (fun n : ℕ => (n : ℝ)) := by
    simpa [Function.comp_def] using
      (Real.isLittleO_logb_id_atTop (b := (p : ℝ))).comp_tendsto
        tendsto_natCast_atTop_atTop
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        ‖Real.logb (p : ℝ) (n : ℝ)‖ ≤
          (c / 2) * ‖(n : ℝ)‖ :=
    hsmall.def hhalf
  have hle :
      (fun n : ℕ => (c / 2) * (n : ℝ)) ≤ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) * c - Real.logb (p : ℝ) (n : ℝ)) := by
    filter_upwards [hbound] with n hn
    have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog_le :
        Real.logb (p : ℝ) (n : ℝ) ≤ (c / 2) * (n : ℝ) := by
      calc
        Real.logb (p : ℝ) (n : ℝ) ≤
            ‖Real.logb (p : ℝ) (n : ℝ)‖ :=
          le_abs_self _
        _ ≤ (c / 2) * ‖(n : ℝ)‖ := hn
        _ = (c / 2) * (n : ℝ) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hnnonneg]
    calc
      (c / 2) * (n : ℝ) =
          (n : ℝ) * c - (c / 2) * (n : ℝ) := by
        ring
      _ ≤ (n : ℝ) * c - Real.logb (p : ℝ) (n : ℝ) :=
        sub_le_sub_left hlog_le ((n : ℝ) * c)
  have hlin :
      Tendsto (fun n : ℕ => (c / 2) * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hhalf tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono' atTop hle hlin

/-- The same logarithmic domination estimate with the natural series indexing
`n + 1`, avoiding the zero denominator in the logarithm series. -/
theorem tendsto_nat_succ_mul_const_sub_logb_atTop
    {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * c - Real.logb p (n + 1))
      atTop atTop := by
  simpa [Function.comp_def] using
    (tendsto_nat_mul_const_sub_logb_atTop (p := p) hc).comp
      (tendsto_add_atTop_nat 1)

/-- Exponential-series estimate for the field-unit logarithm:
for every slope `c > 1`, the linear term `n * c` dominates the factorial
denominator contribution `v_p(n!)`.  The proof uses mathlib's Legendre-bound
`padicValNat_factorial_le`; no factorial valuation formula is reproved here. -/
theorem tendsto_nat_mul_const_sub_padicValNat_factorial_atTop
    [Fact p.Prime] {c : ℝ} (hc : 1 < c) :
    Tendsto
      (fun n : ℕ => (n : ℝ) * c - (padicValNat p n.factorial : ℝ))
      atTop atTop := by
  have hpos : 0 < c - 1 := sub_pos.mpr hc
  have hsource :
      Tendsto (fun n : ℕ => (n : ℝ) * (c - 1)) atTop atTop := by
    simpa [mul_comm] using
      Tendsto.const_mul_atTop hpos tendsto_natCast_atTop_atTop
  have hle :
      (fun n : ℕ => (n : ℝ) * (c - 1)) ≤ᶠ[atTop]
        (fun n : ℕ =>
          (n : ℝ) * c - (padicValNat p n.factorial : ℝ)) := by
    exact Eventually.of_forall fun n => by
      have hdenNat : padicValNat p n.factorial ≤ n :=
        padicValNat_factorial_le (p := p) n
      have hden : (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) :=
        Nat.cast_le.mpr hdenNat
      nlinarith
  exact tendsto_atTop_mono' atTop hle hsource

/-- Legendre's factorial-valuation formula, Legendre's formula in digit form:
if `n = a_0 + a_1 p + ... + a_r p^r`, then multiplying the displayed digit formula by `p - 1` gives
`(p - 1) v_p(n!) = (a_0 p^0 + ... + a_r p^r) - (a_0 + ... + a_r)`. -/
theorem padicValNat_factorial_digits
    [Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p n.factorial =
      Nat.ofDigits p (p.digits n) - (p.digits n).sum := by
  simpa [Nat.ofDigits_digits] using
    (sub_one_mul_padicValNat_factorial (p := p) n)

/-- A nonzero natural number has positive sum of base-`p` digits. -/
theorem digits_sum_pos_of_ne_zero (hn : n ≠ 0) :
    0 < (p.digits n).sum := by
  by_contra hnot
  have hsum0 : (p.digits n).sum = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hnot)
  have hall : ∀ a ∈ p.digits n, a = 0 :=
    List.sum_eq_zero_iff.mp hsum0
  have hmapZero :
      (List.mapIdx (fun i a => a * p ^ i) (p.digits n)).sum = 0 := by
    apply List.sum_eq_zero
    intro b hb
    rw [List.mem_mapIdx] at hb
    rcases hb with ⟨i, hi, rfl⟩
    have hdigit : (p.digits n)[i] = 0 :=
      hall _ (List.getElem_mem hi)
    simp [hdigit]
  have hof : Nat.ofDigits p (p.digits n) = 0 := by
    simpa [Nat.ofDigits_eq_sum_mapIdx] using hmapZero
  have hn0 : n = 0 := by
    simpa [Nat.ofDigits_digits] using hof
  exact hn hn0

/-- Legendre's formula gives the sharp bound
`(p - 1) * v_p(n!) <= n - 1` for nonzero `n`. -/
theorem sub_one_mul_padicValNat_factorial_le_sub_one
    [Fact p.Prime] (hn : n ≠ 0) :
    (p - 1) * padicValNat p n.factorial ≤ n - 1 := by
  rw [padicValNat_factorial_digits, Nat.ofDigits_digits]
  have hsumpos : 1 ≤ (p.digits n).sum :=
    Nat.succ_le_of_lt (digits_sum_pos_of_ne_zero (p := p) hn)
  omega

/-- Factorial-denominator analogue of the factorial quotient estimate:
`v_p(n!) / (n-1) <= 1/(p-1)`. -/
theorem padicValNat_factorial_div_sub_one_le_inv_sub_one
    [Fact p.Prime] (hn : 1 < n) :
    (padicValNat p n.factorial : ℚ) / ((n : ℚ) - 1) ≤
      1 / ((p : ℚ) - 1) := by
  have hpNat : Nat.Prime p := Fact.out
  have hp : (1 : ℚ) < p := by
    exact_mod_cast hpNat.one_lt
  have hpden : 0 < (p : ℚ) - 1 := by
    linarith
  have hnden : 0 < (n : ℚ) - 1 := by
    have hnq : (1 : ℚ) < n := by
      exact_mod_cast hn
    linarith
  have hNat :
      (p - 1) * padicValNat p n.factorial ≤ n - 1 :=
    sub_one_mul_padicValNat_factorial_le_sub_one
      (p := p) (n := n) (by omega)
  have hmul :
      ((p : ℚ) - 1) * (padicValNat p n.factorial : ℚ) ≤
        (n : ℚ) - 1 := by
    have hcast :
        (((p - 1) * padicValNat p n.factorial : ℕ) : ℚ) ≤
          ((n - 1 : ℕ) : ℚ) := by
      exact_mod_cast hNat
    have hpone : 1 ≤ p := hpNat.one_lt.le
    have hnone : 1 ≤ n := by omega
    simpa [Nat.cast_mul, Nat.cast_sub hpone, Nat.cast_sub hnone] using hcast
  field_simp [hnden.ne', hpden.ne']
  nlinarith

/-- Real factorial-denominator bound used for the sharp convergence radius of
the exponential series. -/
theorem padicValNat_factorial_le_sub_one_div_sub_one_real
    [Fact p.Prime] (hn : n ≠ 0) :
    (padicValNat p n.factorial : ℝ) ≤
      ((n : ℝ) - 1) / ((p : ℝ) - 1) := by
  have hpNat : Nat.Prime p := Fact.out
  have hp : (1 : ℝ) < p := by
    exact_mod_cast hpNat.one_lt
  have hpden : 0 < (p : ℝ) - 1 := by
    linarith
  have hNat :
      (p - 1) * padicValNat p n.factorial ≤ n - 1 :=
    sub_one_mul_padicValNat_factorial_le_sub_one
      (p := p) (n := n) hn
  have hmul :
      ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) ≤
        (n : ℝ) - 1 := by
    have hcast :
        (((p - 1) * padicValNat p n.factorial : ℕ) : ℝ) ≤
          ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hNat
    have hpone : 1 ≤ p := hpNat.one_lt.le
    have hnone : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    simpa [Nat.cast_mul, Nat.cast_sub hpone, Nat.cast_sub hnone] using hcast
  exact (le_div_iff₀ hpden).2 (by simpa [mul_comm] using hmul)

/-- Sharp asymptotic estimate for the exponential series denominator:
any real slope strictly above `C/(p-1)` dominates
`C * v_p(n!)`. -/
theorem tendsto_nat_mul_const_sub_const_mul_padicValNat_factorial_atTop
    [Fact p.Prime] {c C : ℝ} (hC : 0 ≤ C)
    (hc : C / ((p : ℝ) - 1) < c) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) * c - C * (padicValNat p n.factorial : ℝ))
      atTop atTop := by
  have hpNat : Nat.Prime p := Fact.out
  have hp : (1 : ℝ) < p := by
    exact_mod_cast hpNat.one_lt
  have hpden : 0 < (p : ℝ) - 1 := by
    linarith
  have hdelta : 0 < c - C / ((p : ℝ) - 1) := sub_pos.mpr hc
  have hsource :
      Tendsto
        (fun n : ℕ => (n : ℝ) * (c - C / ((p : ℝ) - 1)))
        atTop atTop := by
    simpa [mul_comm] using
      Tendsto.const_mul_atTop hdelta tendsto_natCast_atTop_atTop
  have hle :
      (fun n : ℕ => (n : ℝ) * (c - C / ((p : ℝ) - 1))) ≤ᶠ[atTop]
        (fun n : ℕ =>
          (n : ℝ) * c - C * (padicValNat p n.factorial : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    have hfac :=
      padicValNat_factorial_le_sub_one_div_sub_one_real
        (p := p) (n := n) hn0
    have hCfac :
        C * (padicValNat p n.factorial : ℝ) ≤
          C * (((n : ℝ) - 1) / ((p : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hfac hC
    have hCp_nonneg : 0 ≤ C / ((p : ℝ) - 1) :=
      div_nonneg hC hpden.le
    have hden_bound :
        C * (((n : ℝ) - 1) / ((p : ℝ) - 1)) ≤
          (n : ℝ) * (C / ((p : ℝ) - 1)) := by
      calc
        C * (((n : ℝ) - 1) / ((p : ℝ) - 1)) =
            ((n : ℝ) - 1) * (C / ((p : ℝ) - 1)) := by
          ring
        _ ≤ (n : ℝ) * (C / ((p : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hCp_nonneg
    calc
      (n : ℝ) * (c - C / ((p : ℝ) - 1)) =
          (n : ℝ) * c - (n : ℝ) * (C / ((p : ℝ) - 1)) := by
        ring
      _ ≤ (n : ℝ) * c - C * (padicValNat p n.factorial : ℝ) := by
        linarith [hCfac.trans hden_bound]
  exact tendsto_atTop_mono' atTop hle hsource

/-- Ramified sharp-threshold version of
`exp_higher_term_integer_valuation_gt`: if the factorial denominator
contributes `e * v_p(n!)`, then every higher exponential term has larger
integer valuation than the linear term above `e/(p-1)`. -/
theorem exp_higher_term_integer_valuation_gt_scaled
    [Fact p.Prime] {n e : ℕ} (hn : 2 ≤ n) {m : ℤ}
    (hm : (e : ℚ) / ((p : ℚ) - 1) < (m : ℚ)) :
    m < (n : ℤ) * m - (e : ℤ) * (padicValNat p n.factorial : ℤ) := by
  have hquot :=
    padicValNat_factorial_div_sub_one_le_inv_sub_one
      (p := p) (n := n) (by omega)
  have hnden : 0 < (n : ℚ) - 1 := by
    have hnq : (1 : ℚ) < n := by
      exact_mod_cast (by omega : 1 < n)
    linarith
  have he_nonneg : 0 ≤ (e : ℚ) := by
    positivity
  have hscaled_div :
      ((e : ℚ) * (padicValNat p n.factorial : ℚ)) /
          ((n : ℚ) - 1) ≤
        (e : ℚ) / ((p : ℚ) - 1) := by
    calc
      ((e : ℚ) * (padicValNat p n.factorial : ℚ)) /
          ((n : ℚ) - 1) =
          (e : ℚ) *
            ((padicValNat p n.factorial : ℚ) / ((n : ℚ) - 1)) := by
        ring
      _ ≤ (e : ℚ) * (1 / ((p : ℚ) - 1)) :=
        mul_le_mul_of_nonneg_left hquot he_nonneg
      _ = (e : ℚ) / ((p : ℚ) - 1) := by
        ring
  have hstrict :
      ((e : ℚ) * (padicValNat p n.factorial : ℚ)) /
          ((n : ℚ) - 1) < (m : ℚ) :=
    lt_of_le_of_lt hscaled_div hm
  have hdenlt :
      (e : ℚ) * (padicValNat p n.factorial : ℚ) <
        ((n : ℚ) - 1) * (m : ℚ) := by
    calc
      (e : ℚ) * (padicValNat p n.factorial : ℚ) =
          (((e : ℚ) * (padicValNat p n.factorial : ℚ)) /
              ((n : ℚ) - 1)) *
            ((n : ℚ) - 1) := by
        field_simp [hnden.ne']
      _ < (m : ℚ) * ((n : ℚ) - 1) :=
        mul_lt_mul_of_pos_right hstrict hnden
      _ = ((n : ℚ) - 1) * (m : ℚ) := by
        ring
  have hgoal :
      (m : ℚ) <
        (n : ℚ) * (m : ℚ) -
          (e : ℚ) * (padicValNat p n.factorial : ℚ) := by
    nlinarith
  have hgoal' :
      (m : ℚ) <
        (((n : ℤ) * m -
          (e : ℤ) * (padicValNat p n.factorial : ℤ) : ℤ) : ℚ) := by
    simpa [Int.cast_mul, Int.cast_sub, Int.cast_natCast] using hgoal
  exact_mod_cast hgoal'

end PadicLogArithmetic

end LocalFieldTheory.DiscreteValuationField
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_IntegerValuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integer valuations induced by `ℤᵐ⁰`-valued valuations

This file constructs the sign-normalized integer valuation on field units and
proves the elementary formulas for powers and natural-number denominators.
-/

noncomputable section

universe u

open WithZero
open scoped NNReal WithZero

namespace LocalFieldTheory.DiscreteValuationField

namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The integer-valued multiplicative valuation attached to a
`ℤᵐ⁰`-valued field valuation.  The sign convention is normalized so that a
uniformizer of value `exp (-1)` has integer value `1`. -/
noncomputable def ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) :
    MultiplicativeIntegerValuation Kˣ where
  val x := -WithZero.log (v (x : K))
  map_one := by
    simp
  map_mul x y := by
    have hx : v (x : K) ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 x.ne_zero
    have hy : v (y : K) ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 y.ne_zero
    change
      -WithZero.log (v ((x : K) * (y : K))) =
        -WithZero.log (v (x : K)) + -WithZero.log (v (y : K))
    rw [v.map_mul, WithZero.log_mul hx hy]
    ring

/-- Establishes the identity `(ofWithZeroValuation v).val x = -WithZero.log (v (x : K))`. -/
@[simp] theorem ofWithZeroValuation_val
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (x : Kˣ) :
    (ofWithZeroValuation v).val x = -WithZero.log (v (x : K)) :=
  rfl

/--
`ofWithZeroValuation_val_eq_of_valuation_eq_exp` satisfies the negation formula
`(ofWithZeroValuation v).val x = n`.
-/
theorem ofWithZeroValuation_val_eq_of_valuation_eq_exp_neg
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (x : Kˣ) {n : ℤ}
    (hx : v (x : K) = WithZero.exp (-n)) :
    (ofWithZeroValuation v).val x = n := by
  rw [ofWithZeroValuation_val, hx, WithZero.log_exp]
  ring

/-- Natural-number denominator form of the attached integer valuation.

This is the denominator input for the logarithm-series term
`x^n / n` in the field-unit logarithm theorem. -/
theorem ofWithZeroValuation_val_natCast
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (hnK : (n : K) ≠ 0)
    (hnval : v (n : K) = WithZero.exp (-(padicValNat p n : ℤ))) :
    (ofWithZeroValuation v).val (Units.mk0 (n : K) hnK) =
      (padicValNat p n : ℤ) :=
  ofWithZeroValuation_val_eq_of_valuation_eq_exp_neg
    v (Units.mk0 (n : K) hnK) (by simpa using hnval)

/-- Natural-number denominator form with a ramification-index scale in the
integer valuation.  This is the denominator input for finite extensions where
the normalized field valuation satisfies `v(n) = e * v_p(n)`. -/
theorem ofWithZeroValuation_val_natCast_scaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (e : ℕ) (hnK : (n : K) ≠ 0)
    (hnval :
      v (n : K) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n : ℤ)))) :
    (ofWithZeroValuation v).val (Units.mk0 (n : K) hnK) =
      (e : ℤ) * (padicValNat p n : ℤ) :=
  ofWithZeroValuation_val_eq_of_valuation_eq_exp_neg
    v (Units.mk0 (n : K) hnK)
    (n := (e : ℤ) * (padicValNat p n : ℤ)) (by simpa using hnval)

/-- Valuation of the logarithm-series term `x^n / n`, assuming the natural
number denominator has the expected `p`-adic value. -/
theorem ofWithZeroValuation_val_pow_div_natCast
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (x : Kˣ) (hnK : (n : K) ≠ 0)
    (hnval : v (n : K) = WithZero.exp (-(padicValNat p n : ℤ))) :
    (ofWithZeroValuation v).val
        (x ^ n / Units.mk0 (n : K) hnK) =
      (n : ℤ) * (ofWithZeroValuation v).val x -
        (padicValNat p n : ℤ) := by
  rw [(ofWithZeroValuation v).val_div, (ofWithZeroValuation v).val_pow,
    ofWithZeroValuation_val_natCast v hnK hnval]

/-- Valuation of the exponential-series term `x^n / n!`, assuming the
factorial denominator has the expected `p`-adic value. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (x : Kˣ)
    (hnK : (((n.factorial : ℕ) : K) ≠ 0))
    (hnval :
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ))) :
    (ofWithZeroValuation v).val
        (x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) hnK) =
      (n : ℤ) * (ofWithZeroValuation v).val x -
        (padicValNat p n.factorial : ℤ) := by
  rw [(ofWithZeroValuation v).val_div, (ofWithZeroValuation v).val_pow,
    ofWithZeroValuation_val_natCast v hnK hnval]

/-- Valuation of the exponential-series term `x^n / n!`, with a fixed
ramification-index scale in the factorial denominator valuation. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial_scaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (e : ℕ) (x : Kˣ)
    (hnK : (((n.factorial : ℕ) : K) ≠ 0))
    (hnval :
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ)))) :
    (ofWithZeroValuation v).val
        (x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) hnK) =
      (n : ℤ) * (ofWithZeroValuation v).val x -
        (e : ℤ) * (padicValNat p n.factorial : ℤ) := by
  rw [(ofWithZeroValuation v).val_div, (ofWithZeroValuation v).val_pow,
    ofWithZeroValuation_val_natCast_scaled
      (v := v) (p := p) (n := n.factorial) e hnK hnval]

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_SeriesValuationEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Valuation estimates for logarithm and exponential series

This file proves lower bounds and divergence-to-infinity statements for the
integer valuations of the logarithm and exponential series terms.
-/

noncomputable section

universe u

open Filter WithZero
open scoped NNReal Filter WithZero

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- Positive-degree exponential terms have positive integer valuation when
the input has valuation strictly bigger than one. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial_pos_of_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : (((n.factorial : ℕ) : K) ≠ 0))
    (hnval :
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hxone : 1 < (ofWithZeroValuation v).val x)
    (hn : n ≠ 0) :
    0 <
      (ofWithZeroValuation v).val
        (x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) hnK) := by
  have hterm :=
    ofWithZeroValuation_val_pow_div_natCast_factorial
      (v := v) (p := p) (n := n) x hnK hnval
  have hxge : (2 : ℤ) ≤ (ofWithZeroValuation v).val x := by
    omega
  have hnnonneg : (0 : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hlin :
      (n : ℤ) * 2 ≤
        (n : ℤ) * (ofWithZeroValuation v).val x :=
    mul_le_mul_of_nonneg_left hxge hnnonneg
  have hden :
      (padicValNat p n.factorial : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast padicValNat_factorial_le (p := p) n
  have hnpos : (0 : ℤ) < (n : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  rw [hterm]
  linarith

/-- Real lower bound for the valuation of the exponential-series term
`x^n / n!`. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial_real_lower_bound
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (x : Kˣ)
    (hnK : (((n.factorial : ℕ) : K) ≠ 0))
    (hnval :
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    {c : ℝ} (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    (n : ℝ) * c - (padicValNat p n.factorial : ℝ) ≤
      ((ofWithZeroValuation v).val
        (x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) hnK) : ℝ) := by
  have hterm :=
    ofWithZeroValuation_val_pow_div_natCast_factorial
      (v := v) (p := p) (n := n) x hnK hnval
  have hlin :
      (n : ℝ) * c ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) :=
    mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)
  calc
    (n : ℝ) * c - (padicValNat p n.factorial : ℝ) ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) -
          (padicValNat p n.factorial : ℝ) := by
      linarith
    _ =
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) hnK) : ℝ) := by
      rw [hterm]
      norm_num [Int.cast_sub, Int.cast_mul]

/-- Real lower bound for the valuation of the exponential-series term
`x^n / n!`, with a ramification-index scale in the denominator valuation. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial_scaled_real_lower_bound
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (e : ℕ) (x : Kˣ)
    (hnK : (((n.factorial : ℕ) : K) ≠ 0))
    (hnval :
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    {c : ℝ} (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    (n : ℝ) * c - (e : ℝ) * (padicValNat p n.factorial : ℝ) ≤
      ((ofWithZeroValuation v).val
        (x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) hnK) : ℝ) := by
  have hterm :=
    ofWithZeroValuation_val_pow_div_natCast_factorial_scaled
      (v := v) (p := p) (n := n) e x hnK hnval
  have hlin :
      (n : ℝ) * c ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) :=
    mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)
  calc
    (n : ℝ) * c - (e : ℝ) * (padicValNat p n.factorial : ℝ) ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) -
          (e : ℝ) * (padicValNat p n.factorial : ℝ) := by
      linarith
    _ =
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) hnK) : ℝ) := by
      rw [hterm]
      norm_num [Int.cast_sub, Int.cast_mul]

/-- The valuations of the exponential-series terms `x^n / n!` tend to `+∞`
when the value of `x` is strictly larger than one.  This is the convergence
estimate used for the exponential half of the field-unit logarithm theorem. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial_tendsto_atTop
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    {c : ℝ} (hcOne : 1 < c)
    (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop := by
  have hsource :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) * c - (padicValNat p n.factorial : ℝ))
        atTop atTop :=
    tendsto_nat_mul_const_sub_padicValNat_factorial_atTop
      (p := p) hcOne
  have hle :
      (fun n : ℕ =>
        (n : ℝ) * c - (padicValNat p n.factorial : ℝ)) ≤ᶠ[atTop]
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ)) := by
    exact Eventually.of_forall fun n =>
      ofWithZeroValuation_val_pow_div_natCast_factorial_real_lower_bound
        (v := v) (p := p) (n := n) x (hnK n) (hnval n) hc
  exact tendsto_atTop_mono' atTop hle hsource

/-- Sharp ramified convergence estimate for the exponential-series terms
`x^n / n!`: a value of `x` strictly above `e/(p-1)` dominates the scaled
factorial denominator contribution `e * v_p(n!)`. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial_scaled_tendsto_atTop
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    {c : ℝ}
    (hcThreshold : (e : ℝ) / ((p : ℝ) - 1) < c)
    (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop := by
  have hsource :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) * c -
            (e : ℝ) * (padicValNat p n.factorial : ℝ))
        atTop atTop :=
    tendsto_nat_mul_const_sub_const_mul_padicValNat_factorial_atTop
      (p := p) (c := c) (C := (e : ℝ)) (Nat.cast_nonneg e)
      hcThreshold
  have hle :
      (fun n : ℕ =>
        (n : ℝ) * c -
          (e : ℝ) * (padicValNat p n.factorial : ℝ)) ≤ᶠ[atTop]
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ)) := by
    exact Eventually.of_forall fun n =>
      ofWithZeroValuation_val_pow_div_natCast_factorial_scaled_real_lower_bound
        (v := v) (p := p) (n := n) e x (hnK n) (hnval n) hc
  exact tendsto_atTop_mono' atTop hle hsource

/-- Real lower bound for the valuation of `x^n / n`, in the form used to prove
that the logarithm-series terms tend to zero. -/
theorem ofWithZeroValuation_val_pow_div_natCast_real_lower_bound
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} [Fact p.Prime] (x : Kˣ) (hnK : (n : K) ≠ 0)
    (hnval : v (n : K) = WithZero.exp (-(padicValNat p n : ℤ)))
    {c : ℝ} (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    (n : ℝ) * c - Real.logb p n ≤
      ((ofWithZeroValuation v).val
        (x ^ n / Units.mk0 (n : K) hnK) : ℝ) := by
  have hterm :=
    ofWithZeroValuation_val_pow_div_natCast
      (v := v) (p := p) (n := n) x hnK hnval
  have hlin :
      (n : ℝ) * c ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) :=
    mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)
  have hden :
      (padicValNat p n : ℝ) ≤ Real.logb p n :=
    padicValNat_le_real_logb (p := p) n
  have hmain :
      (n : ℝ) * c - Real.logb p n ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) -
          (padicValNat p n : ℝ) := by
    linarith
  calc
    (n : ℝ) * c - Real.logb p n ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) -
          (padicValNat p n : ℝ) := hmain
    _ =
        ((ofWithZeroValuation v).val
          (x ^ n / Units.mk0 (n : K) hnK) : ℝ) := by
      rw [hterm]
      norm_num [Int.cast_sub, Int.cast_mul]

/-- The valuations of the logarithm-series terms `x^(n+1)/(n+1)` tend to
`+∞`, assuming the natural-number denominators have their expected `p`-adic
values and `x` has positive valuation. -/
theorem ofWithZeroValuation_val_pow_succ_div_natCast_tendsto_atTop
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    {c : ℝ} (hcpos : 0 < c)
    (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop := by
  have hsource :
      Tendsto
        (fun n : ℕ =>
          ((n + 1 : ℕ) : ℝ) * c - Real.logb p (n + 1))
        atTop atTop :=
    tendsto_nat_succ_mul_const_sub_logb_atTop (p := p) hcpos
  have hle :
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) * c - Real.logb p (n + 1)) ≤ᶠ[atTop]
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) : ℝ)) := by
    exact Eventually.of_forall fun n => by
      simpa [Nat.cast_add, Nat.cast_one] using
        ofWithZeroValuation_val_pow_div_natCast_real_lower_bound
          (v := v) (p := p) (n := n + 1) x (hnK n) (hnval n) hc
  exact tendsto_atTop_mono' atTop hle hsource

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_SeriesTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Defines the logarithm and exponential series terms and proves the valuation estimates used in
their convergence arguments.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The unsigned logarithm-series term for a field element.  This is the form
needed for principal units `1 + x`, where `x` may be zero. -/
noncomputable def logSeriesTermField
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) : K :=
  x ^ (n + 1) /
    ((Units.mk0 (((n + 1 : ℕ) : K)) (hnK n) : Kˣ) : K)

/-- Establishes the identity `logSeriesTermField x hnK 0 = x`. -/
@[simp] theorem logSeriesTermField_zero
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    logSeriesTermField x hnK 0 = x := by
  simp [logSeriesTermField]

/-- The signed logarithm-series term for a field element. -/
noncomputable def signedLogSeriesTermField
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) : K :=
  (-1 : K) ^ n * logSeriesTermField x hnK n

/-- Establishes the identity `signedLogSeriesTermField x hnK 0 = x`. -/
@[simp] theorem signedLogSeriesTermField_zero
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    signedLogSeriesTermField x hnK 0 = x := by
  simp [signedLogSeriesTermField]

/-- Field-element finite partial sums of the principal-unit logarithm series. -/
noncomputable def logOnePlusPartialSumField
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (N : ℕ) : K :=
  ∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK n

/-- Establishes the identity `logOnePlusPartialSumField x hnK 0 = 0`. -/
@[simp] theorem logOnePlusPartialSumField_zero
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    logOnePlusPartialSumField x hnK 0 = 0 := by
  simp [logOnePlusPartialSumField]

/-- Establishes the identity `logOnePlusPartialSumField x hnK 1 = x`. -/
@[simp] theorem logOnePlusPartialSumField_one
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    logOnePlusPartialSumField x hnK 1 = x := by
  simp [logOnePlusPartialSumField]

/-- Field-element value of the principal-unit logarithm series. -/
noncomputable def logOnePlusSeriesFieldOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) : K := by
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact ∑' n : ℕ, signedLogSeriesTermField x hnK n

/-! ### Exponential-series terms -/

/-- The `n`-th term `x^n / n!` in the exponential series, for nonzero `x`. -/
noncomputable def expSeriesTerm
    (x : Kˣ) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (n : ℕ) : K :=
  ((x ^ n /
    Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K)

/-- Establishes the identity `expSeriesTerm x hnK 0 = 1`. -/
@[simp] theorem expSeriesTerm_zero
    (x : Kˣ) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) :
    expSeriesTerm x hnK 0 = 1 := by
  simp [expSeriesTerm]

/-- The `n`-th exponential-series term for a field element.  This covers
`x = 0`, which is needed for the eventual principal-ideal domain of the
exponential map. -/
noncomputable def expSeriesTermField
    (x : K) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (n : ℕ) : K :=
  x ^ n / ((Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K)

/-- Establishes the identity `expSeriesTermField x hnK 0 = 1`. -/
@[simp] theorem expSeriesTermField_zero
    (x : K) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) :
    expSeriesTermField x hnK 0 = 1 := by
  simp [expSeriesTermField]

/-- The `n`-th field exponential-series term is the evaluation of the
`n`-th coefficient of mathlib's formal exponential series at `x`. -/
theorem formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField
    [Algebra ℚ K] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.exp K) * x ^ n =
      expSeriesTermField x hnK n := by
  rw [PowerSeries.coeff_exp]
  simp [expSeriesTermField, div_eq_mul_inv, mul_comm]

/-- Field-element finite partial sums of the exponential series. -/
noncomputable def expSeriesPartialSumField
    (x : K) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (N : ℕ) : K :=
  ∑ n ∈ Finset.range N, expSeriesTermField x hnK n

/-- Establishes the identity `expSeriesPartialSumField x hnK 0 = 0`. -/
@[simp] theorem expSeriesPartialSumField_zero
    (x : K) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) :
    expSeriesPartialSumField x hnK 0 = 0 := by
  simp [expSeriesPartialSumField]

/-- Establishes the identity `expSeriesPartialSumField x hnK 1 = 1`. -/
@[simp] theorem expSeriesPartialSumField_one
    (x : K) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) :
    expSeriesPartialSumField x hnK 1 = 1 := by
  simp [expSeriesPartialSumField]

/-- Coefficientwise Cauchy product for the local exponential terms, inherited
from mathlib's formal identity `exp(xX) * exp(yX) = exp((x+y)X)`. -/
theorem expSeriesTermField_add_eq_sum_antidiagonal
    [Algebra ℚ K] (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) (n : ℕ) :
    expSeriesTermField (x + y) hnK n =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        expSeriesTermField x hnK ij.1 *
          expSeriesTermField y hnK ij.2 := by
  symm
  calc
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        expSeriesTermField x hnK ij.1 *
          expSeriesTermField y hnK ij.2) =
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          (PowerSeries.coeff ij.1 (PowerSeries.exp K) * x ^ ij.1) *
            (PowerSeries.coeff ij.2 (PowerSeries.exp K) * y ^ ij.2) := by
      exact Finset.sum_congr rfl fun ij _ => by
        rw [formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField
          (K := K) x hnK ij.1,
          formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField
          (K := K) y hnK ij.2]
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          PowerSeries.coeff ij.1
              (PowerSeries.rescale x (PowerSeries.exp K)) *
            PowerSeries.coeff ij.2
              (PowerSeries.rescale y (PowerSeries.exp K)) := by
      exact Finset.sum_congr rfl fun ij _ => by
        simp [mul_assoc, mul_left_comm, mul_comm]
    _ = PowerSeries.coeff n
          (PowerSeries.rescale x (PowerSeries.exp K) *
            PowerSeries.rescale y (PowerSeries.exp K)) := by
      rw [PowerSeries.coeff_mul]
    _ = PowerSeries.coeff n
          (PowerSeries.rescale (x + y) (PowerSeries.exp K)) := by
      rw [PowerSeries.exp_mul_exp_eq_exp_add]
    _ = PowerSeries.coeff n (PowerSeries.exp K) * (x + y) ^ n := by
      simp [mul_comm]
    _ = expSeriesTermField (x + y) hnK n :=
      formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField
        (K := K) (x + y) hnK n

/-- Field-element value of the exponential series. -/
noncomputable def expSeriesFieldOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (x : K) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) : K := by
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact ∑' n : ℕ, expSeriesTermField x hnK n

/-- The topology attached to a valued field is nonarchimedean.  This is the
topological input needed before applying mathlib's nonarchimedean infinite-sum
criterion. -/
theorem nonarchimedeanRing_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    NonarchimedeanRing K := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  simpa [Valued.mk'] using v.subgroups_basis.nonarchimedean

/-- In the topology attached to a discrete `ℤᵐ⁰`-valued valuation, every open
valuation ball of nonzero radius is sequentially closed for convergent
sequences. -/
theorem valuation_limit_lt_of_tendsto_of_eventually_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0)
    {u : ℕ → K} {z : K}
    (hu :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Tendsto u atTop (𝓝 z))
    (hsmall : ∀ᶠ n : ℕ in atTop, v (u n) < γ) :
    v z < γ := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_contra hznot
  have hzle : γ ≤ v z := le_of_not_gt hznot
  have hvz0 : v z ≠ 0 := by
    intro hvz
    apply hγ
    apply le_antisymm
    · simpa [hvz] using hzle
    · exact zero_le
  have hdiff :
      Tendsto (fun n : ℕ => z - u n) atTop (𝓝 (0 : K)) := by
    have hz : Tendsto (fun _ : ℕ => z) atTop (𝓝 z) := tendsto_const_nhds
    simpa using hz.sub hu
  have hball : {w : K | v w < v z} ∈ 𝓝 (0 : K) := by
    rw [Valued.mem_nhds_zero]
    refine ⟨Units.mk0 (v.restrict z) (by simpa using hvz0), ?_⟩
    intro w hw
    change v.restrict w < v.restrict z at hw
    exact v.restrict_lt_iff.mp hw
  have hdiff_small : ∀ᶠ n : ℕ in atTop, v (z - u n) < v z :=
    hdiff.eventually hball
  have hcontra : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hsmall, hdiff_small] with n hun hdiffn
    have hun_lt_z : v (u n) < v z := lt_of_lt_of_le hun hzle
    have hsub : v (z - u n) = v z :=
      v.map_sub_eq_of_lt_left hun_lt_z
    rw [hsub] at hdiffn
    exact (lt_irrefl _ hdiffn)
  rcases hcontra.exists with ⟨_, hfalse⟩
  exact hfalse

/-- In the topology attached to a discrete `ℤᵐ⁰`-valued valuation, the open
unit ball is sequentially closed for convergent sequences. -/
theorem valuation_limit_lt_one_of_tendsto_of_eventually_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {u : ℕ → K} {z : K}
    (hu :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Tendsto u atTop (𝓝 z))
    (hsmall :
      ∀ᶠ n : ℕ in atTop,
        v (u n) < (1 : WithZero (Multiplicative ℤ))) :
    v z < (1 : WithZero (Multiplicative ℤ)) := by
  exact
    valuation_limit_lt_of_tendsto_of_eventually_lt
      (v := v) (γ := (1 : WithZero (Multiplicative ℤ))) one_ne_zero
      hu hsmall

/-- The open valuation ball of any radius is closed under addition. -/
theorem valuation_add_lt_of_lt
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : _root_.Valuation K Γ₀) {γ : Γ₀} {x y : K}
    (hx : v x < γ) (hy : v y < γ) :
    v (x + y) < γ := by
  exact lt_of_le_of_lt (map_add_le_max v x y) (max_lt hx hy)

/-- The normalized exponential convergence radius is stable under addition. -/
theorem valuation_add_lt_exp_neg_one_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) {x y : K}
    (hx : v x < WithZero.exp (-1 : ℤ))
    (hy : v y < WithZero.exp (-1 : ℤ)) :
    v (x + y) < WithZero.exp (-1 : ℤ) :=
  valuation_add_lt_of_lt v hx hy

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_ExpConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Establishes convergence and summability of the exponential series on sufficiently deep
nonarchimedean ideals.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- Establishes the identity `expSeriesTermField x hnK n = 0`. -/
theorem expSeriesTermField_eq_zero_of_eq_zero_of_ne_zero
    {x : K} (hx : x = 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    {n : ℕ} (hn : n ≠ 0) :
    expSeriesTermField x hnK n = 0 := by
  cases n with
  | zero => exact False.elim (hn rfl)
  | succ n => simp [expSeriesTermField, hx]

/-- The field-element exponential series at zero has value one. -/
@[simp] theorem expSeriesField_zero_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) :
    expSeriesFieldOfWithZeroValuation v 0 hnK = 1 := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  calc
    expSeriesFieldOfWithZeroValuation v 0 hnK =
        ∑' n : ℕ, expSeriesTermField (0 : K) hnK n := by
      rfl
    _ = expSeriesTermField (0 : K) hnK 0 := by
      exact tsum_eq_single 0 fun n hn =>
        expSeriesTermField_eq_zero_of_eq_zero_of_ne_zero rfl hnK hn
    _ = 1 := by
      simp

/-- Zero lies in the normalized exponential convergence ball. -/
theorem valuation_zero_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) :
    v (0 : K) < WithZero.exp (-1 : ℤ) := by
  simp

/-- The additive ball on which the local exponential series converges. -/
def expConvergenceAddSubgroupOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) :
    AddSubgroup K where
  carrier := {x : K | v x < WithZero.exp (-1 : ℤ)}
  zero_mem' := valuation_zero_lt_exp_neg_one (K := K) v
  add_mem' := by
    intro x y hx hy
    exact valuation_add_lt_exp_neg_one_of_lt_exp_neg_one v hx hy
  neg_mem' := by
    intro x hx
    simpa using hx

/--
Characterizes `x ∈ expConvergenceAddSubgroupOfWithZeroValuation v` by the equivalent condition `v
x < WithZero.exp (-1 : ℤ)`.
-/
@[simp] theorem mem_expConvergenceAddSubgroupOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) {x : K} :
    x ∈ expConvergenceAddSubgroupOfWithZeroValuation v ↔
      v x < WithZero.exp (-1 : ℤ) :=
  Iff.rfl

/-- Exponential partial sums split into the constant term and the positive
degree tail. -/
theorem expSeriesPartialSumField_succ_eq_one_add_tail
    (x : K) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (N : ℕ) :
    expSeriesPartialSumField x hnK (N + 1) =
      1 + ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1) := by
  calc
    expSeriesPartialSumField x hnK (N + 1) =
        (∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1)) +
          expSeriesTermField x hnK 0 := by
      rw [expSeriesPartialSumField, Finset.sum_range_succ']
    _ = 1 + ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1) := by
      simp [add_comm]

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_LogConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Establishes convergence and summability of the logarithm series on the nonarchimedean open unit
ball.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- Establishes the identity `logSeriesTermField x hnK n = 0`. -/
theorem logSeriesTermField_eq_zero_of_eq_zero
    {x : K} (hx : x = 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) :
    logSeriesTermField x hnK n = 0 := by
  have hpow : (0 : K) ^ (n + 1) = 0 := by
    cases n with
    | zero => simp
    | succ n => simp
  simp [logSeriesTermField, hx, hpow]

/-- Establishes the identity `signedLogSeriesTermField x hnK n = 0`. -/
theorem signedLogSeriesTermField_eq_zero_of_eq_zero
    {x : K} (hx : x = 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) :
    signedLogSeriesTermField x hnK n = 0 := by
  simp [signedLogSeriesTermField,
    logSeriesTermField_eq_zero_of_eq_zero hx hnK n]

/-- Establishes the identity `logOnePlusSeriesFieldOfWithZeroValuation v 0 hnK = 0`. -/
@[simp] theorem logOnePlusSeriesField_zero_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    logOnePlusSeriesFieldOfWithZeroValuation v 0 hnK = 0 := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hzero :
      (fun n : ℕ => signedLogSeriesTermField (0 : K) hnK n) =
        fun _ : ℕ => (0 : K) := by
    funext n
    exact signedLogSeriesTermField_eq_zero_of_eq_zero rfl hnK n
  simp [logOnePlusSeriesFieldOfWithZeroValuation, hzero]

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_Homomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Packages the convergent logarithm and exponential series as additive and multiplicative
homomorphisms on their natural nonarchimedean domains.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- If two convergent field-valued sequences differ by a sequence converging
to zero, then their limits agree.  This is the topological endpoint used to
turn the formal logarithm product defect into actual additivity of the local
logarithm. -/
theorem eq_of_tendsto_sub_zero
    [TopologicalSpace K] [T2Space K] [ContinuousAdd K] [ContinuousNeg K]
    {f g : ℕ → K} {a b : K}
    (hf : Tendsto f atTop (𝓝 a))
    (hg : Tendsto g atTop (𝓝 b))
    (hsub : Tendsto (fun n => f n - g n) atTop (𝓝 0)) :
    a = b := by
  have hfg :
      Tendsto (fun n => (f n - g n) + g n) atTop (𝓝 (0 + b)) :=
    hsub.add hg
  have hf' : Tendsto f atTop (𝓝 b) := by
    simpa [sub_eq_add_neg, add_assoc] using hfg
  exact tendsto_nhds_unique hf hf'

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicField
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

/-- The DVR valuation on `ℚ_[p]` obtained from the discrete valuation ring
`ℤ_[p]`.  This is the chosen-valuation side of the local-field structure theory,
the local-field structure classification, for the basic `p`-adic field. -/
abbrev padicDVRValuation (p : ℕ) [Fact p.Prime] :
    _root_.Valuation ℚ_[p] ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]

/-- The valuation subring of the DVR valuation on `ℚ_[p]` is the usual
`p`-adic integer ring. -/
noncomputable def padicIntEquivValuationSubring
    (p : ℕ) [Fact p.Prime] :
    ℤ_[p] ≃+* (padicDVRValuation p).valuationSubring :=
  IsDiscreteValuationRing.equivValuationSubring (A := ℤ_[p]) (K := ℚ_[p])

/-- The valuation-subring equivalence is the usual inclusion into `ℚ_[p]`
after forgetting the integrality proof. -/
@[simp]
theorem padicIntEquivValuationSubring_coe
    (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) :
    ((padicIntEquivValuationSubring p x :
        (padicDVRValuation p).valuationSubring) : ℚ_[p]) =
      (x : ℚ_[p]) :=
  rfl

/-- The residue field of `ℤ_[p]` is `ZMod p`. -/
noncomputable def padicIntResidueFieldEquivZMod
    (p : ℕ) [Fact p.Prime] :
    IsLocalRing.ResidueField ℤ_[p] ≃+* ZMod p :=
  PadicInt.residueField

/-- The residue field of `ℤ_[p]` is finite. -/
theorem padicInt_residueField_finite
    (p : ℕ) [Fact p.Prime] :
    Finite (IsLocalRing.ResidueField ℤ_[p]) :=
  Finite.of_equiv (ZMod p)
    (padicIntResidueFieldEquivZMod p).symm.toEquiv

/-- The valuation in `(padicDVRValuation p).IsRankOneDiscrete` is rank-one and discrete. -/
instance padicDVRValuation_isRankOneDiscrete
    (p : ℕ) [Fact p.Prime] :
    (padicDVRValuation p).IsRankOneDiscrete := by
  dsimp [padicDVRValuation]
  infer_instance

/-- The valuation subring of the DVR valuation on `ℚ_[p]` is complete for its
maximal-ideal topology.  The proof transports mathlib's adic completeness of
`ℤ_[p]` across the explicit valuation-subring equivalence. -/
theorem padicDVRValuation_isAdicComplete
    (p : ℕ) [Fact p.Prime] :
    IsAdicComplete
      (IsLocalRing.maximalIdeal (padicDVRValuation p).valuationSubring)
      (padicDVRValuation p).valuationSubring := by
  let e : ℤ_[p] ≃+* (padicDVRValuation p).valuationSubring :=
    padicIntEquivValuationSubring p
  let : Algebra ℤ_[p] (padicDVRValuation p).valuationSubring :=
    e.toRingHom.toAlgebra
  let eLin : ℤ_[p] ≃ₗ[ℤ_[p]] (padicDVRValuation p).valuationSubring :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro r x
        change e (r * x) =
          (algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring r) * e x
        simp [RingHom.algebraMap_toAlgebra] }
  have hcompleteZp :
      IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p] :=
    inferInstance
  let : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p] :=
    hcompleteZp
  have hcompleteAsZp :
      IsAdicComplete
        (IsLocalRing.maximalIdeal ℤ_[p])
        (padicDVRValuation p).valuationSubring :=
    isAdicComplete_of_linearEquiv
      (M := ℤ_[p]) (N := (padicDVRValuation p).valuationSubring)
      (IsLocalRing.maximalIdeal ℤ_[p]) eLin
  have hcompleteMap :
      IsAdicComplete
        ((IsLocalRing.maximalIdeal ℤ_[p]).map
          (algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring))
        (padicDVRValuation p).valuationSubring :=
    (isAdicComplete_map_algebraMap_iff
      (I := IsLocalRing.maximalIdeal ℤ_[p])
      (S := (padicDVRValuation p).valuationSubring)).2 hcompleteAsZp
  have hmem (x : ℤ_[p]) :
      algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring x ∈
          IsLocalRing.maximalIdeal (padicDVRValuation p).valuationSubring ↔
        x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hx hunit
      exact hx (hunit.map (algebraMap ℤ_[p]
        (padicDVRValuation p).valuationSubring))
    · intro hx hunit
      apply hx
      have hpre := hunit.map e.symm.toRingHom
      simpa [RingHom.algebraMap_toAlgebra] using hpre
  have hmapMax :
      (IsLocalRing.maximalIdeal ℤ_[p]).map
          (algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring) =
        IsLocalRing.maximalIdeal (padicDVRValuation p).valuationSubring := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact (hmem x).2 hx
    · intro y hy
      have hx :
          e.symm y ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
        apply (hmem (e.symm y)).1
        simpa [RingHom.algebraMap_toAlgebra] using hy
      have hmap :=
        Ideal.mem_map_of_mem
          (algebraMap ℤ_[p] (padicDVRValuation p).valuationSubring) hx
      simpa [RingHom.algebraMap_toAlgebra] using hmap
  simpa [hmapMax] using hcompleteMap

end Qp
end Examples
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_IntegerRingComparison
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integer rings in the two finite-place completion models

This file restricts the canonical equivalences between the absolute-value and
adic completion models to their valuation rings.  It also identifies the
residue field of a rational finite-place completion.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- Localizing the ring of integers at a finite prime preserves its residue
field.  This is the ideal-theoretic end of the finite-completion residue
comparison. -/
noncomputable def finitePlaceIdealResidueEquivLocalization
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 K ⧸ v.asIdeal) ≃+*
      IsLocalRing.ResidueField (v.valuationSubringAtPrime K) :=
  IsLocalization.AtPrime.equivQuotMaximalIdeal
    v.asIdeal (v.valuationSubringAtPrime K)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_BaseChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Scalar extension from relative to ordinary ideles

The finite restricted-product comparison is combined here with the
archimedean form of the canonical local tensor decomposition. Infinite places above a fixed
infinite place of the base field are identified with exact extensions of
its absolute value.  Surjectivity is reduced through the finite normal
closure to the Galois valuation-extension comparison.
-/

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Restriction of an infinite place of `L` to the base field. -/
def infinitePlaceBelow
    (W : InfinitePlace L) : InfinitePlace K :=
  W.comap (algebraMap K L)

omit [NumberField K] in
/-- Restricting an infinite place along the identity extension fixes it. -/
@[simp]
theorem infinitePlaceBelow_self
    (W : InfinitePlace K) :
    infinitePlaceBelow (K := K) W = W := by
  rw [infinitePlaceBelow,
    Algebra.algebraMap_self, InfinitePlace.comap_id]

section InfinitePlaceTower

variable {M : Type*}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]

omit [NumberField K] [NumberField L] [NumberField M]
    [FiniteDimensional K L] in
/-- Restriction of infinite places is transitive in a tower of number
fields. -/
@[simp]
theorem infinitePlaceBelow_infinitePlaceBelow
    (W : InfinitePlace L) :
    infinitePlaceBelow (K := K)
        (infinitePlaceBelow (K := M) W) =
      infinitePlaceBelow (K := K) W := by
  rw [infinitePlaceBelow, infinitePlaceBelow, infinitePlaceBelow,
    ← InfinitePlace.comap_comp,
    IsScalarTower.algebraMap_eq K M L]

end InfinitePlaceTower
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_Decomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-support decompositions of actual ideles

For a finite set `S` of finite places, this file identifies the actual
subgroup `I_K^S` with the product of all archimedean local groups, the
full multiplicative groups at places in `S`, and the local unit groups
away from `S`.  The construction is componentwise and uses the genuine
restricted-product membership condition.

For a finite family of base places in a Galois extension, it also
assembles the local tensor-algebra decomposition and proves its
equivariance for the full Galois action.  Finally, the concrete
unramified local class-field theorem is transported through Shapiro to
show that every unramified induced integer-unit block has trivial
`H⁰` and `H⁻¹`.
-/

open scoped NumberField RestrictedProduct ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open HilbertRamification
open LocalFieldTheory

universe u

variable {F : Type u} [Field F] [NumberField F]

/-- The finite local factors occurring in `I_F^S`: arbitrary local
elements on `S`, and integral local units away from `S`. -/
abbrev FiniteSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 F))) :=
  (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∈ S},
      (v.1.adicCompletion F)ˣ) ×
    (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      (v.1.adicCompletionIntegers F).units)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_NormLocalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local orders of finite-place norms

For a finite extension of number fields and a place upstairs, the order of
the concrete local field norm is the inertia degree times the upstairs
order.  The proof uses the actual norm–valuation theorem for finite separable
local-field extensions.  The two normalization comparisons needed here are
also concrete:

* the intrinsic local-field valuation is compared with the distinguished
  `ℤᵐ⁰`-valued completion valuation;
* the residue degree of the completed extension is identified with the
  inertia degree of the corresponding prime of the number-field extension.
-/

open scoped NumberField ValuativeRel WithZero
open NumberField IsDedekindDomain

noncomputable section

namespace FiniteIdeleGroup

universe u v w

lemma withZeroMultiplicativeInt_le_exp_neg_one_of_lt_one
    (γ : WithZero (Multiplicative ℤ)) (hγ : γ < 1) :
    γ ≤ WithZero.exp (-1 : ℤ) := by
  cases γ using WithZero.recZeroCoe with
  | zero =>
      exact bot_le
  | coe γ =>
      rw [WithZero.exp_eq_coe_ofAdd, WithZero.coe_le_coe]
      rw [← Multiplicative.toAdd_le]
      change Multiplicative.toAdd γ ≤ (-1 : ℤ)
      have hγ' : Multiplicative.toAdd γ < (0 : ℤ) := by
        have : γ < (1 : Multiplicative ℤ) := by
          simpa using hγ
        change
          Multiplicative.toAdd γ <
            Multiplicative.toAdd (1 : Multiplicative ℤ)
        exact Multiplicative.toAdd_lt.mpr this
      omega

/-- Identity on the underlying field gives the equivalence between the
intrinsic valuation ring and the distinguished valued-field integer ring. -/
noncomputable def intrinsicIntegerEquivValuedInteger
    (F : Type w)
    [Field F] [ValuativeRel F]
    [Valued F (WithZero (Multiplicative ℤ))]
    [(Valued.v :
      Valuation F (WithZero (Multiplicative ℤ))).Compatible] :
    𝒪[F] ≃+* Valued.integer F := by
  apply RingEquiv.subringCongr
  exact congrArg ValuationSubring.toSubring <|
    (Valuation.isEquiv_iff_valuationSubring
      (ValuativeRel.valuation F)
      (Valued.v : Valuation F (WithZero (Multiplicative ℤ)))).mp <|
      ValuativeRel.isEquiv
        (ValuativeRel.valuation F)
        (Valued.v :
          Valuation F (WithZero (Multiplicative ℤ)))

/-- The residue field for the intrinsic valuation is the residue field of
the distinguished `ℤᵐ⁰`-valued completion valuation. -/
noncomputable def intrinsicResidueFieldEquivValuedResidueField
    (F : Type w)
    [Field F] [ValuativeRel F]
    [Valued F (WithZero (Multiplicative ℤ))]
    [(Valued.v :
      Valuation F (WithZero (Multiplicative ℤ))).Compatible] :
    𝓀[F] ≃+* Valued.ResidueField F :=
  IsLocalRing.ResidueField.mapEquiv
    (intrinsicIntegerEquivValuedInteger F)


end FiniteIdeleGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_DenominatorValuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Valuations of natural-number denominators

For a complete discrete valuation with value group `WithZero (Multiplicative ℤ)`
and finite residue field, this file constructs the ramification index
`e = v_K(p)` from the valuation itself.  In mixed characteristic it then proves
the natural-number valuation formula used in the logarithm and exponential theorems.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

variable {K : Type u} [Field K]

/-- The full ordered group structure whose ordered-monoid parent is the
canonical one used by `Valuation` on `ℤᵐ⁰`. -/
@[reducible] def coherentWithZeroMultiplicativeIntGroup :
    LinearOrderedCommGroupWithZero
      (WithZero (Multiplicative ℤ)) where
  __ :=
    (inferInstance :
      LinearOrderedCommMonoidWithZero
        (WithZero (Multiplicative ℤ)))
  __ :=
    (inferInstance :
      CommGroupWithZero
        (WithZero (Multiplicative ℤ)))

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_IwasawaIndexing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Topological structure of local-field units: reindexing the Iwasawa product

The equal-characteristic proof naturally indexes copies of `ℤ_[p]` by a
positive integer prime to `p` and a residue-field basis vector.  This file
records that, when the basis is nonempty, this is exactly a countable product.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField

/-- Positive degrees prime to `p`, as used in the Iwasawa product. -/
def IwasawaDegree (p : ℕ) := {n : ℕ // 1 ≤ n ∧ Nat.Coprime n p}

/-- A prime-to-`p` degree together with a residue-field basis coordinate. -/
abbrev IwasawaIndex (p f : ℕ) := IwasawaDegree p × Fin f

end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
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

def orthoBox {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) : Set E :=
  {x | ∀ i, |u.repr x i| ≤ a i}

open scoped Matrix
open Matrix

open TopologicalSpace
open scoped Topology

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Topology_CompatibleInverseLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Compatible families in inverse systems

The elementary inverse limits used in the local-field structure development are subobjects of dependent
products: their elements are precisely the families preserved by every
transition map.  Keeping this construction at the level of `Subring` and
`Subgroup` lets Lean inherit the ambient algebraic structure instead of
rebuilding the same pointwise instances for each inverse system.
-/

namespace LubinTate

/-- Families in a preorder-indexed system of rings that are preserved by all
transition maps.  No coherence hypotheses on `transition` are needed merely
to form this subring; concrete inverse systems supply them separately when
they are used. -/
def compatibleRingFamilies
    {ι : Type*} [Preorder ι] (R : ι → Type*) [∀ i, Ring (R i)]
    (transition : ∀ {i j : ι}, i ≤ j → R j →+* R i) :
    Subring (∀ i, R i) where
  carrier :=
    {x | ∀ {i j : ι} (hij : i ≤ j), transition hij (x j) = x i}
  zero_mem' := by
    intro i j hij
    exact map_zero (transition hij)
  one_mem' := by
    intro i j hij
    exact map_one (transition hij)
  add_mem' hx hy := by
    intro i j hij
    simpa using congrArg₂ (· + ·) (hx hij) (hy hij)
  mul_mem' hx hy := by
    intro i j hij
    simpa using congrArg₂ (· * ·) (hx hij) (hy hij)
  neg_mem' hx := by
    intro i j hij
    simpa using congrArg Neg.neg (hx hij)

/-- Families in a preorder-indexed system of groups that are preserved by all
transition maps.  The resulting subtype inherits its group structure from
the dependent product. -/
def compatibleGroupFamilies
    {ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, Group (G i)]
    (transition : ∀ {i j : ι}, i ≤ j → G j →* G i) :
    Subgroup (∀ i, G i) where
  carrier :=
    {x | ∀ {i j : ι} (hij : i ≤ j), transition hij (x j) = x i}
  one_mem' := by
    intro i j hij
    exact map_one (transition hij)
  mul_mem' hx hy := by
    intro i j hij
    simpa using congrArg₂ (· * ·) (hx hij) (hy hij)
  inv_mem' hx := by
    intro i j hij
    simpa using congrArg Inv.inv (hx hij)

/-- The group structure transported from the concrete compatible-family
subgroup.  Declaring it explicitly keeps clients independent of reducibility
of `compatibleGroupFamilies`. -/
instance compatibleGroupFamiliesGroup
    { ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, Group (G i)]
    (transition : ∀ {i j : ι}, i ≤ j → G j →* G i) :
    Group (compatibleGroupFamilies G transition) := by
  unfold compatibleGroupFamilies
  infer_instance

/-- Coordinatewise commutativity descends to the compatible-family inverse
limit. -/
instance compatibleGroupFamiliesCommGroup
    { ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, CommGroup (G i)]
    (transition : ∀ {i j : ι}, i ≤ j → G j →* G i) :
    CommGroup (compatibleGroupFamilies G transition) :=
  { (compatibleGroupFamiliesGroup G transition) with
    mul_comm := fun x y => by
      apply Subtype.ext
      funext i
      exact mul_comm (x.1 i) (y.1 i) }

/-- Evaluation of a compatible family at one coordinate. -/
def compatibleGroupFamiliesEval
    { ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, Group (G i)]
    (transition : ∀ {i j : ι}, i ≤ j → G j →* G i) (i : ι) :
    compatibleGroupFamilies G transition →* G i :=
  (Pi.evalMonoidHom G i).comp (compatibleGroupFamilies G transition).subtype

/-- Evaluation of a compatible group family returns its component at the chosen index. -/
@[simp]
theorem compatibleGroupFamiliesEval_apply
    { ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, Group (G i)]
    (transition : ∀ {i j : ι}, i ≤ j → G j →* G i)
    (i : ι) (x : compatibleGroupFamilies G transition) :
    compatibleGroupFamiliesEval G transition i x = x.1 i :=
  rfl

/-- Compatible families are equal when all named coordinate evaluations
agree. -/
@[ext]
theorem compatibleGroupFamilies_ext
    { ι : Type*} [Preorder ι] (G : ι → Type*) [∀ i, Group (G i)]
    (transition : ∀ {i j : ι}, i ≤ j → G j →* G i)
    {x y : compatibleGroupFamilies G transition}
    (h : ∀ i, compatibleGroupFamiliesEval G transition i x =
      compatibleGroupFamiliesEval G transition i y) : x = y := by
  apply Subtype.ext
  funext i
  exact h i

/-- Stagewise multiplicative equivalences induce an equivalence of compatible
families when they commute with every transition map.  This is the reusable
inverse-limit boundary behind the quotient-unit comparisons between finite quotient systems. -/
def compatibleGroupFamiliesMulEquiv
    {ι : Type*} [Preorder ι]
    (G H : ι → Type*) [∀ i, Group (G i)] [∀ i, Group (H i)]
    (transitionG : ∀ {i j : ι}, i ≤ j → G j →* G i)
    (transitionH : ∀ {i j : ι}, i ≤ j → H j →* H i)
    (e : ∀ i, G i ≃* H i)
    (hcomm : ∀ {i j : ι} (hij : i ≤ j) (x : G j),
      transitionH hij (e j x) = e i (transitionG hij x)) :
    compatibleGroupFamilies G transitionG ≃*
      compatibleGroupFamilies H transitionH where
  toFun x :=
    ⟨fun i => e i (x.1 i), by
      intro i j hij
      rw [hcomm hij, x.2 hij]⟩
  invFun y :=
    ⟨fun i => (e i).symm (y.1 i), by
      intro i j hij
      apply (e i).injective
      calc
        e i (transitionG hij ((e j).symm (y.1 j))) =
            transitionH hij (e j ((e j).symm (y.1 j))) :=
          (hcomm hij ((e j).symm (y.1 j))).symm
        _ = transitionH hij (y.1 j) := by rw [(e j).apply_symm_apply]
        _ = y.1 i := y.2 hij
        _ = e i ((e i).symm (y.1 i)) := by rw [(e i).apply_symm_apply]
      ⟩
  left_inv x := by
    ext i
    exact (e i).symm_apply_apply (x.1 i)
  right_inv y := by
    ext i
    exact (e i).apply_symm_apply (y.1 i)
  map_mul' x y := by
    ext i
    exact (e i).map_mul (x.1 i) (y.1 i)

end LubinTate
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Topology_Models
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Topological API for `WithTopology`

This file adds only the two topology lemmas used by valuation theory. The
underlying type, topology, and basic API come directly from Mathlib. Algebraic
structures needed on a particular topology-indexed copy are installed at that
copy's owner rather than globally in the root `WithTopology` namespace.
-/

universe u v

namespace WithTopology

variable {X : Type u} {t : TopologicalSpace X}

/-- The canonical homeomorphism from Mathlib's topology-indexed copy to its
underlying carrier equipped with the indexed topology. -/
def homeomorph {α : Type u} {topology : TopologicalSpace α} :
    @Homeomorph (WithTopology α topology) α
      (inferInstance : TopologicalSpace (WithTopology α topology)) topology where
  toEquiv := WithTopology.equiv α topology
  continuous_toFun := continuous_ofTopology topology
  continuous_invFun := continuous_toTopology topology

end WithTopology
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Topology_AdicCompletionInverseLimitRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Adic completion and inverse limits

This file contains the algebraic and topological projective-limit descriptions
of adically complete rings, complete discrete valuation rings, and their unit
groups.
-/

noncomputable section

namespace LubinTate
namespace Valuations

open ValuationTheory.DiscreteValuationField
open ValuationTheory.Valuations
open Filter Set Topology
open scoped Valued

/-- The adic inverse-limit equivalence, algebraic form: an adically complete ring is canonically
isomorphic to its adic completion. -/
def adicCompletionAlgEquiv
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    R ≃ₐ[R] AdicCompletion I R :=
  AdicCompletion.ofAlgEquiv I

/-- A finite adic quotient with its discrete topology fixed in the type. -/
structure DiscreteAdicQuotient
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) where
  /-- The underlying residue class modulo `I ^ n`. -/
  val : R ⧸ I ^ n

namespace DiscreteAdicQuotient

/-- Defines `equiv`. -/
def equiv {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    DiscreteAdicQuotient I n ≃ R ⧸ I ^ n where
  toFun := val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/-- Each adic quotient is equipped with the discrete topology. -/
instance instTopologicalSpace {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    TopologicalSpace (DiscreteAdicQuotient I n) := ⊥

/-- The selected topology on an adic quotient is discrete. -/
instance instDiscreteTopology {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    DiscreteTopology (DiscreteAdicQuotient I n) :=
  ⟨rfl⟩

/-- Defines `of`. -/
def of {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : R ⧸ I ^ n) : DiscreteAdicQuotient I n :=
  ⟨x⟩

/-- Forgetting the discrete adic wrapper after insertion recovers the original quotient element. -/
@[simp]
theorem val_of {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : R ⧸ I ^ n) : (of I n x).val = x :=
  rfl

/-- The explicit boundary homeomorphism to the raw quotient equipped with
the discrete topology. -/
def homeomorph {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    @Homeomorph (DiscreteAdicQuotient I n) (R ⧸ I ^ n)
      (inferInstance : TopologicalSpace (DiscreteAdicQuotient I n))
      (⊥ : TopologicalSpace (R ⧸ I ^ n)) := by
  letI : TopologicalSpace (R ⧸ I ^ n) := ⊥
  letI : DiscreteTopology (R ⧸ I ^ n) := ⟨rfl⟩
  exact
    { toEquiv := equiv I n
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The discrete adic homeomorphism evaluates as the underlying quotient equivalence. -/
@[simp]
theorem homeomorph_apply {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : DiscreteAdicQuotient I n) : homeomorph I n x = x.val :=
  rfl

/-- The inverse quotient equivalence inserts a concrete quotient into its discrete copy. -/
@[simp]
theorem equiv_symm_apply {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) (x : R ⧸ I ^ n) :
    (equiv I n).symm x = of I n x :=
  rfl

end DiscreteAdicQuotient

/-- The adic inverse-limit object `lim_n R/I^n`.  This is an opaque public
type; its compatible-family implementation is exposed only through the named
equivalence and coordinate API below. -/
def adicQuotientInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) : Type _ :=
  compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ n)
    (fun {_ _} hmn => Ideal.Quotient.factorPow I hmn)

/-- The implementation representation of the all-level adic inverse limit. -/
def adicQuotientInverseLimitCompatibleFamiliesEquiv
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicQuotientInverseLimit I ≃
      compatibleRingFamilies (fun n : ℕ => R ⧸ I ^ n)
        (fun {_ _} hmn => Ideal.Quotient.factorPow I hmn) := by
  unfold adicQuotientInverseLimit
  exact Equiv.refl _

/-- Compatible adic quotient families form a commutative ring coordinatewise. -/
instance adicQuotientInverseLimit.instCommRing
    {R : Type*} [CommRing R] (I : Ideal R) :
    CommRing (adicQuotientInverseLimit I) :=
  (adicQuotientInverseLimitCompatibleFamiliesEquiv I).commRing

/-- Build an all-level adic inverse-limit point from a compatible family. -/
def adicQuotientInverseLimit_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, R ⧸ I ^ n)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Ideal.Quotient.factorPow I hmn (x n) = x m) :
    adicQuotientInverseLimit I :=
  (adicQuotientInverseLimitCompatibleFamiliesEquiv I).symm
    ⟨x, compatible⟩

/-- Coordinate evaluation from the explicit projective limit. -/
def adicQuotientInverseLimit_eval
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    adicQuotientInverseLimit I →+* R ⧸ I ^ n where
  toFun x := (adicQuotientInverseLimitCompatibleFamiliesEquiv I x).1 n
  map_one' := by rfl
  map_mul' _ _ := by rfl
  map_zero' := by rfl
  map_add' _ _ := by rfl

/-- Evaluation of an adic inverse-limit family returns its component at the selected level. -/
@[simp]
theorem adicQuotientInverseLimit_eval_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, R ⧸ I ^ n)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Ideal.Quotient.factorPow I hmn (x n) = x m)
    (n : ℕ) :
    adicQuotientInverseLimit_eval I n
        (adicQuotientInverseLimit_mk I x compatible) = x n := by
  rfl

/-- Adic inverse-limit elements are equal when all coordinate evaluations agree. -/
@[ext]
theorem adicQuotientInverseLimit_ext
    {R : Type*} [CommRing R] (I : Ideal R)
    {x y : adicQuotientInverseLimit I}
    (h : ∀ n : ℕ, adicQuotientInverseLimit_eval I n x =
      adicQuotientInverseLimit_eval I n y) :
    x = y := by
  apply (adicQuotientInverseLimitCompatibleFamiliesEquiv I).injective
  apply Subtype.ext
  funext n
  exact h n

/-- The explicit projective-limit coordinates are compatible with quotient
transition maps. -/
theorem adicQuotientInverseLimit_eval_factorPow
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n)
    (x : adicQuotientInverseLimit I) :
    Ideal.Quotient.factorPow I hmn
        (adicQuotientInverseLimit_eval I n x) =
      adicQuotientInverseLimit_eval I m x :=
  (adicQuotientInverseLimitCompatibleFamiliesEquiv I x).2 hmn

/-- The quotient algebra equivalence induced by equal ideals sends inverse
representatives as expected. -/
theorem quotientEquivAlgOfEq_apply_symm
    {R : Type*} [CommRing R] {I J : Ideal R}
    (h₁ h₂ : I = J) (y : R ⧸ J) :
    (Ideal.quotientEquivAlgOfEq R h₁)
      ((Ideal.quotientEquivAlgOfEq R h₂).symm y) = y := by
  refine Quotient.inductionOn' y ?_
  intro r
  rw [Ideal.quotientEquivAlgOfEq_symm]
  change (Ideal.quotientEquivAlgOfEq R h₁)
      ((Ideal.quotientEquivAlgOfEq R h₂.symm) (Ideal.Quotient.mk J r)) =
    Ideal.Quotient.mk J r
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rw [Ideal.quotientEquivAlgOfEq_mk]

/-- Adic transition maps commute with quotient equivalences arising from equal powers. -/
theorem transitionMap_quotientEquivAlgOfEq
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n)
    (hm : (I ^ m • ⊤ : Ideal R) = I ^ m)
    (hn : (I ^ n • ⊤ : Ideal R) = I ^ n)
    (y : R ⧸ I ^ n) :
    (Ideal.quotientEquivAlgOfEq R hm)
      (AdicCompletion.transitionMap I R hmn
        ((Ideal.quotientEquivAlgOfEq R hn).symm y)) =
      Ideal.Quotient.factorPow I hmn y := by
  refine Quotient.inductionOn' y ?_
  intro r
  rw [Ideal.quotientEquivAlgOfEq_symm]
  change (Ideal.quotientEquivAlgOfEq R hm)
      (AdicCompletion.transitionMap I R hmn
        ((Ideal.quotientEquivAlgOfEq R hn.symm)
          (Ideal.Quotient.mk (I ^ n) r))) =
    Ideal.Quotient.factorPow I hmn (Ideal.Quotient.mk (I ^ n) r)
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rw [AdicCompletion.transitionMap_ideal_mk]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- The finite quotient coordinates of an adic-completion point are compatible
under the transition maps. -/
theorem adicCompletion_eval_factorPow
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (z : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n z) =
      AdicCompletion.evalₐ I m z := by
  rcases AdicCompletion.mk_surjective I R z with ⟨seq, rfl⟩
  simpa [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow] using
    (AdicCompletion.Ideal.mk_eq_mk I hmn seq)

/-- The map from the adic completion to the explicit projective limit
`lim_n R/I^n`. -/
def adicCompletion_toQuotientInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) :
    AdicCompletion I R → adicQuotientInverseLimit I :=
  fun z =>
    adicQuotientInverseLimit_mk I
      (fun n => AdicCompletion.evalₐ I n z)
      (fun hmn => adicCompletion_eval_factorPow I hmn z)

/-- The inverse map from the explicit projective limit `lim_n R/I^n` to the
adic completion. -/
def adicQuotientInverseLimit_toCompletion
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicQuotientInverseLimit I → AdicCompletion I R :=
  fun x =>
    ⟨fun n =>
      let h : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext r; simp
      (Ideal.quotientEquivAlgOfEq R h).symm
        (adicQuotientInverseLimit_eval I n x),
    by
      intro m n hmn
      let hm : (I ^ m • ⊤ : Ideal R) = I ^ m := by ext r; simp
      let hn : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext r; simp
      apply (Ideal.quotientEquivAlgOfEq R hm).injective
      rw [transitionMap_quotientEquivAlgOfEq I hmn hm hn]
      rw [quotientEquivAlgOfEq_apply_symm]
      exact adicQuotientInverseLimit_eval_factorPow I hmn x⟩

/-- The map from the adic inverse limit to the completion has the prescribed
residue at every level. -/
theorem adicQuotientInverseLimit_toCompletion_eval
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : adicQuotientInverseLimit I) (n : ℕ) :
    AdicCompletion.evalₐ I n
        (adicQuotientInverseLimit_toCompletion I x) =
      adicQuotientInverseLimit_eval I n x := by
  change (Ideal.quotientEquivAlgOfEq R (by ext r; simp))
      ((adicQuotientInverseLimit_toCompletion I x).val n) =
    adicQuotientInverseLimit_eval I n x
  dsimp [adicQuotientInverseLimit_toCompletion]
  rw [quotientEquivAlgOfEq_apply_symm]

/-- Mapping an inverse-limit family to the completion and back recovers the family. -/
theorem adicQuotientInverseLimit_left_inverse
    {R : Type*} [CommRing R] (I : Ideal R) (z : AdicCompletion I R) :
    adicQuotientInverseLimit_toCompletion I
        (adicCompletion_toQuotientInverseLimit I z) = z := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [adicQuotientInverseLimit_toCompletion_eval]
  rfl

/-- Mapping a completion element to its residue family and back recovers the element. -/
theorem adicQuotientInverseLimit_right_inverse
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : adicQuotientInverseLimit I) :
    adicCompletion_toQuotientInverseLimit I
        (adicQuotientInverseLimit_toCompletion I x) = x := by
  ext n
  change AdicCompletion.evalₐ I n
      (adicQuotientInverseLimit_toCompletion I x) =
    adicQuotientInverseLimit_eval I n x
  rw [adicQuotientInverseLimit_toCompletion_eval]

/-- The adic inverse-limit equivalence, algebraic projective-limit form:
the adic completion is canonically isomorphic to `lim_n R/I^n`. -/
def adicCompletion_equiv_quotientInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) :
    AdicCompletion I R ≃+* adicQuotientInverseLimit I where
  toFun := adicCompletion_toQuotientInverseLimit I
  invFun := adicQuotientInverseLimit_toCompletion I
  left_inv := adicQuotientInverseLimit_left_inverse I
  right_inv := adicQuotientInverseLimit_right_inverse I
  map_mul' x y := by
    ext n
    change AdicCompletion.evalₐ I n (x * y) =
      AdicCompletion.evalₐ I n x * AdicCompletion.evalₐ I n y
    simp
  map_add' x y := by
    ext n
    change AdicCompletion.evalₐ I n (x + y) =
      AdicCompletion.evalₐ I n x + AdicCompletion.evalₐ I n y
    simp

end Valuations
end LubinTate
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Topology_AdicCompletionInverseLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Adic unit and higher-unit inverse limits

This file contains the algebraic and topological projective-limit descriptions
of unit groups of adically complete rings and complete discrete valuation
rings.  The underlying adic ring inverse-limit theory lives in
`AdicCompletionInverseLimitRing`.
-/

noncomputable section

namespace LubinTate
namespace Valuations

universe u v

open ValuationTheory.DiscreteValuationField
open ValuationTheory.Valuations
open Filter Set Topology
open scoped Valued

/-- The adic inverse-limit equivalence, unit form of the canonical adic-completion isomorphism. -/
def adicCompletionUnitsEquiv
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    Rˣ ≃* (AdicCompletion I R)ˣ :=
  Units.mapEquiv (adicCompletionAlgEquiv I).toRingEquiv.toMulEquiv

/-- The opaque projective-limit object `lim_n (R/I^n)^*` for quotient-unit
groups. -/
def adicUnitInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) : Type _ :=
  compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ n)ˣ)
    (fun {_ _} hmn =>
      Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom)

/-- Defines `adicUnitInverseLimitCompatibleFamiliesEquiv`. -/
def adicUnitInverseLimitCompatibleFamiliesEquiv
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicUnitInverseLimit I ≃
      compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ n)ˣ)
        (fun {_ _} hmn =>
          Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom) := by
  unfold adicUnitInverseLimit
  exact Equiv.refl _

/-- Compatible unit families form a commutative group under coordinatewise multiplication. -/
instance adicUnitInverseLimit.instCommGroup
    {R : Type*} [CommRing R] (I : Ideal R) :
    CommGroup (adicUnitInverseLimit I) :=
  (adicUnitInverseLimitCompatibleFamiliesEquiv I).commGroup

/-- Defines `adicUnitInverseLimit_mk`. -/
def adicUnitInverseLimit_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, (R ⧸ I ^ n)ˣ)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom (x n) = x m) :
    adicUnitInverseLimit I :=
  (adicUnitInverseLimitCompatibleFamiliesEquiv I).symm ⟨x, compatible⟩

/-- Defines `adicUnitInverseLimit_eval`. -/
def adicUnitInverseLimit_eval
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    adicUnitInverseLimit I →* (R ⧸ I ^ n)ˣ where
  toFun x := (adicUnitInverseLimitCompatibleFamiliesEquiv I x).1 n
  map_one' := by rfl
  map_mul' _ _ := by rfl

/-- Evaluation of a compatible unit family returns its component at the selected level. -/
@[simp]
theorem adicUnitInverseLimit_eval_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, (R ⧸ I ^ n)ˣ)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom (x n) = x m)
    (n : ℕ) :
    adicUnitInverseLimit_eval I n (adicUnitInverseLimit_mk I x compatible) =
      x n := by
  rfl

/-- Two adic unit inverse-limit elements are equal when all evaluations agree. -/
@[ext]
theorem adicUnitInverseLimit_ext
    {R : Type*} [CommRing R] (I : Ideal R)
    {x y : adicUnitInverseLimit I}
    (h : ∀ n : ℕ, adicUnitInverseLimit_eval I n x =
      adicUnitInverseLimit_eval I n y) :
    x = y := by
  apply (adicUnitInverseLimitCompatibleFamiliesEquiv I).injective
  apply Subtype.ext
  funext n
  exact h n

/-- Evaluation commutes with the transition map between adic quotient levels. -/
theorem adicUnitInverseLimit_eval_transition
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : adicUnitInverseLimit I) :
    Units.map (Ideal.Quotient.factorPow I hmn).toMonoidHom
        (adicUnitInverseLimit_eval I n x) =
      adicUnitInverseLimit_eval I m x :=
  (adicUnitInverseLimitCompatibleFamiliesEquiv I x).2 hmn

/-- Units of the explicit projective-limit ring are the same as compatible
families of units in the finite quotient rings. -/
def adicQuotientInverseLimitUnitsEquiv
    {R : Type*} [CommRing R] (I : Ideal R) :
    (adicQuotientInverseLimit I)ˣ ≃*
      adicUnitInverseLimit I where
  toFun u := adicUnitInverseLimit_mk I
    (fun n => Units.map (adicQuotientInverseLimit_eval I n).toMonoidHom u)
    (fun hmn => by
      ext
      exact adicQuotientInverseLimit_eval_factorPow I hmn
        (u : adicQuotientInverseLimit I))
  invFun u :=
    { val := adicQuotientInverseLimit_mk I
        (fun n => (adicUnitInverseLimit_eval I n u : R ⧸ I ^ n))
        (fun hmn => congrArg Units.val
          (adicUnitInverseLimit_eval_transition I hmn u))
      inv := adicQuotientInverseLimit_mk I
        (fun n =>
          (((adicUnitInverseLimit_eval I n u)⁻¹ : (R ⧸ I ^ n)ˣ) :
            R ⧸ I ^ n))
        (fun hmn => by
          have h := congrArg Units.val
            (congrArg Inv.inv
              (adicUnitInverseLimit_eval_transition I hmn u))
          simpa using h)
      val_inv := by
        ext n
        exact Units.mul_inv (adicUnitInverseLimit_eval I n u)
      inv_val := by
        ext n
        exact Units.inv_mul (adicUnitInverseLimit_eval I n u) }
  left_inv u := by
    ext n
    rfl
  right_inv u := by
    ext n
    rfl
  map_mul' u v := by
    ext n
    rfl

/-- The adic inverse-limit equivalence, units of the adic completion are the projective limit of
the units of the finite quotient rings. -/
def adicCompletionUnitsEquivUnitInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) :
    (AdicCompletion I R)ˣ ≃* adicUnitInverseLimit I :=
  (Units.mapEquiv
      (adicCompletion_equiv_quotientInverseLimit I).toMulEquiv).trans
    (adicQuotientInverseLimitUnitsEquiv I)

/-- The adic inverse-limit equivalence, unit projective-limit form for a complete ring. -/
def unitsEquivUnitInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    Rˣ ≃* adicUnitInverseLimit I :=
  (adicCompletionUnitsEquiv I).trans
    (adicCompletionUnitsEquivUnitInverseLimit I)

/-- The opaque positive-indexed unit inverse limit
`lim_n (R/I^(n+1))ˣ`. -/
def adicPositiveUnitInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) : Type _ :=
  compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ (n + 1))ˣ)
    (fun {_ _} hmn =>
      Units.map
        (Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn)).toMonoidHom)

/-- Defines `adicPositiveUnitInverseLimitCompatibleFamiliesEquiv`. -/
def adicPositiveUnitInverseLimitCompatibleFamiliesEquiv
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicPositiveUnitInverseLimit I ≃
      compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ (n + 1))ˣ)
        (fun {_ _} hmn =>
          Units.map
            (Ideal.Quotient.factorPow I
              (Nat.succ_le_succ hmn)).toMonoidHom) := by
  unfold adicPositiveUnitInverseLimit
  exact Equiv.refl _

/-- Positive-level compatible unit families form a commutative group. -/
instance adicPositiveUnitInverseLimit.instCommGroup
    {R : Type*} [CommRing R] (I : Ideal R) :
    CommGroup (adicPositiveUnitInverseLimit I) :=
  (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I).commGroup

/-- Defines `adicPositiveUnitInverseLimitRepresentation`. -/
def adicPositiveUnitInverseLimitRepresentation
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicPositiveUnitInverseLimit I ≃*
      compatibleGroupFamilies (fun n : ℕ => (R ⧸ I ^ (n + 1))ˣ)
        (fun {_ _} hmn =>
          Units.map
            (Ideal.Quotient.factorPow I
              (Nat.succ_le_succ hmn)).toMonoidHom) :=
  (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I).mulEquiv

/-- Defines `adicPositiveUnitInverseLimit_mk`. -/
def adicPositiveUnitInverseLimit_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, (R ⧸ I ^ (n + 1))ˣ)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Units.map
          (Ideal.Quotient.factorPow I
            (Nat.succ_le_succ hmn)).toMonoidHom (x n) = x m) :
    adicPositiveUnitInverseLimit I :=
  (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I).symm
    ⟨x, compatible⟩

/-- Defines `adicPositiveUnitInverseLimit_eval`. -/
def adicPositiveUnitInverseLimit_eval
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    adicPositiveUnitInverseLimit I →* (R ⧸ I ^ (n + 1))ˣ where
  toFun x :=
    (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I x).1 n
  map_one' := by rfl
  map_mul' _ _ := by rfl

/-- Evaluation of a positive-level unit family returns its chosen component. -/
@[simp]
theorem adicPositiveUnitInverseLimit_eval_mk
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : ∀ n : ℕ, (R ⧸ I ^ (n + 1))ˣ)
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      Units.map
          (Ideal.Quotient.factorPow I
            (Nat.succ_le_succ hmn)).toMonoidHom (x n) = x m)
    (n : ℕ) :
    adicPositiveUnitInverseLimit_eval I n
        (adicPositiveUnitInverseLimit_mk I x compatible) = x n := by
  rfl

/-- Positive adic unit families are determined by all of their components. -/
@[ext]
theorem adicPositiveUnitInverseLimit_ext
    {R : Type*} [CommRing R] (I : Ideal R)
    {x y : adicPositiveUnitInverseLimit I}
    (h : ∀ n : ℕ, adicPositiveUnitInverseLimit_eval I n x =
      adicPositiveUnitInverseLimit_eval I n y) :
    x = y := by
  apply (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I).injective
  apply Subtype.ext
  funext n
  exact h n

/-- Positive-level evaluation respects the adic transition maps. -/
theorem adicPositiveUnitInverseLimit_eval_transition
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : adicPositiveUnitInverseLimit I) :
    Units.map
        (Ideal.Quotient.factorPow I
          (Nat.succ_le_succ hmn)).toMonoidHom
        (adicPositiveUnitInverseLimit_eval I n x) =
      adicPositiveUnitInverseLimit_eval I m x :=
  (adicPositiveUnitInverseLimitCompatibleFamiliesEquiv I x).2 hmn

/-- Defines `adicUnitInverseLimit_toPositive`. -/
def adicUnitInverseLimit_toPositive
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicUnitInverseLimit I →
      adicPositiveUnitInverseLimit I :=
  fun u =>
    adicPositiveUnitInverseLimit_mk I
      (fun n => adicUnitInverseLimit_eval I (n + 1) u)
      (fun hmn => adicUnitInverseLimit_eval_transition I
        (Nat.succ_le_succ hmn) u)

/-- Defines `adicPositiveUnitInverseLimit_toAll`. -/
def adicPositiveUnitInverseLimit_toAll
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicPositiveUnitInverseLimit I →
      adicUnitInverseLimit I :=
  fun u =>
    adicUnitInverseLimit_mk I (fun n => match n with
      | 0 => 1
      | k + 1 => adicPositiveUnitInverseLimit_eval I k u)
    (by
      intro m n hmn
      cases m with
      | zero =>
          ext
          have : Subsingleton (R ⧸ I ^ 0) := by
            simpa only [pow_zero, Ideal.one_eq_top] using
              (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
          exact Subsingleton.elim _ _
      | succ m =>
          cases n with
          | zero => cases hmn
          | succ n =>
              exact adicPositiveUnitInverseLimit_eval_transition I
                (Nat.succ_le_succ_iff.mp hmn) u)

/-- Restricting an all-level unit family to positive levels and extending back is the identity. -/
theorem adicPositiveUnitInverseLimit_toPositive_toAll
    {R : Type*} [CommRing R] (I : Ideal R)
    (u : adicPositiveUnitInverseLimit I) :
    adicUnitInverseLimit_toPositive I
        (adicPositiveUnitInverseLimit_toAll I u) = u := by
  ext n
  rfl

/-- Extending a positive-level unit family and restricting again is the identity. -/
theorem adicUnitInverseLimit_toAll_toPositive
    {R : Type*} [CommRing R] (I : Ideal R)
    (u : adicUnitInverseLimit I) :
    adicPositiveUnitInverseLimit_toAll I
        (adicUnitInverseLimit_toPositive I u) = u := by
  ext n
  cases n with
  | zero =>
      have : Subsingleton (R ⧸ I ^ 0) := by
        simpa only [pow_zero, Ideal.one_eq_top] using
          (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
      exact Subsingleton.elim _ _
  | succ n =>
      rfl

/-- The all-level unit inverse limit is equivalent to the positive-indexed
one.  This removes the degenerate `I^0` coordinate used by mathlib's adic
completion API. -/
def adicUnitInverseLimitEquivPositive
    {R : Type*} [CommRing R] (I : Ideal R) :
    adicUnitInverseLimit I ≃*
      adicPositiveUnitInverseLimit I where
  toFun := adicUnitInverseLimit_toPositive I
  invFun := adicPositiveUnitInverseLimit_toAll I
  left_inv := adicUnitInverseLimit_toAll_toPositive I
  right_inv := adicPositiveUnitInverseLimit_toPositive_toAll I
  map_mul' u v := by
    ext n
    rfl

/-- Complete-ring unit projective-limit form with the positive indexing. -/
def unitsEquivPositiveUnitInverseLimit
    {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    Rˣ ≃* adicPositiveUnitInverseLimit I :=
  (unitsEquivUnitInverseLimit I).trans
    (adicUnitInverseLimitEquivPositive I)

/-- The first principal ideal generated by `π` has powers `π^nO`. -/
theorem dvrPowerIdeal_one_pow
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    (uniformizerPowerIdeal π 1) ^ n = uniformizerPowerIdeal π n := by
  simp [uniformizerPowerIdeal, Ideal.span_singleton_pow]

/-- The principal-power ideals form a decreasing filtration. -/
theorem dvrPowerIdeal_le_of_le
    {O : Type*} [CommRing O] (π : O) {m n : ℕ} (hmn : m ≤ n) :
    uniformizerPowerIdeal π n ≤ uniformizerPowerIdeal π m := by
  rw [← dvrPowerIdeal_one_pow π m,
    ← dvrPowerIdeal_one_pow π n]
  exact Ideal.pow_le_pow_right hmn

/-- Transition map on the finite unit quotients `(O/π^(n+1)O)ˣ`. -/
def dvrPowerIdealUnitTransition
    {O : Type*} [CommRing O] (π : O) {m n : ℕ} (hmn : m ≤ n) :
    O ⧸ uniformizerPowerIdeal π (n + 1) →+*
      O ⧸ uniformizerPowerIdeal π (m + 1) :=
  Ideal.Quotient.factor
    (dvrPowerIdeal_le_of_le π (Nat.succ_le_succ hmn))

/-- The opaque positive-indexed projective limit
`lim_n (O/π^(n+1)O)ˣ`. -/
def dvrPowerIdealUnitInverseLimit
    {O : Type*} [CommRing O] (π : O) : Type _ :=
  compatibleGroupFamilies
    (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
    (fun {_ _} hmn =>
      Units.map
        (dvrPowerIdealUnitTransition π hmn).toMonoidHom)

/-- Defines `dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv`. -/
def dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv
    {O : Type*} [CommRing O] (π : O) :
    dvrPowerIdealUnitInverseLimit π ≃
      compatibleGroupFamilies
        (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
        (fun {_ _} hmn =>
          Units.map
            (dvrPowerIdealUnitTransition π hmn).toMonoidHom) := by
  unfold dvrPowerIdealUnitInverseLimit
  exact Equiv.refl _

/-- Compatible units modulo powers of a DVR element form a commutative group. -/
instance dvrPowerIdealUnitInverseLimit.instCommGroup
    {O : Type*} [CommRing O] (π : O) :
    CommGroup (dvrPowerIdealUnitInverseLimit π) :=
  (dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv π).commGroup

/-- Defines `dvrPowerIdealUnitInverseLimitRepresentation`. -/
def dvrPowerIdealUnitInverseLimitRepresentation
    {O : Type*} [CommRing O] (π : O) :
    dvrPowerIdealUnitInverseLimit π ≃*
      compatibleGroupFamilies
        (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
        (fun {_ _} hmn =>
          Units.map
            (dvrPowerIdealUnitTransition π hmn).toMonoidHom) :=
  (dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv π).mulEquiv

/-- Defines `dvrPowerIdealUnitInverseLimit_eval`. -/
def dvrPowerIdealUnitInverseLimit_eval
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    dvrPowerIdealUnitInverseLimit π →*
      (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ where
  toFun x :=
    (dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv π x).1 n
  map_one' := by rfl
  map_mul' _ _ := by rfl

/-- DVR power-ideal unit families are equal when all coordinate evaluations agree. -/
@[ext]
theorem dvrPowerIdealUnitInverseLimit_ext
    {O : Type*} [CommRing O] (π : O)
    {x y : dvrPowerIdealUnitInverseLimit π}
    (h : ∀ n : ℕ, dvrPowerIdealUnitInverseLimit_eval π n x =
      dvrPowerIdealUnitInverseLimit_eval π n y) :
    x = y := by
  apply (dvrPowerIdealUnitInverseLimitCompatibleFamiliesEquiv π).injective
  apply Subtype.ext
  funext n
  exact h n

/-- The finite quotient-unit stage for `(π)^(n+1)` agrees with the canonical
stage `π^(n+1)O`. -/
def powerIdealStageEquiv
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    (O ⧸ (uniformizerPowerIdeal π 1) ^ (n + 1))ˣ ≃*
      (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ :=
  Units.mapEquiv
    (Ideal.quotientEquivAlgOfEq O
      (dvrPowerIdeal_one_pow π (n + 1))).toRingEquiv.toMulEquiv

/-- The stage equivalences commute with the projective transition maps. -/
theorem powerIdealStageEquiv_factorPow
    {O : Type*} [CommRing O] (π : O) {m n : ℕ} (hmn : m ≤ n)
    (x : O ⧸ (uniformizerPowerIdeal π 1) ^ (n + 1)) :
    (Ideal.quotientEquivAlgOfEq O
      (dvrPowerIdeal_one_pow π (m + 1)))
        (Ideal.Quotient.factorPow (uniformizerPowerIdeal π 1)
          (Nat.succ_le_succ hmn) x) =
      dvrPowerIdealUnitTransition π hmn
        ((Ideal.quotientEquivAlgOfEq O
          (dvrPowerIdeal_one_pow π (n + 1))) x) := by
  refine Quotient.inductionOn' x ?_
  intro r
  change (Ideal.quotientEquivAlgOfEq O
      (dvrPowerIdeal_one_pow π (m + 1)))
        (Ideal.Quotient.factorPow (uniformizerPowerIdeal π 1)
          (Nat.succ_le_succ hmn)
          (Ideal.Quotient.mk ((uniformizerPowerIdeal π 1) ^ (n + 1)) r)) =
      dvrPowerIdealUnitTransition π hmn
        ((Ideal.quotientEquivAlgOfEq O
          (dvrPowerIdeal_one_pow π (n + 1)))
            (Ideal.Quotient.mk ((uniformizerPowerIdeal π 1) ^ (n + 1)) r))
  rw [Ideal.quotientEquivAlgOfEq_mk]
  simp [dvrPowerIdealUnitTransition, Ideal.Quotient.factorPow]

/-- The positive-indexed unit inverse limit for the principal ideal `(π)` is
the finite quotient-unit inverse limit `lim_n (O/π^(n+1)O)ˣ`. -/
def adicPositiveUnitInverseLimitEquivDVRPowerIdealUnitInverseLimit
    {O : Type*} [CommRing O] (π : O) :
    adicPositiveUnitInverseLimit (uniformizerPowerIdeal π 1) ≃*
      dvrPowerIdealUnitInverseLimit π :=
  (adicPositiveUnitInverseLimitRepresentation
      (uniformizerPowerIdeal π 1)).trans
    ((compatibleGroupFamiliesMulEquiv
      (fun n : ℕ => (O ⧸ (uniformizerPowerIdeal π 1) ^ (n + 1))ˣ)
      (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
      (fun {_ _} hmn =>
        Units.map
          (Ideal.Quotient.factorPow (uniformizerPowerIdeal π 1)
            (Nat.succ_le_succ hmn)).toMonoidHom)
      (fun {_ _} hmn =>
        Units.map
          (dvrPowerIdealUnitTransition π hmn).toMonoidHom)
      (fun n => powerIdealStageEquiv π n)
      (by
        intro m n hmn u
        apply Units.ext
        exact (powerIdealStageEquiv_factorPow π hmn (u : _)).symm)).trans
      (dvrPowerIdealUnitInverseLimitRepresentation π).symm)

/-- Transition map on the positive-indexed quotients `Oˣ/U^(n+1)`. -/
def dvrHigherUnitQuotientTransition
    {O : Type*} [CommRing O] (π : O) {m n : ℕ} (hmn : m ≤ n) :
    Oˣ ⧸ higherUnitSubgroup π (n + 1) →*
      Oˣ ⧸ higherUnitSubgroup π (m + 1) :=
  QuotientGroup.map _ _ (MonoidHom.id Oˣ) <| by
    intro u hu
    exact higherUnitSubgroup_le_of_le π (Nat.succ_le_succ hmn) hu

theorem dvrHigherUnitQuotientTransition_mk
    {O : Type*} [CommRing O] (π : O) {m n : ℕ} (hmn : m ≤ n) (u : Oˣ) :
    dvrHigherUnitQuotientTransition π hmn
        (u : Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
      (u : Oˣ ⧸ higherUnitSubgroup π (m + 1)) := by
  have hmap :
      higherUnitSubgroup π (n + 1) ≤
        (higherUnitSubgroup π (m + 1)).comap (MonoidHom.id Oˣ) := by
    intro x hx
    exact higherUnitSubgroup_le_of_le π (Nat.succ_le_succ hmn) hx
  unfold dvrHigherUnitQuotientTransition
  exact QuotientGroup.map_mk
    (N := higherUnitSubgroup π (n + 1))
    (higherUnitSubgroup π (m + 1)) (MonoidHom.id Oˣ) hmap u

/-- A higher-unit quotient with discreteness fixed in its type. -/
structure DiscreteHigherUnitQuotient
    {O : Type*} [CommRing O] (π : O) (n : ℕ) where
  /-- The underlying higher-unit quotient class. -/
  val : Oˣ ⧸ higherUnitSubgroup π n

namespace DiscreteHigherUnitQuotient

/-- Defines `equiv`. -/
def equiv {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    DiscreteHigherUnitQuotient π n ≃
      Oˣ ⧸ higherUnitSubgroup π n where
  toFun := val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/-- Each higher-unit quotient is equipped with the discrete topology. -/
instance instTopologicalSpace {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    TopologicalSpace (DiscreteHigherUnitQuotient π n) := ⊥

/-- The chosen topology on a higher-unit quotient is discrete. -/
instance instDiscreteTopology {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    DiscreteTopology (DiscreteHigherUnitQuotient π n) :=
  ⟨rfl⟩

/-- Defines `of`. -/
def of {O : Type*} [CommRing O] (π : O) (n : ℕ)
    (x : Oˣ ⧸ higherUnitSubgroup π n) :
    DiscreteHigherUnitQuotient π n :=
  ⟨x⟩

/-- Forgetting the discrete wrapper after inserting a quotient element recovers that element. -/
@[simp]
theorem val_of {O : Type*} [CommRing O] (π : O) (n : ℕ)
    (x : Oˣ ⧸ higherUnitSubgroup π n) : (of π n x).val = x :=
  rfl

/-- Defines `homeomorph`. -/
def homeomorph {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    @Homeomorph (DiscreteHigherUnitQuotient π n)
      (Oˣ ⧸ higherUnitSubgroup π n)
      (inferInstance : TopologicalSpace
        (DiscreteHigherUnitQuotient π n))
      (⊥ : TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π n)) := by
  letI : TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π n) := ⊥
  letI : DiscreteTopology (Oˣ ⧸ higherUnitSubgroup π n) := ⟨rfl⟩
  exact
    { toEquiv := equiv π n
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The discrete comparison homeomorphism acts as the underlying quotient equivalence. -/
@[simp]
theorem homeomorph_apply {O : Type*} [CommRing O] (π : O) (n : ℕ)
    (x : DiscreteHigherUnitQuotient π n) : homeomorph π n x = x.val :=
  rfl

/-- The inverse discrete quotient equivalence wraps the concrete quotient element. -/
@[simp]
theorem equiv_symm_apply {O : Type*} [CommRing O]
    (π : O) (n : ℕ) (x : Oˣ ⧸ higherUnitSubgroup π n) :
    (equiv π n).symm x = of π n x :=
  rfl

end DiscreteHigherUnitQuotient

/-- The opaque direct quotient-system object `lim_n Oˣ/U^(n+1)`. -/
def dvrHigherUnitQuotientInverseLimit
    {O : Type*} [CommRing O] (π : O) : Type _ :=
  compatibleGroupFamilies
    (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
    (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn)

/-- Defines `dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv`. -/
def dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv
    {O : Type*} [CommRing O] (π : O) :
    dvrHigherUnitQuotientInverseLimit π ≃
      compatibleGroupFamilies
        (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
        (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) := by
  unfold dvrHigherUnitQuotientInverseLimit
  exact Equiv.refl _

/-- The inverse limit of higher-unit quotients is a commutative group. -/
instance dvrHigherUnitQuotientInverseLimit.instCommGroup
    {O : Type*} [CommRing O] (π : O) :
    CommGroup (dvrHigherUnitQuotientInverseLimit π) :=
  (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).commGroup

/-- Defines `dvrHigherUnitQuotientInverseLimitRepresentation`. -/
def dvrHigherUnitQuotientInverseLimitRepresentation
    {O : Type*} [CommRing O] (π : O) :
    dvrHigherUnitQuotientInverseLimit π ≃*
      compatibleGroupFamilies
        (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
        (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) :=
  (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).mulEquiv

/-- Defines `dvrHigherUnitQuotientInverseLimit_mk`. -/
def dvrHigherUnitQuotientInverseLimit_mk
    {O : Type*} [CommRing O] (π : O)
    (x : ∀ n : ℕ, Oˣ ⧸ higherUnitSubgroup π (n + 1))
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      dvrHigherUnitQuotientTransition π hmn (x n) = x m) :
    dvrHigherUnitQuotientInverseLimit π :=
  (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).symm
    ⟨x, compatible⟩

/-- Defines `dvrHigherUnitQuotientInverseLimit_eval`. -/
def dvrHigherUnitQuotientInverseLimit_eval
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    dvrHigherUnitQuotientInverseLimit π →*
      Oˣ ⧸ higherUnitSubgroup π (n + 1) where
  toFun x :=
    (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π x).1 n
  map_one' := by rfl
  map_mul' _ _ := by rfl

/-- Evaluation of a higher-unit inverse-limit family returns its selected quotient component. -/
@[simp]
theorem dvrHigherUnitQuotientInverseLimit_eval_mk
    {O : Type*} [CommRing O] (π : O)
    (x : ∀ n : ℕ, Oˣ ⧸ higherUnitSubgroup π (n + 1))
    (compatible : ∀ {m n : ℕ} (hmn : m ≤ n),
      dvrHigherUnitQuotientTransition π hmn (x n) = x m)
    (n : ℕ) :
    dvrHigherUnitQuotientInverseLimit_eval π n
        (dvrHigherUnitQuotientInverseLimit_mk π x compatible) = x n := by
  rfl

/-- Higher-unit inverse-limit elements are determined by their evaluations at every level. -/
@[ext]
theorem dvrHigherUnitQuotientInverseLimit_ext
    {O : Type*} [CommRing O] (π : O)
    {x y : dvrHigherUnitQuotientInverseLimit π}
    (h : ∀ n : ℕ, dvrHigherUnitQuotientInverseLimit_eval π n x =
      dvrHigherUnitQuotientInverseLimit_eval π n y) :
    x = y := by
  apply (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).injective
  apply Subtype.ext
  funext n
  exact h n

/-- The higher-unit inverse limit carries the topology induced by its discrete coordinates. -/
noncomputable instance dvrHigherUnitQuotientInverseLimit.instTopologicalSpace
    {O : Type*} [CommRing O] (π : O) :
    TopologicalSpace (dvrHigherUnitQuotientInverseLimit π) := by
  letI : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  exact
    (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).topologicalSpace

noncomputable def
    dvrHigherUnitQuotientInverseLimitRepresentationHomeomorph
    {O : Type*} [CommRing O] (π : O) :
    letI : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
    dvrHigherUnitQuotientInverseLimit π ≃ₜ
      compatibleGroupFamilies
        (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
        (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) := by
  letI : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  exact
    (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π).homeomorph

/-- Defines `dvrHigherUnitQuotientInverseLimit_discreteEval`. -/
def dvrHigherUnitQuotientInverseLimit_discreteEval
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    dvrHigherUnitQuotientInverseLimit π →
      DiscreteHigherUnitQuotient π (n + 1) :=
  fun x => DiscreteHigherUnitQuotient.of π (n + 1)
    (dvrHigherUnitQuotientInverseLimit_eval π n x)

/-- Every coordinate evaluation from the higher-unit inverse limit to its
discrete quotient is continuous. -/
theorem dvrHigherUnitQuotientInverseLimit_discreteEval_continuous
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    Continuous (dvrHigherUnitQuotientInverseLimit_discreteEval π n) := by
  let : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  let representation :=
    dvrHigherUnitQuotientInverseLimitRepresentationHomeomorph π
  have hraw : Continuous fun x : dvrHigherUnitQuotientInverseLimit π =>
      (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π x).1 n :=
    (continuous_apply n).comp
      (continuous_subtype_val.comp representation.continuous)
  have hmodel :=
    (DiscreteHigherUnitQuotient.homeomorph π (n + 1)).symm.continuous.comp
      hraw
  change Continuous (fun x : dvrHigherUnitQuotientInverseLimit π =>
    (DiscreteHigherUnitQuotient.equiv π (n + 1)).symm
      ((dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π x).1 n)) at hmodel
  change Continuous (fun x : dvrHigherUnitQuotientInverseLimit π =>
    (DiscreteHigherUnitQuotient.equiv π (n + 1)).symm
      ((dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π x).1 n))
  exact hmodel

/-- A map into the higher-unit inverse limit is continuous exactly when all
of its named discrete coordinates are continuous.  This is the public
universal property of the canonical prodiscrete topology; raw quotient
topology instances remain confined to the proof. -/
theorem dvrHigherUnitQuotientInverseLimit_continuous_iff
    {O : Type*} [CommRing O] {α : Type*} [TopologicalSpace α]
    (π : O) (f : α → dvrHigherUnitQuotientInverseLimit π) :
    Continuous f ↔
      ∀ n : ℕ, Continuous fun x =>
        dvrHigherUnitQuotientInverseLimit_discreteEval π n (f x) := by
  constructor
  · intro hf n
    exact
      (dvrHigherUnitQuotientInverseLimit_discreteEval_continuous π n).comp hf
  · intro h
    let : (n : ℕ) → TopologicalSpace
        (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
    let : (n : ℕ) → DiscreteTopology
        (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⟨rfl⟩
    let representation :=
      dvrHigherUnitQuotientInverseLimitRepresentationHomeomorph π
    have hrepresentation : Continuous fun x => representation (f x) :=
      Continuous.subtype_mk
        (continuous_pi fun n => by
          have hraw :=
            (DiscreteHigherUnitQuotient.homeomorph π (n + 1)).continuous.comp
              (h n)
          change Continuous fun x =>
            dvrHigherUnitQuotientInverseLimit_eval π n (f x)
          exact hraw)
        (fun x => by
          change ∀ {i j : ℕ} (hij : i ≤ j),
            dvrHigherUnitQuotientTransition π hij
                ((dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π
                  (f x)).1 j) =
              (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π
                (f x)).1 i
          exact
            (dvrHigherUnitQuotientInverseLimitCompatibleFamiliesEquiv π
              (f x)).2)
    have hback := representation.symm.continuous.comp hrepresentation
    exact hback.congr fun x => representation.symm_apply_apply (f x)

/-- The canonical homomorphism
`Oˣ → lim_n Oˣ/U^(n+1)`. -/
def unitsToHigherUnitQuotientInverseLimit
    {O : Type*} [CommRing O] (π : O) :
    Oˣ →* dvrHigherUnitQuotientInverseLimit π where
  toFun u := dvrHigherUnitQuotientInverseLimit_mk π
    (fun _ => QuotientGroup.mk u)
    (fun {m n} hmn =>
      dvrHigherUnitQuotientTransition_mk π (m := m) (n := n) hmn u)
  map_one' := by ext n; rfl
  map_mul' u v := by ext n; rfl

/-- The finite-stage isomorphisms
`Oˣ/U^(n+1) ≃ (O/π^(n+1)O)ˣ` commute with the projective transition maps. -/
theorem higherUnitQuotient_finiteStage_compat
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m n : ℕ} (hmn : m ≤ n)
    (q : Oˣ ⧸ higherUnitSubgroup π (n + 1)) :
    units_quotient_equiv hπ
        (Nat.succ_pos m)
        (dvrHigherUnitQuotientTransition π hmn q) =
      Units.map (dvrPowerIdealUnitTransition π hmn).toMonoidHom
        (units_quotient_equiv hπ
          (Nat.succ_pos n) q) := by
  refine QuotientGroup.induction_on q ?_
  intro u
  rw [dvrHigherUnitQuotientTransition_mk]
  ext
  simp [units_quotient_equiv_mk,
    dvrPowerIdealUnitTransition, unitReduction]

/-- The direct quotient-system `lim Oˣ/U^(n+1)` is equivalent to the finite
quotient-unit limit `lim (O/π^(n+1)O)ˣ`. -/
def higherUnitQuotientInverseLimitEquivPowerIdealUnitInverseLimit
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) :
    dvrHigherUnitQuotientInverseLimit π ≃*
      dvrPowerIdealUnitInverseLimit π :=
  (dvrHigherUnitQuotientInverseLimitRepresentation π).trans
    ((compatibleGroupFamiliesMulEquiv
      (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
      (fun n : ℕ => (O ⧸ uniformizerPowerIdeal π (n + 1))ˣ)
      (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn)
      (fun {_ _} hmn =>
        Units.map
          (dvrPowerIdealUnitTransition π hmn).toMonoidHom)
      (fun n => units_quotient_equiv hπ
        (Nat.succ_pos n))
      (by
        intro m n hmn q
        exact (higherUnitQuotient_finiteStage_compat
          hπ hmn q).symm)).trans
      (dvrPowerIdealUnitInverseLimitRepresentation π).symm)

/-- The adic inverse-limit equivalence, direct unit-quotient form:
if `O` is complete for the `(π)`-adic topology, then `Oˣ` is isomorphic to
the projective limit `lim_n Oˣ/U^(n+1)`. -/
def dvrUnitsEquivHigherUnitQuotientInverseLimit
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) [IsAdicComplete (uniformizerPowerIdeal π 1) O] :
    Oˣ ≃* dvrHigherUnitQuotientInverseLimit π :=
  ((unitsEquivPositiveUnitInverseLimit (uniformizerPowerIdeal π 1)).trans
    (adicPositiveUnitInverseLimitEquivDVRPowerIdealUnitInverseLimit π)).trans
    (higherUnitQuotientInverseLimitEquivPowerIdealUnitInverseLimit hπ).symm

/-- The direct unit-quotient inverse-limit isomorphism is the canonical
map, coordinatewise `u ↦ u mod U^(n+1)`. -/
theorem dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) [IsAdicComplete (uniformizerPowerIdeal π 1) O]
    (u : Oˣ) (n : ℕ) :
    dvrHigherUnitQuotientInverseLimit_eval π n
        (dvrUnitsEquivHigherUnitQuotientInverseLimit hπ u) =
      QuotientGroup.mk u := by
  apply
    (units_quotient_equiv hπ
      (Nat.succ_pos n)).injective
  change units_quotient_equiv hπ (Nat.succ_pos n)
      (dvrHigherUnitQuotientInverseLimit_eval π n
        (dvrUnitsEquivHigherUnitQuotientInverseLimit hπ u)) =
    units_quotient_equiv hπ (Nat.succ_pos n)
      (QuotientGroup.mk u)
  rw [units_quotient_equiv_mk]
  change dvrPowerIdealUnitInverseLimit_eval π n
      ((higherUnitQuotientInverseLimitEquivPowerIdealUnitInverseLimit hπ)
        (dvrUnitsEquivHigherUnitQuotientInverseLimit hπ u)) =
    unitReduction (uniformizerPowerIdeal π (n + 1)) u
  simp [dvrUnitsEquivHigherUnitQuotientInverseLimit,
    adicPositiveUnitInverseLimitEquivDVRPowerIdealUnitInverseLimit,
    unitReduction]
  ext
  change (Ideal.quotientEquivAlgOfEq O
      (dvrPowerIdeal_one_pow π (n + 1)))
        (Ideal.Quotient.mk ((uniformizerPowerIdeal π 1) ^ (n + 1)) (u : O)) =
    Ideal.Quotient.mk (uniformizerPowerIdeal π (n + 1)) (u : O)
  rw [Ideal.quotientEquivAlgOfEq_mk]

/-- Equality in the finite higher-unit quotient is exactly congruence modulo
`π^nO` on the underlying elements. -/
theorem higherUnitQuotient_mk_eq_mk_iff_sub_mem
    {O : Type*} [CommRing O] (π : O) (n : ℕ) (u v : Oˣ) :
    (QuotientGroup.mk v : Oˣ ⧸ higherUnitSubgroup π n) =
        QuotientGroup.mk u ↔
      (v : O) - (u : O) ∈ uniformizerPowerIdeal π n := by
  constructor
  · intro h
    have hdiv : v / u ∈ higherUnitSubgroup π n := by
      exact (QuotientGroup.eq_iff_div_mem
        (N := higherUnitSubgroup π n) (x := v) (y := u)).1 h
    have hmem :
        ((v / u : Oˣ) : O) - 1 ∈ uniformizerPowerIdeal π n :=
      (mem_higherUnitSubgroup_iff_sub_one_mem_powerIdeal
        (π := π) (n := n) (u := v / u)).1 hdiv
    have hmul :
        (((v / u : Oˣ) : O) - 1) * (u : O) ∈
          uniformizerPowerIdeal π n :=
      (uniformizerPowerIdeal π n).mul_mem_right (u : O) hmem
    have hcalc :
        (((v / u : Oˣ) : O) - 1) * (u : O) = (v : O) - (u : O) := by
      calc
        (((v / u : Oˣ) : O) - 1) * (u : O)
            = ((v : O) * ((u⁻¹ : Oˣ) : O) - 1) * (u : O) := rfl
        _ = (v : O) * (((u⁻¹ : Oˣ) : O) * (u : O)) - (u : O) := by ring
        _ = (v : O) - (u : O) := by simp
    simpa [hcalc] using hmul
  · intro hsub
    have hmem :
        ((v / u : Oˣ) : O) - 1 ∈ uniformizerPowerIdeal π n := by
      have hmul :
          ((v : O) - (u : O)) * ((u⁻¹ : Oˣ) : O) ∈
            uniformizerPowerIdeal π n :=
        (uniformizerPowerIdeal π n).mul_mem_right ((u⁻¹ : Oˣ) : O) hsub
      convert hmul using 1
      all_goals try with_reducible_and_instances rfl
      calc
        ((v / u : Oˣ) : O) - 1
            = (v : O) * ((u⁻¹ : Oˣ) : O) - 1 := rfl
        _ = (v : O) * ((u⁻¹ : Oˣ) : O) -
              (u : O) * ((u⁻¹ : Oˣ) : O) := by simp
        _ = ((v : O) - (u : O)) * ((u⁻¹ : Oˣ) : O) := by ring
    have hdiv : v / u ∈ higherUnitSubgroup π n :=
      (mem_higherUnitSubgroup_iff_sub_one_mem_powerIdeal
        (π := π) (n := n) (u := v / u)).2 hmem
    exact (QuotientGroup.eq_iff_div_mem
      (N := higherUnitSubgroup π n) (x := v) (y := u)).2 hdiv

/-- The topology on a unit group induced by an explicitly chosen adic
topology on its ring. -/
@[reducible]
noncomputable def adicUnitsTopology
    {O : Type*} [CommRing O] (I : Ideal O) : TopologicalSpace Oˣ := by
  letI : TopologicalSpace O := I.adicTopology
  exact inferInstance

/-- Reduction to a higher-unit quotient is continuous for the adic topology
on `Oˣ` and the discrete topology on the finite quotient. -/
theorem higherUnitQuotient_mk_continuous_adic_raw
    {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    @Continuous Oˣ (Oˣ ⧸ higherUnitSubgroup π n)
      (adicUnitsTopology (uniformizerPowerIdeal π 1))
      (⊥ : TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π n))
      (fun u : Oˣ =>
        (QuotientGroup.mk u : Oˣ ⧸ higherUnitSubgroup π n)) := by
  let : TopologicalSpace O := (uniformizerPowerIdeal π 1).adicTopology
  let : TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π n) := ⊥
  let : DiscreteTopology (Oˣ ⧸ higherUnitSubgroup π n) := ⟨rfl⟩
  rw [continuous_iff_continuousAt]
  intro u
  change Filter.Tendsto
    (fun v : Oˣ => (QuotientGroup.mk v :
      Oˣ ⧸ higherUnitSubgroup π n)) (𝓝 u)
    (𝓝 (QuotientGroup.mk u : Oˣ ⧸ higherUnitSubgroup π n))
  rw [@nhds_discrete (Oˣ ⧸ higherUnitSubgroup π n) _ _]
  rw [Filter.tendsto_def]
  intro s hs
  rw [mem_pure] at hs
  let ball : Set O :=
    (fun y => (u : O) + y) ''
      (((uniformizerPowerIdeal π 1) ^ n : Ideal O) : Set O)
  have hball : ball ∈ 𝓝 (u : O) :=
    (Ideal.hasBasis_nhds_adic (uniformizerPowerIdeal π 1) (u : O)).mem_iff.mpr
      ⟨n, trivial, subset_rfl⟩
  have hpre : {v : Oˣ | (v : O) ∈ ball} ∈ 𝓝 u :=
    Units.continuous_val.continuousAt hball
  exact mem_of_superset hpre (by
    intro v hv
    rcases hv with ⟨z, hz, hzv⟩
    have hsub : (v : O) - (u : O) ∈ uniformizerPowerIdeal π n := by
      rw [← dvrPowerIdeal_one_pow π n]
      have hz_eq : (v : O) - (u : O) = z := by
        rw [← hzv]
        ring
      simpa [hz_eq] using hz
    have hq :
        (QuotientGroup.mk v : Oˣ ⧸ higherUnitSubgroup π n) =
          QuotientGroup.mk u :=
      (higherUnitQuotient_mk_eq_mk_iff_sub_mem
        π n u v).2 hsub
    simpa [hq] using hs)

noncomputable def unitsCompatibleFamiliesHomeomorph
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) [IsAdicComplete (uniformizerPowerIdeal π 1) O] :
    letI : TopologicalSpace O := (uniformizerPowerIdeal π 1).adicTopology
    letI : (n : ℕ) →
      TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
    Oˣ ≃ₜ compatibleGroupFamilies
      (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
      (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) := by
  letI : TopologicalSpace O := (uniformizerPowerIdeal π 1).adicTopology
  letI : (n : ℕ) →
      TopologicalSpace (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  letI : (n : ℕ) →
      DiscreteTopology (Oˣ ⧸ higherUnitSubgroup π (n + 1)) :=
    fun _ => ⟨rfl⟩
  let e := (dvrUnitsEquivHigherUnitQuotientInverseLimit hπ).trans
    (dvrHigherUnitQuotientInverseLimitRepresentation π)
  let c := (dvrHigherUnitQuotientInverseLimitRepresentation π).toMonoidHom.comp
    (unitsToHigherUnitQuotientInverseLimit π)
  refine
    { toFun := fun u => c u
      invFun := fun q => e.symm q
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro u
    have hc : c u = e u := by
      ext n
      exact (dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
        hπ u n).symm
    change e.symm (c u) = u
    rw [hc]
    exact e.left_inv u
  · intro q
    ext n
    change (QuotientGroup.mk (e.symm q) :
        Oˣ ⧸ higherUnitSubgroup π (n + 1)) = q.1 n
    calc
      (QuotientGroup.mk (e.symm q) :
          Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
          (e (e.symm q)).1 n :=
        (dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
          hπ (e.symm q) n).symm
      _ = q.1 n := by simp [e.apply_symm_apply q]
  · change Continuous fun u : Oˣ => c u
    exact Continuous.subtype_mk
      (continuous_pi fun n => by
        simpa [c, unitsToHigherUnitQuotientInverseLimit] using
          (higherUnitQuotient_mk_continuous_adic_raw π (n + 1)))
      (by
        intro u m n hmn
        exact dvrHigherUnitQuotientTransition_mk π hmn u)
  · apply Units.continuous_iff.mpr
    constructor
    · rw [continuous_iff_continuousAt]
      intro q
      rw [ContinuousAt, Filter.tendsto_def]
      intro s hs
      rcases (Ideal.hasBasis_nhds_adic (uniformizerPowerIdeal π 1)
          ((e.symm q : Oˣ) : O)).mem_iff.mp hs with
        ⟨n, _hn, hns⟩
      let cylinder : Set (compatibleGroupFamilies
          (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
          (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn)) :=
        {q' | q'.1 n = q.1 n}
      have hcont_coord :
          Continuous fun q' : compatibleGroupFamilies
              (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
              (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) =>
            q'.1 n := by
        exact (continuous_apply n).comp continuous_subtype_val
      have hcyl_open : IsOpen cylinder := by
        exact
          (isOpen_discrete
            ({q.1 n} : Set (Oˣ ⧸ higherUnitSubgroup π (n + 1)))).preimage
              hcont_coord
      have hqmem : q ∈ cylinder := rfl
      exact mem_of_superset (hcyl_open.mem_nhds hqmem) (by
        intro q' hq'
        apply hns
        have hmk :
            (QuotientGroup.mk (e.symm q') :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
              QuotientGroup.mk (e.symm q) := by
          calc
            (QuotientGroup.mk (e.symm q') :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
                (e (e.symm q')).1 n :=
              (dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
                hπ (e.symm q') n).symm
            _ = q'.1 n := by simp [e.apply_symm_apply q']
            _ = q.1 n := hq'
            _ = (e (e.symm q)).1 n := by simp [e.apply_symm_apply q]
            _ = QuotientGroup.mk (e.symm q) :=
              dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
                hπ (e.symm q) n
        have hsub_succ :
            ((e.symm q' : Oˣ) : O) - ((e.symm q : Oˣ) : O) ∈
              uniformizerPowerIdeal π (n + 1) :=
          (higherUnitQuotient_mk_eq_mk_iff_sub_mem
            π (n + 1) (e.symm q) (e.symm q')).1 hmk
        have hsub :
            ((e.symm q' : Oˣ) : O) - ((e.symm q : Oˣ) : O) ∈
              (uniformizerPowerIdeal π 1) ^ n := by
          rw [dvrPowerIdeal_one_pow π n]
          exact dvrPowerIdeal_le_of_le π (Nat.le_succ n) hsub_succ
        refine ⟨((e.symm q' : Oˣ) : O) - ((e.symm q : Oˣ) : O), hsub, ?_⟩
        change ((e.symm q : Oˣ) : O) +
            (((e.symm q' : Oˣ) : O) - ((e.symm q : Oˣ) : O)) =
          ((e.symm q' : Oˣ) : O)
        ring)
    · rw [continuous_iff_continuousAt]
      intro q
      rw [ContinuousAt, Filter.tendsto_def]
      intro s hs
      rcases (Ideal.hasBasis_nhds_adic (uniformizerPowerIdeal π 1)
          (((e.symm q)⁻¹ : Oˣ) : O)).mem_iff.mp hs with
        ⟨n, _hn, hns⟩
      let cylinder : Set (compatibleGroupFamilies
          (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
          (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn)) :=
        {q' | q'.1 n = q.1 n}
      have hcont_coord :
          Continuous fun q' : compatibleGroupFamilies
              (fun n : ℕ => Oˣ ⧸ higherUnitSubgroup π (n + 1))
              (fun {_ _} hmn => dvrHigherUnitQuotientTransition π hmn) =>
            q'.1 n := by
        exact (continuous_apply n).comp continuous_subtype_val
      have hcyl_open : IsOpen cylinder := by
        exact
          (isOpen_discrete
            ({q.1 n} : Set (Oˣ ⧸ higherUnitSubgroup π (n + 1)))).preimage
              hcont_coord
      have hqmem : q ∈ cylinder := rfl
      exact mem_of_superset (hcyl_open.mem_nhds hqmem) (by
        intro q' hq'
        apply hns
        have hmk :
            (QuotientGroup.mk (e.symm q') :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
              QuotientGroup.mk (e.symm q) := by
          calc
            (QuotientGroup.mk (e.symm q') :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
                (e (e.symm q')).1 n :=
              (dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
                hπ (e.symm q') n).symm
            _ = q'.1 n := by simp [e.apply_symm_apply q']
            _ = q.1 n := hq'
            _ = (e (e.symm q)).1 n := by simp [e.apply_symm_apply q]
            _ = QuotientGroup.mk (e.symm q) :=
              dvrUnitsEquivHigherUnitQuotientInverseLimit_apply
                hπ (e.symm q) n
        have hinv_mk :
            (QuotientGroup.mk ((e.symm q')⁻¹ : Oˣ) :
                Oˣ ⧸ higherUnitSubgroup π (n + 1)) =
              QuotientGroup.mk ((e.symm q)⁻¹ : Oˣ) := by
          simpa using congrArg Inv.inv hmk
        have hinv_sub_succ :
            (((e.symm q')⁻¹ : Oˣ) : O) - (((e.symm q)⁻¹ : Oˣ) : O) ∈
              uniformizerPowerIdeal π (n + 1) :=
          (higherUnitQuotient_mk_eq_mk_iff_sub_mem
            π (n + 1) ((e.symm q)⁻¹ : Oˣ) ((e.symm q')⁻¹ : Oˣ)).1 hinv_mk
        have hinv_sub :
            (((e.symm q')⁻¹ : Oˣ) : O) - (((e.symm q)⁻¹ : Oˣ) : O) ∈
              (uniformizerPowerIdeal π 1) ^ n := by
          rw [dvrPowerIdeal_one_pow π n]
          exact dvrPowerIdeal_le_of_le π (Nat.le_succ n)
            hinv_sub_succ
        refine
          ⟨(((e.symm q')⁻¹ : Oˣ) : O) - (((e.symm q)⁻¹ : Oˣ) : O),
            hinv_sub, ?_⟩
        change (((e.symm q)⁻¹ : Oˣ) : O) +
            ((((e.symm q')⁻¹ : Oˣ) : O) - (((e.symm q)⁻¹ : Oˣ) : O)) =
          (((e.symm q')⁻¹ : Oˣ) : O)
        ring)

/-- The unit-group inverse-limit homeomorphism with the adic source and
prodiscrete target fixed at the type level. -/
noncomputable def unitsEquivHigherUnitQuotientInverseLimitHomeomorph
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π)
    [IsAdicComplete (uniformizerPowerIdeal π 1) O] :
    WithTopology Oˣ
        (adicUnitsTopology (uniformizerPowerIdeal π 1)) ≃ₜ
      dvrHigherUnitQuotientInverseLimit π := by
  letI : TopologicalSpace O := (uniformizerPowerIdeal π 1).adicTopology
  letI : (n : ℕ) → TopologicalSpace
      (Oˣ ⧸ higherUnitSubgroup π (n + 1)) := fun _ => ⊥
  let source := WithTopology.homeomorph
    (α := Oˣ)
    (topology := adicUnitsTopology (uniformizerPowerIdeal π 1))
  let algebraic := unitsCompatibleFamiliesHomeomorph hπ
  let target := dvrHigherUnitQuotientInverseLimitRepresentationHomeomorph π
  exact source.trans (algebraic.trans target.symm)

/-! ### Direct complete-valued-field form of the adic inverse-limit equivalence -/

end Valuations
end LubinTate
end
end


