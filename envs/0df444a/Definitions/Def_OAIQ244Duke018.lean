-- Prove2me | Definitions.Def_OAIQ244Duke018
-- name    : OAIQ244Duke018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:18:11.940355+00:00
-- url     : https://prove2.me/theorems/11eb963b-b018-4959-b6dd-a9b94456c4cb
-- title:
--   Definitions bundle OAIQ244Duke018 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 198 declarations of OpenAI's Lean: 44 definitions, 1 inductive type or structure, 5 instances and 148 theorems. The definitions and types are `IsGaloisStableFinitePlaces`, `KummerTheory.PrimeCyclotomicPushout`, `LocalClassFieldTheory.additiveFixedUnitToInvariantsNormQuotientHom`, `LocalClassFieldTheory.additiveFixedUnitsEquivInvariants`, `LocalClassFieldTheory.fixedUnitToInvariantsNormQuotientMonoidHom`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued_rankOne`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_rankOne`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits`, `LocalFieldTheory.DiscreteValuationField.LocalField`, `LocalFieldTheory.DiscreteValuationField.LocalField.mrangeValueGroup`, `LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.LocalField.qpadicClosureSubfield`, `LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield`, `LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield`, `LocalFieldTheory.DiscreteValuationField.LocalField.ratSubfield`, `LocalFieldTheory.DiscreteValuationField.LocalField.residueCharacteristic`, `LocalFieldTheory.DiscreteValuationField.LocalField.residueField`, `LocalFieldTheory.DiscreteValuationField.LocalField.residueMap`, `LocalFieldTheory.DiscreteValuationField.LocalField.valuationSubring`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgumentLeftPositions`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgumentMixedPositions`, `LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.formalLogOnePlusProductArgumentRightPositions`, `LocalFieldTheory.DiscreteValuationField.WithZeroValuationTopology.completeDVF`, `LocalFieldTheory.Padic.integerRingEquivPadicInt`, `RelativeIdeleGroup.adeleEmbedding`, `RelativeIdeleGroup.ideleEmbedding`, `ValuationTheory.DiscreteValuationField.CompleteDVF.residueField`, `ValuationTheory.DiscreteValuationField.CompleteDVF.residueMap`, `ValuationTheory.DiscreteValuationField.HenselianDVF.residueField`, `ValuationTheory.DiscreteValuationField.HenselianDVF.residueMap`, `ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex`, `ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree` and 5 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Adele_IntegralTensorSupport_AbsoluteValue`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_FinitePlaceCompletion`, `AlgebraicNumberTheory_Adele_RestrictedAction`, `AlgebraicNumberTheory_Completion_Comparison`, `AlgebraicNumberTheory_Idele_BaseChange`, `AlgebraicNumberTheory_Idele_Extension_EmbeddingNorm`, `AlgebraicNumberTheory_Idele_Extension_GaloisNorm`, `AlgebraicNumberTheory_Idele_Extension_NormLocalOrder`, `AlgebraicNumberTheory_Idele_PrincipalCore`, `AlgebraicNumberTheory_SUnit_GaloisAction`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_FinitePlaceCompletionInstances`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_LocalResidueArithmetic`, `KummerTheory_Concrete_CyclotomicPrimeBaseChange`, `LocalClassFieldTheory_ClassFormation_CohomologyBridge`, `LocalField_Analytic_DenominatorValuation`, `LocalField_Analytic_LogExpAdditivity`, `LocalField_Analytic_LogExpSeries_FormalCore`, `LocalField_Analytic_LogExpSeries_FormalCoreBase_BasicFactors`, `LocalField_Analytic_LogExpSeries_FormalCoreBase_ChoiceCountSystem`, `LocalField_Analytic_LogExpSeries_FormalCoreBase_ChoicePositions`, `LocalField_Analytic_LogExpSeries_FormalCoreBase_ExplicitChoiceCounts`, `LocalField_Analytic_LogExpSeries_FormalCoreBase_ProductArgument`, `LocalField_Analytic_LogExpSeries_FormalProduct`, `LocalField_Analytic_LogExpSeries_SeriesTerms`, `LocalField_DiscreteValuationField_Basic`, `LocalField_DiscreteValuationField_MixedCharacteristicQp`, `LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice`, `LocalField_DiscreteValuationField_Units`, `LocalField_DiscreteValuationField_ValuationSubringUnits_CompleteRangeRestriction`, `LocalField_DiscreteValuationField_ValuationSubringUnits_IntegerValuation`, `LocalField_DiscreteValuationField_ValuationSubringUnits_RangeRestrictedTopology`, `LocalField_DiscreteValuationField_ValuationSubringUnits_SeriesValuationEstimates`, `LocalField_DiscreteValuationField_ValuationSubringUnits_UniformizerIntegerValuation`, `LocalField_DiscreteValuationField_ValuationSubringUnits_ValuationSubringUnitMap`, `LocalField_DiscreteValuationField_WithZeroValuationTopology`, `LocalField_GroupTheory_PowerIndex`, `LocalField_Padic_NonarchimedeanLocalField`, `LocalField_Padic_PrincipalUnits`, `Valuation_DiscreteValuationField_Basic`, `Valuation_DiscreteValuationField_Complete`, `Valuation_DiscreteValuationField_Extensions`, `Valuation_DiscreteValuationField_FiniteExtension_Degree`, `Valuation_DiscreteValuationField_Henselian`, `Valuation_HenselLemma`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke000`, `OAIQ244Duke001`, `OAIQ244Duke002`, `OAIQ244Duke004`, `OAIQ244Duke005`, `OAIQ244Duke006`, `OAIQ244Duke007` and `OAIQ244Duke008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke028`, `OAIQ244Duke029`, `OAIQ244Duke030`, `OAIQ244Duke031`, `OAIQ244Duke033` and `OAIQ244Duke034`; the proofs of `OAI.DukePrimeDegree.exists_bounded_branching_subordinate_observation_with_lifts`, `OAI.DukePrimeDegree.exists_bounded_cover_subordinate_observation` and `OAI.DukePrimeDegree.exists_small_future_observation`.
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
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
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
import Definitions.Def_OAIQ244Duke000
import Definitions.Def_OAIQ244Duke001
import Definitions.Def_OAIQ244Duke002
import Definitions.Def_OAIQ244Duke004
import Definitions.Def_OAIQ244Duke005
import Definitions.Def_OAIQ244Duke006
import Definitions.Def_OAIQ244Duke007
import Definitions.Def_OAIQ244Duke008

section
-- module Solutions.OAIQ244_DUKE.Compat
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_PrincipalCore
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Principal ideles and the idele class group

This file formalizes the diagonal
embedding of `Kˣ` into the idele group and the resulting idele class group.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

namespace IdeleGroup

variable {K}

variable (K)

/-- The diagonal map from field units to ideles is injective. -/
theorem principalIdele_injective :
    Function.Injective (principalIdele K) := by
  apply (equivAdeleRingUnits (K := K)).symm.injective.comp
  exact Units.map_injective
    (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K))

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_GaloisNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The Galois product formula for the relative idele norm

This file proves that, in the tensor-product presentation
`𝔸_L = 𝔸_K ⊗_K L`, extension of the determinant norm back to `𝔸_L`
is the product of all Galois conjugates.
-/

open scoped BigOperators TensorProduct
open NumberField

noncomputable section


namespace RelativeIdeleGroup

universe u v w

variable
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- The universal determinant norm polynomial becomes the product of the
universal Galois conjugates after extending its coefficients to `L`. -/
theorem map_normPolynomial_eq_galoisProductPolynomial
    [IsGalois K L] [Infinite K]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) :
    MvPolynomial.map (algebraMap K L) (normPolynomial b) =
      galoisProductPolynomial b := by
  apply MvPolynomial.funext_set
    (fun _ : ι ↦ Set.range (algebraMap K L))
  · intro i
    exact Set.infinite_range_of_injective
      (algebraMap K L).injective
  · intro c hc
    choose d hd using fun i ↦ hc i (Set.mem_univ i)
    let x : L :=
      b.repr.symm (Finsupp.equivFunOnFinite.symm d)
    have hcoords :
        c = fun i ↦ algebraMap K L (b.repr x i) := by
      funext i
      calc
        c i = algebraMap K L (d i) := (hd i).symm
        _ = algebraMap K L (b.repr x i) := by simp [x]
    rw [hcoords, eval_galoisProductPolynomial]
    rw [MvPolynomial.eval_map]
    change MvPolynomial.eval₂ (algebraMap K L)
        ((algebraMap K L) ∘ fun i ↦ b.repr x i)
        (normPolynomial b) =
      _
    rw [← MvPolynomial.eval₂_comp]
    rw [eval_normPolynomial]
    exact Algebra.norm_eq_prod_automorphisms K x

omit [FiniteDimensional K L] in
/-- Evaluating a universal conjugate polynomial at the coordinates of a
base-changed element gives its actual scalar-extended conjugate. -/
theorem eval₂_conjugatePolynomial_baseChange
    (A : Type*) [CommRing A] [Algebra K A]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (σ : L ≃ₐ[K] L)
    (z : A ⊗[K] L) :
    MvPolynomial.eval₂
        ((Algebra.TensorProduct.includeRight
          (R := K) (A := A) (B := L)).toRingHom)
        (fun i ↦ (Algebra.TensorProduct.includeLeft
          (R := K) (S := K) (A := A) (B := L))
          ((Algebra.TensorProduct.basis A b).repr z i))
        (conjugatePolynomial b σ) =
      scalarConjugation (K := K) (L := L) A σ z := by
  simp only [conjugatePolynomial, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_C]
  calc
    ∑ i, (Algebra.TensorProduct.includeLeft
          (R := K) (S := K) (A := A) (B := L))
          ((Algebra.TensorProduct.basis A b).repr z i) *
        (Algebra.TensorProduct.includeRight
          (R := K) (A := A) (B := L)) (σ (b i)) =
        ∑ i, scalarConjugation (K := K) (L := L) A σ
          (((Algebra.TensorProduct.basis A b).repr z i) •
            Algebra.TensorProduct.basis A b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [scalarConjugation, Algebra.TensorProduct.basis_apply,
        Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.smul_def]
    _ = scalarConjugation (K := K) (L := L) A σ
          (∑ i, ((Algebra.TensorProduct.basis A b).repr z i) •
            Algebra.TensorProduct.basis A b i) := by
      rw [map_sum]
    _ = scalarConjugation (K := K) (L := L) A σ z := by
      rw [(Algebra.TensorProduct.basis A b).sum_repr]

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_Units
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Principal-unit filtrations

This file provides a theorem API for antitone principal-unit filtrations used by
ramification and norm arguments.
-/

universe u v

open scoped BigOperators

namespace DiscreteValuationField

namespace AntitoneSubgroupFiltration

variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)

/-- A subquotient of a commutative principal-unit filtration retains the
commutative group structure of its concrete quotient representation. -/
instance principalUnitSubquotientCommGroup
    {H : Type u} [CommGroup H] (V : AntitoneSubgroupFiltration H)
    (m n : ℕ) [(V.principalUnitSubgroup n).Normal] :
    CommGroup (V.principalUnitSubquotient m n) :=
  { (inferInstance : Group (V.principalUnitSubquotient m n)) with
    mul_comm := fun x y => by
      apply (V.principalUnitSubquotientConcreteEquiv m n).injective
      simp only [map_mul]
      exact mul_comm _ _ }

/-- The kernel of `G ⧸ U^n →* G ⧸ U^m` is the image of `U^m` in
`G ⧸ U^n`. -/
theorem quotient_principalUnitSubgroup_mapOfLe_ker_eq_classInQuotient
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (U.quotient_principalUnitSubgroup_mapOfLe hmn).ker =
      U.principalUnitSubgroupClassInQuotient m n := by
  exact (QuotientGroup.ker_map (U.principalUnitSubgroup n)
    (U.principalUnitSubgroup m) (MonoidHom.id G) (by
      intro x hx
      exact U.mem_of_mem_of_le hmn hx)).trans
    (congrArg (Subgroup.map (QuotientGroup.mk' (U.principalUnitSubgroup n)))
      (Subgroup.comap_id (U.principalUnitSubgroup m)))

/-- The restricted map `U^l/U^n → U^l/U^m` has kernel `U^m/U^n`. -/
theorem principalUnitClassMapOfLe_ker_eq {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (U.principalUnitClassMapOfLe hlm hmn).ker =
      (U.principalUnitSubgroupClassInQuotient m n).subgroupOf
        (U.principalUnitSubgroupClassInQuotient l n) := by
  ext q
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hq
    have hq' := congrArg Subtype.val hq
    change
      U.quotient_principalUnitSubgroup_mapOfLe hmn
          (q : G ⧸ U.principalUnitSubgroup n) = 1 at hq'
    rw [← U.quotient_principalUnitSubgroup_mapOfLe_ker_eq_classInQuotient hmn,
      MonoidHom.mem_ker]
    exact hq'
  · intro hq
    apply Subtype.ext
    change
      U.quotient_principalUnitSubgroup_mapOfLe hmn
          (q : G ⧸ U.principalUnitSubgroup n) = 1
    rw [← MonoidHom.mem_ker,
      U.quotient_principalUnitSubgroup_mapOfLe_ker_eq_classInQuotient hmn]
    exact hq

end AntitoneSubgroupFiltration

end DiscreteValuationField

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- Membership in the valuation subring is `v x <= 1`. -/
theorem mem_valuationSubring_iff (F : DVF.{u, v} K) (x : K) :
    x ∈ F.valuation.valuationSubring ↔ F.valuation x <= 1 :=
  Valuation.mem_valuationSubring_iff (v := F.valuation) x

/-- Maximal-ideal membership is `v x < 1`. -/
theorem mem_maximalIdeal_iff (F : DVF.{u, v} K)
    (x : F.valuationSubring) :
    x ∈ F.maximalIdeal ↔ F.valuation (x : K) < 1 := by
  change
    x ∈ IsLocalRing.maximalIdeal F.valuation.valuationSubring ↔
    (F.valuation (x : K) < 1)
  exact Valuation.mem_maximalIdeal_iff (v := F.valuation)

/-- A residue class in a DVF valuation ring is nonzero exactly when its
representative is a unit of the valuation ring. -/
theorem residue_ne_zero_iff_isUnit (F : DVF.{u, v} K)
    (x : F.valuationSubring) :
    F.residueMap x ≠ 0 ↔ IsUnit x := by
  change IsLocalRing.residue F.valuation.valuationSubring x ≠ 0 ↔ IsUnit x
  exact IsLocalRing.residue_ne_zero_iff_isUnit x

/-- The residue map is surjective. -/
theorem residue_surjective (F : DVF.{u, v} K) :
    Function.Surjective F.residueMap :=
  IsLocalRing.residue_surjective (R := F.valuation.valuationSubring)

/-! ### Successive quotients of powers of the maximal ideal -/

/-- Binary elimination through arbitrary ideal-power representatives. -/
protected theorem MaximalIdealPowSuccQuot.inductionOn₂
    (F : DVF.{u, v} K) (n : ℕ)
    {motive : F.MaximalIdealPowSuccQuot n →
      F.MaximalIdealPowSuccQuot n → Prop}
    (q r : F.MaximalIdealPowSuccQuot n)
    (h : ∀ a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u),
      motive (F.maximalIdealPowSuccQuotMk n a)
        (F.maximalIdealPowSuccQuotMk n b)) :
    motive q r := by
  refine MaximalIdealPowSuccQuot.inductionOn F n
    (motive := fun q' ↦ motive q' r) q ?_
  intro a
  refine MaximalIdealPowSuccQuot.inductionOn F n
    (motive := fun r' ↦ motive (F.maximalIdealPowSuccQuotMk n a) r') r ?_
  intro b
  exact h a b

end DVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Henselian
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

namespace HenselianDVF

variable {K : Type u} [Field K]

/-- Introduces the abbreviation `residueField`. -/
abbrev residueField (F : HenselianDVF.{u, v} K) : Type u :=
  F.toDVF.residueField

/-- Introduces the abbreviation `residueMap`. -/
abbrev residueMap (F : HenselianDVF.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  F.toDVF.residueMap

end HenselianDVF

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Complete
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

end Valuation

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- Introduces the abbreviation `residueField`. -/
abbrev residueField (F : CompleteDVF.{u, v} K) : Type u :=
  F.toHenselianDVF.residueField

/-- Introduces the abbreviation `residueMap`. -/
abbrev residueMap (F : CompleteDVF.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  F.toHenselianDVF.residueMap

/-- Membership in the valuation subring is characterized by nonnegative valuation. -/
theorem mem_valuationSubring_iff (F : CompleteDVF.{u, v} K) (x : K) :
    x ∈ F.valuation.valuationSubring ↔ F.valuation x <= 1 :=
  F.toDVF.mem_valuationSubring_iff x

/-- An integral element has nonzero residue exactly when it is a unit. -/
theorem residue_ne_zero_iff_isUnit (F : CompleteDVF.{u, v} K)
    (x : F.valuationSubring) :
    F.residueMap x ≠ 0 ↔ IsUnit x :=
  IsLocalRing.residue_ne_zero_iff_isUnit x

/-- Every residue-field element has a representative in the valuation ring. -/
theorem residue_surjective (F : CompleteDVF.{u, v} K) :
    Function.Surjective F.residueMap :=
  IsLocalRing.residue_surjective

end CompleteDVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Extensions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Finite extensions of discretely valued fields

The extension relation is ambient data: an algebra, finite-dimensionality, and
mathlib's `Valuation.HasExtension` property.  There is deliberately no
proof-irrelevant marker object.  All invariants and maps are defined once for
`DVF` values and can therefore be used unchanged for Henselian and complete
discretely valued fields through their canonical `toDVF` projections.
-/

noncomputable section

universe u v w x

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : DVF.{u, v} K) (target : DVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The canonical ramification index of the target maximal ideal over the
base maximal ideal. -/
noncomputable def ramificationIndex : ℕ :=
  Ideal.ramificationIdx'
    (base.maximalIdeal : Ideal base.valuationSubring)
    (target.maximalIdeal : Ideal target.valuationSubring)

/-- The canonical residue degree of the target maximal ideal over the base
maximal ideal. -/
noncomputable def residueDegree : ℕ :=
  (target.maximalIdeal : Ideal target.valuationSubring).inertiaDeg
    base.valuationSubring

end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteExtension_Degree
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Finite valued extension consequences

This file collects theorem-level consequences around finite valued extensions:
canonical local-Dedekind degree formulas, uniqueness criteria for extended
valuations, and the algebra equivalence identifying an actual integral-closure
valuation ring with mathlib's `integralClosure`.
-/

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

open ValuationTheory.DiscreteValuationField.Valuation

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

omit [FiniteDimensional K L] in
/-- The canonical integer map into the valuation subring built from the actual
integral closure is injective.  This is the ring-theoretic input needed to
turn a prime over the base maximal ideal into a nonzero prime of the constructed
integral-closure valuation ring. -/
theorem integralClosureValuationSubringIntegerMapOfMemOrInv_injective
    (base : CompleteDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    Function.Injective
      (integralClosureValuationSubringIntegerMapOfMemOrInv
        (K := K) (L := L) base hval) := by
  intro a b hab
  apply Subtype.ext
  apply FaithfulSMul.algebraMap_injective K L
  have hvalEq := congrArg
    (fun x :
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval => (x : L)) hab
  change algebraMap K L (a : K) = algebraMap K L (b : K) at hvalEq
  exact hvalEq

/- Numerical defect is a derived quotient; defectlessness itself is the
canonical equality `degree = e * f` defined in `Extensions`.  Positivity
and the fundamental identity are established below only under the hypotheses
needed by the local-Dedekind theorem. -/
end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_HenselLemma
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
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

namespace HenselianDVF

open ValuationTheory.DiscreteValuationField.ResidueField

variable {K : Type u} [Field K]

variable (F : HenselianDVF.{u, v} K)

/-- A simple root in a fixed residue class is unique.

This is the uniqueness half used by residue-lift constructions: if two actual
roots have the same residue and one of them has unit derivative, then they are
equal. -/
theorem eq_of_isRoot_of_isRoot_of_residue_eq_of_derivative_isUnit
    {f : Polynomial F.valuationSubring} {a b : F.valuationSubring}
    (ha : f.IsRoot a) (hb : f.IsRoot b)
    (hres : F.residueMap b = F.residueMap a)
    (hderiv : IsUnit (f.derivative.eval a)) :
    b = a := by
  let q : Polynomial F.valuationSubring :=
    f /ₘ (Polynomial.X - Polynomial.C a)
  have hfactor :
      (Polynomial.X - Polynomial.C a) * q = f := by
    dsimp [q]
    rw [Polynomial.mul_divByMonic_eq_iff_isRoot]
    exact ha
  have hq_eval :
      q.eval a = f.derivative.eval a := by
    simpa [q] using
      divByMonic_X_sub_C_eval_eq_derivative_eval (p := f) a
  have hq_unit_a : IsUnit (q.eval a) := by
    simpa [hq_eval] using hderiv
  have hq_residue :
      F.residueMap (q.eval b) = F.residueMap (q.eval a) := by
    calc
      F.residueMap (q.eval b) =
          (q.map F.residueMap).eval (F.residueMap b) := by
        exact (Polynomial.eval_map_apply (f := F.residueMap) (p := q) b).symm
      _ = (q.map F.residueMap).eval (F.residueMap a) := by
        rw [hres]
      _ = F.residueMap (q.eval a) := by
        exact Polynomial.eval_map_apply (f := F.residueMap) (p := q) a
  have hq_residue_ne : F.residueMap (q.eval b) ≠ 0 := by
    rw [hq_residue]
    exact (F.toDVF.residue_ne_zero_iff_isUnit (q.eval a)).2 hq_unit_a
  have hq_ne : q.eval b ≠ 0 := by
    intro hzero
    exact hq_residue_ne (by rw [hzero, map_zero])
  have hmul : (b - a) * q.eval b = 0 := by
    have hb_eval :
        ((Polynomial.X - Polynomial.C a) * q).eval b = 0 := by
      rw [hfactor]
      exact Polynomial.IsRoot.def.mp hb
    simpa [Polynomial.eval_mul, Polynomial.eval_sub] using hb_eval
  have hsub : b - a = 0 :=
    (mul_eq_zero.mp hmul).resolve_right hq_ne
  exact sub_eq_zero.mp hsub

end HenselianDVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_CohomologyBridge
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.inducedFixedEquiv_apply_coe _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open CyclicCohomology

/-!
# The actual low-degree Tate quotients as Herbrand quotients

This file compares the concrete multiplicative Herbrand quotients from
low-degree cyclic cohomology with the Tate objects built from mathlib's actual
Galois representation on `Lˣ`.  The comparison uses the standard Galois action
on units; it does not introduce a replacement coefficient object.
-/

noncomputable section

open scoped BigOperators

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CategoryTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- Multiplicative fixed units and the invariant submodule of the actual unit
representation are the same additive group. -/
def additiveFixedUnitsEquivInvariants :
    Additive (fixedSubgroup (Gal(L / K)) Lˣ) ≃+
      unitsInvariantSubmodule K L where
  toFun x := ⟨Additive.ofMul ((Additive.toMul x : fixedSubgroup (Gal(L / K)) Lˣ) : Lˣ), by
    intro σ
    exact congrArg Additive.ofMul ((Additive.toMul x).property σ)⟩
  invFun x := Additive.ofMul ⟨Additive.toMul (x : Additive Lˣ), by
    intro σ
    exact Additive.ofMul.injective (x.property σ)⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl

/-- Additive quotient map from fixed units to invariant units modulo norms. -/
def additiveFixedUnitToInvariantsNormQuotientHom
    [Fintype (Gal(L / K))] :
    Additive (fixedSubgroup (Gal(L / K)) Lˣ) →+
      (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) :=
  additiveEquivToQuotientHom (additiveFixedUnitsEquivInvariants K L)
    (unitsTateH0NormSubmodule K L)

/-- Send a fixed unit to its invariant-unit class modulo norms. -/
def fixedUnitToInvariantsNormQuotientMonoidHom
    [Fintype (Gal(L / K))] :
    fixedSubgroup (Gal(L / K)) Lˣ →*
      Multiplicative
        (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) :=
  additiveHomToMultiplicativeHom
    (additiveFixedUnitToInvariantsNormQuotientHom K L)

/-- A fixed unit maps to its canonical invariant-unit class modulo norms. -/
@[simp]
theorem fixedUnitToInvariantsNormQuotientMonoidHom_apply
    [Fintype (Gal(L / K))] (x : fixedSubgroup (Gal(L / K)) Lˣ) :
    Multiplicative.toAdd
        (fixedUnitToInvariantsNormQuotientMonoidHom K L x) =
      (unitsTateH0NormSubmodule K L).mkQ
        (additiveFixedUnitsEquivInvariants K L (Additive.ofMul x)) :=
  rfl

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_AbsoluteValue
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral lattices for the relative tensor basis

This file continues the finite-support construction for relative tensor
decompositions.  A single nonzero integer is chosen which carries every
vector of the fixed `K`-basis of `L` into `𝓞 L`.  Their
`𝓞 K`-span is a full lattice in `𝓞 L`.

The quotient of `𝓞 L` by this lattice is then proved directly to be a
finite torsion `𝓞 K`-module.  A nonzero element of its annihilator
therefore gives an actual finite set of bad height-one primes.  Outside
that set the scaled lattice generates the localization of `𝓞 L` over
the local ring of `K`.

Finally, a universe-polymorphic comparison between the absolute-value
and adic models of `K_v` carries this result through the canonical local tensor decomposition.
Away from the same bad set, the chosen basis-integral lattice maps into
the product of the completion valuation rings; applying the statement
to a unit and its inverse gives the actual product of local integer
unit groups needed in the finite-support decomposition.
-/

open scoped NumberField TensorProduct NNReal
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- An element integral over `ℤ` lies in the valuation subring of
every nonarchimedean real absolute value. -/
theorem absoluteValue_le_one_of_isIntegral
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    {x : F} (hx : IsIntegral ℤ x) :
    vF x ≤ 1 := by
  let ν : Valuation F NNReal :=
    realAbsoluteValueValuation vF hvF
  let V : ValuationSubring F := ν.valuationSubring
  let : IsIntegrallyClosedIn V F :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn F).1
      inferInstance
  let : IsScalarTower ℤ V F :=
    IsScalarTower.of_algebraMap_eq fun n => by
      simp
  have hxV : IsIntegral V x :=
    hx.tower_top
  obtain ⟨y, hy⟩ :=
    (IsIntegrallyClosedIn.isIntegral_iff).1 hxV
  have hν : x ∈ V := by
    rw [← hy, ValuationSubring.algebraMap_apply]
    exact y.property
  change
    realAbsoluteValueValuation vF hvF x ≤ 1 at hν
  exact_mod_cast hν
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_FinitePlaceCompletion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
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

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The inverse of the universe-polymorphic completion comparison is
also an isometry. -/
theorem relativeFinitePlaceCompletionAlgEquiv_symm_norm
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K) :
    ‖(relativeFinitePlaceCompletionAlgEquiv w).symm x‖ =
      ‖x‖ := by
  let y :=
    (relativeFinitePlaceCompletionAlgEquiv w).symm x
  have h :=
    (relativeFinitePlaceCompletionRingHom_isometry w).norm_map_of_map_zero
      (map_zero
        (relativeFinitePlaceCompletionRingHom w)) y
  have hy :
      relativeFinitePlaceCompletionRingHom w y = x := by
    change
      relativeFinitePlaceCompletionAlgEquiv w y = x
    exact
      (relativeFinitePlaceCompletionAlgEquiv w).apply_symm_apply x
  rw [hy] at h
  exact h.symm

/-- Cramer's rule over an integrally closed base: coordinates are
integral once the trace matrix, the trace vector, and the inverse
discriminant are integral. -/
theorem basis_coord_isIntegral_of_integral_traces
    {R A B ι : Type*}
    [CommRing R] [Field A] [CommRing B]
    [Algebra R A] [Algebra A B]
    [Fintype ι] [DecidableEq ι]
    [Module.Free A B] [Module.Finite A B]
    (b : Module.Basis ι A B)
    {x : B}
    (hM : ∀ j k, IsIntegral R
      (Algebra.trace A B (b j * b k)))
    (ht : ∀ j, IsIntegral R
      (Algebra.trace A B (x * b j)))
    (hdiscInv : IsIntegral R (Algebra.discr A b)⁻¹)
    (hdiscne : Algebra.discr A b ≠ 0)
    (i : ι) :
    IsIntegral R (b.equivFun x i) := by
  let M : Matrix ι ι A := Algebra.traceMatrix A b
  let c : ι → A := b.equivFun x
  let t : ι → A := fun j => Algebra.trace A B (x * b j)
  have hM' : ∀ j k, IsIntegral R (M j k) := by
    intro j k
    exact hM j k
  have ht' : ∀ j, IsIntegral R (t j) := by
    intro j
    exact ht j
  have hcramer : IsIntegral R (M.cramer t i) := by
    rw [Matrix.cramer_apply]
    apply IsIntegral.det
    intro j k
    by_cases hki : k = i
    · simpa [Matrix.updateCol_apply, hki] using ht' j
    · simpa [Matrix.updateCol_apply, hki] using hM' j k
  have hmul : M.mulVec c = t :=
    Algebra.traceMatrix_of_basis_mulVec b x
  have hcramerEq : M.det • c = M.cramer t := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hmul,
      Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcoord :
      Algebra.discr A b * c i = M.cramer t i := by
    have hi := congrFun hcramerEq i
    simpa [M, Algebra.discr_def, Pi.smul_apply] using hi
  have hcEq :
      c i = (Algebra.discr A b)⁻¹ * M.cramer t i := by
    rw [← hcoord, ← mul_assoc, inv_mul_cancel₀ hdiscne, one_mul]
  change IsIntegral R (c i)
  rw [hcEq]
  exact hdiscInv.mul hcramer
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_RestrictedAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
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

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
theorem scalarTensorConjugation_one
    (z : A ⊗[K] L) :
    scalarTensorConjugation
        (K := K) (L := L) (A := A)
        (1 : L ≃ₐ[K] L) z = z := by
  induction z using OAI.tensorInductionOn with
  | tmul a x => simp
  | add x y hx hy => simp [hx, hy]

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
theorem scalarTensorConjugation_mul
    (σ τ : L ≃ₐ[K] L)
    (z : A ⊗[K] L) :
    scalarTensorConjugation
        (K := K) (L := L) (A := A) (σ * τ) z =
      scalarTensorConjugation
        (K := K) (L := L) (A := A) σ
        (scalarTensorConjugation
          (K := K) (L := L) (A := A) τ z) := by
  induction z using OAI.tensorInductionOn with
  | tmul a x => simp
  | add x y hx hy => simp [hx, hy]

/-- The action by tensor conjugation on local tensor units. -/
@[reducible]
noncomputable def scalarTensorUnitsAction :
    MulDistribMulAction
      (L ≃ₐ[K] L) (A ⊗[K] L)ˣ where
  smul σ z :=
    Units.mapEquiv
      (scalarTensorConjugation
        (K := K) (L := L) (A := A) σ).toMulEquiv z
  one_smul z := by
    apply Units.ext
    exact scalarTensorConjugation_one
      (K := K) (L := L) (A := A)
      (z : A ⊗[K] L)
  mul_smul σ τ z := by
    apply Units.ext
    exact scalarTensorConjugation_mul
      (K := K) (L := L) (A := A)
      σ τ (z : A ⊗[K] L)
  smul_one σ := by
    apply Units.ext
    exact
      (scalarTensorConjugation
        (K := K) (L := L) (A := A) σ).map_one
  smul_mul σ x y := by
    apply Units.ext
    exact
      (scalarTensorConjugation
        (K := K) (L := L) (A := A) σ).map_mul
        (x : A ⊗[K] L) (y : A ⊗[K] L)

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
@[simp]
theorem scalarTensorUnitsAction_coe
    (σ : L ≃ₐ[K] L)
    (z : (A ⊗[K] L)ˣ) :
    letI := scalarTensorUnitsAction
      (K := K) (L := L) (A := A)
    ((σ • z : (A ⊗[K] L)ˣ) :
        A ⊗[K] L) =
      scalarTensorConjugation
        (K := K) (L := L) (A := A) σ
        (z : A ⊗[K] L) :=
  rfl

end ScalarTensor
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_SUnit_GaloisAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.mem_sUnitFiniteKummerRadical_iff _root_.LocalFieldTheory.residueField_algebraMap_residue
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
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

noncomputable section

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in
/-- The integral adic valuation is invariant under simultaneous transport
of the finite place and the integer. -/
theorem intValuation_finitePlaceEquiv
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L))
    (r : 𝓞 L) :
    (finitePlaceEquiv K L σ v).intValuation
        (NumberField.RingOfIntegers.mapAlgEquiv σ r) =
      v.intValuation r := by
  let e := (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv
  by_cases hr : r = 0
  · subst r
    simp
  change
    (finitePlaceEquiv K L σ v).intValuation (e r) =
      v.intValuation r
  have her : e r ≠ 0 := by
    simpa using e.injective.ne hr
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity
      (finitePlaceEquiv K L σ v) her,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v hr]
  congr 2
  have hspan :
      Ideal.span ({e r} : Set (𝓞 L)) =
        idealMapMulEquiv e (Ideal.span ({r} : Set (𝓞 L))) := by
    simp [idealMapMulEquiv, Ideal.map_span]
  rw [finitePlaceEquiv_asIdeal, hspan]
  norm_cast
  exact multiplicity_map_eq (idealMapMulEquiv e)
    (a := v.asIdeal) (b := Ideal.span ({r} : Set (𝓞 L)))

omit [NumberField K] in
/-- The field-valued adic valuation is invariant under simultaneous
transport of the finite place and the field element. -/
theorem valuation_finitePlaceEquiv
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L))
    (x : L) :
    (finitePlaceEquiv K L σ v).valuation L (σ x) =
      v.valuation L x := by
  obtain ⟨r, d, hrd⟩ :=
    IsLocalization.exists_mk'_eq (𝓞 L)⁰ x
  rw [← hrd, IsFractionRing.mk'_eq_div, map_div₀,
    map_div₀, map_div₀]
  have hσr :
      σ ((algebraMap (𝓞 L) L) r) =
        (algebraMap (𝓞 L) L)
          (NumberField.RingOfIntegers.mapAlgEquiv σ r) :=
    rfl
  have hσd :
      σ ((algebraMap (𝓞 L) L) (d : 𝓞 L)) =
        (algebraMap (𝓞 L) L)
          (NumberField.RingOfIntegers.mapAlgEquiv σ (d : 𝓞 L)) :=
    rfl
  rw [hσr, hσd]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  rw [intValuation_finitePlaceEquiv, intValuation_finitePlaceEquiv]

section FinitePlaceAction

attribute [local instance] instMulActionAlgEquivHeightOneSpectrumRingOfIntegers_solutions
attribute [local instance] instMulDistribMulActionAlgEquivUnits_solutions
/-- A finite set of finite places is Galois-stable when it is invariant
under the concrete place permutation. -/
def IsGaloisStableFinitePlaces
    (S : Finset (HeightOneSpectrum (𝓞 L))) : Prop :=
  ∀ (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 L)),
      v ∈ S ↔ σ • v ∈ S

omit [NumberField K] [NumberField L] in
theorem IsGaloisStableFinitePlaces.smul_mem
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L) {v : HeightOneSpectrum (𝓞 L)}
    (hv : v ∈ S) :
    σ • v ∈ S :=
  (hS σ v).mp hv

omit [NumberField K] in
/-- Galois automorphisms preserve the concrete `S`-unit subgroup when
the finite-place set is stable. -/
theorem sUnit_smul_mem
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L) (x : Lˣ)
    (hx : x ∈ SUnitGroup (K := L) S) :
    σ • x ∈ SUnitGroup (K := L) S := by
  intro v hv
  let w : HeightOneSpectrum (𝓞 L) := σ⁻¹ • v
  have hw : w ∉ S := by
    intro hwmem
    exact hv ((hS σ⁻¹ v).mpr hwmem)
  have hxw : w.valuation L (x : L) = 1 :=
    hx w hw
  have htransport :=
    valuation_finitePlaceEquiv K L σ w (x : L)
  have hvw : finitePlaceEquiv K L σ w = v := by
    change
      finitePlaceEquiv K L σ
          (finitePlaceEquiv K L σ⁻¹ v) = v
    rw [← finitePlaceEquiv_mul]
    simp
  rw [hvw] at htransport
  change v.valuation L (σ (x : L)) = 1
  exact htransport.trans hxw

/-- The actual Galois action on the `S`-unit group. -/
@[reducible]
noncomputable def sUnitMulDistribMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    MulDistribMulAction (L ≃ₐ[K] L)
      (SUnitGroup (K := L) S) :=
  stableSubgroupMulDistribMulAction
    (SUnitGroup (K := L) S)
    (sUnit_smul_mem K L hS)

omit [NumberField K] in
@[simp]
theorem sUnit_smul_coe
    {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : IsGaloisStableFinitePlaces K L S)
    (σ : L ≃ₐ[K] L)
    (x : SUnitGroup (K := L) S) :
    letI := sUnitMulDistribMulAction K L S hS
    ((σ • x : SUnitGroup (K := L) S) : Lˣ) =
      Units.mapEquiv σ.toMulEquiv (x : Lˣ) :=
  rfl

/-- The action on the finite set `S` obtained by restricting the
finite-place permutation. -/
@[reducible]
noncomputable def stableFinitePlaceMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    MulAction (L ≃ₐ[K] L) S where
  smul σ v :=
    ⟨σ • (v : HeightOneSpectrum (𝓞 L)),
      IsGaloisStableFinitePlaces.smul_mem K L hS σ
        v.property⟩
  one_smul v := by
    apply Subtype.ext
    exact one_smul _ (v : HeightOneSpectrum (𝓞 L))
  mul_smul σ τ v := by
    apply Subtype.ext
    exact mul_smul σ τ (v : HeightOneSpectrum (𝓞 L))

/-- The permutation action on all logarithmic places
`InfinitePlace L ⊕ S`. -/
@[reducible]
noncomputable def logPlaceMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    MulAction (L ≃ₐ[K] L)
      (SUnitGroup.LogPlace (K := L) S) := by
  letI : MulAction (L ≃ₐ[K] L) S :=
    stableFinitePlaceMulAction K L S hS
  exact
    { smul := fun σ p =>
        match p with
        | Sum.inl w => Sum.inl (σ • w)
        | Sum.inr v => Sum.inr (σ • v)
      one_smul := by
        intro p
        cases p with
        | inl w =>
            change Sum.inl ((1 : L ≃ₐ[K] L) • w) =
              Sum.inl w
            rw [one_smul]
        | inr v =>
            change Sum.inr ((1 : L ≃ₐ[K] L) • v) =
              Sum.inr v
            rw [one_smul]
      mul_smul := by
        intro σ τ p
        cases p with
        | inl w =>
            change Sum.inl ((σ * τ) • w) =
              Sum.inl (σ • (τ • w))
            rw [mul_smul]
        | inr v =>
            change Sum.inr ((σ * τ) • v) =
              Sum.inr (σ • (τ • v))
            rw [mul_smul] }

/-- The additive action on the additive form of the `S`-unit group. -/
@[reducible]
noncomputable def additiveSUnitDistribMulAction
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : IsGaloisStableFinitePlaces K L S) :
    DistribMulAction (L ≃ₐ[K] L)
      (Additive (SUnitGroup (K := L) S)) := by
  letI := sUnitMulDistribMulAction K L S hS
  exact
    { smul := fun σ x =>
        Additive.ofMul
          (σ • (Additive.toMul x :
            SUnitGroup (K := L) S))
      one_smul := by
        intro x
        apply Additive.toMul.injective
        exact one_smul (L ≃ₐ[K] L) (Additive.toMul x :
          SUnitGroup (K := L) S)
      mul_smul := by
        intro σ τ x
        apply Additive.toMul.injective
        exact mul_smul σ τ (Additive.toMul x :
          SUnitGroup (K := L) S)
      smul_zero := by
        intro σ
        apply Additive.toMul.injective
        change σ • (1 : SUnitGroup (K := L) S) = 1
        exact MulDistribMulAction.smul_one σ
      smul_add := by
        intro σ x y
        apply Additive.toMul.injective
        exact MulDistribMulAction.smul_mul σ
          (Additive.toMul x : SUnitGroup (K := L) S)
          (Additive.toMul y : SUnitGroup (K := L) S) }

end FinitePlaceAction
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_Comparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Comparing finite-place completion models

For an exact extension `w` of the normalized absolute value at a finite
place `v` of `K`, its centre `W` is a finite place of `L`.  The absolute
values `w` and the standard normalized absolute value at `W` differ by a
positive real power.  Consequently the identity on `L` extends to a ring
equivalence between their completions and preserves the valuation ring.

Composing with the existing comparison between the standard
absolute-value completion and mathlib's concrete adic completion gives the
local factor comparison used in the adelic restricted-product bridge.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The existing comparison from the standard absolute-value completion
to the concrete adic completion is an isometry. -/
theorem relativeFinitePlaceCompletionRingEquiv_norm
    (W : HeightOneSpectrum (𝓞 L))
    (x : (HeightOneSpectrum.adicAbv L W).Completion) :
    ‖relativeFinitePlaceCompletionRingEquiv W x‖ = ‖x‖ := by
  change ‖relativeFinitePlaceCompletionRingHom W x‖ = ‖x‖
  exact
    (relativeFinitePlaceCompletionRingHom_isometry W).norm_map_of_map_zero
      (map_zero (relativeFinitePlaceCompletionRingHom W)) x
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_BaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit
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


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [NumberField K] in
/-- The map on infinite-place completions induced by the identity field
extension is the identity map. -/
@[simp]
theorem infinitePlaceCompletionMap_self_apply
    (W : InfinitePlace K)
    (x : W.Completion) :
    letI : W.1.LiesOver W.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1)
        (infinitePlaceBelow_self (K := K) W)⟩
    NumberField.LiesOver.completionMap
        (v := W) (w := W) x = x := by
  let : W.1.LiesOver W.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1)
      (infinitePlaceBelow_self (K := K) W)⟩
  refine InfinitePlace.Completion.induction_on W x ?_ ?_
  · exact isClosed_eq
      NumberField.LiesOver.continuous_completionMap
      continuous_id
  · intro y
    change
      NumberField.LiesOver.completionMap
          (y : W.Completion) =
        (y : W.Completion)
    rw [NumberField.LiesOver.completionMap_coe
      (v := W) (w := W) y]
    have hy :
        algebraMap (WithAbs W.1) (WithAbs W.1) y = y := by
      apply (WithAbs.equiv W.1).injective
      change
        algebraMap K K (WithAbs.equiv W.1 y) =
          WithAbs.equiv W.1 y
      rw [Algebra.algebraMap_self]
      rfl
    exact
      congrArg
        (fun z : WithAbs W.1 => (z : W.Completion)) hy

/-- Completion maps at infinite places compose in a tower of number
fields. -/
theorem infinitePlaceCompletionMap_comp_apply
    {M : Type*}
    [Field M] [NumberField M]
    [Algebra K M] [Algebra M L]
    [IsScalarTower K M L]
    (W : InfinitePlace L)
    (x :
      (infinitePlaceBelow
        (K := K) W).Completion) :
    let V :=
      infinitePlaceBelow (K := M) W
    let v :=
      infinitePlaceBelow (K := K) W
    letI : V.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1)
        (infinitePlaceBelow_infinitePlaceBelow
          (K := K) (M := M) (L := L) W)⟩
    letI : W.1.LiesOver V.1 := ⟨rfl⟩
    letI : W.1.LiesOver v.1 := ⟨rfl⟩
    NumberField.LiesOver.completionMap
        (v := V) (w := W)
        (NumberField.LiesOver.completionMap
          (v := v) (w := V) x) =
      NumberField.LiesOver.completionMap
        (v := v) (w := W) x := by
  dsimp only
  let V :=
    infinitePlaceBelow (K := M) W
  let v :=
    infinitePlaceBelow (K := K) W
  let : V.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1)
      (infinitePlaceBelow_infinitePlaceBelow
        (K := K) (M := M) (L := L) W)⟩
  let : W.1.LiesOver V.1 := ⟨rfl⟩
  let : W.1.LiesOver v.1 := ⟨rfl⟩
  refine InfinitePlace.Completion.induction_on v x ?_ ?_
  · exact isClosed_eq
      ((NumberField.LiesOver.continuous_completionMap
          (v := V) (w := W)).comp
        (NumberField.LiesOver.continuous_completionMap
          (v := v) (w := V)))
      (NumberField.LiesOver.continuous_completionMap
        (v := v) (w := W))
  · intro y
    rw [NumberField.LiesOver.completionMap_coe
        (v := v) (w := V) y,
      NumberField.LiesOver.completionMap_coe
        (v := V) (w := W)
        (algebraMap (WithAbs v.1) (WithAbs V.1) y),
      NumberField.LiesOver.completionMap_coe
        (v := v) (w := W) y]
    apply congrArg
      (fun z : WithAbs W.1 => (z : W.Completion))
    apply (WithAbs.equiv W.1).injective
    change
      algebraMap M L
          (algebraMap K M (WithAbs.equiv v.1 y)) =
        algebraMap K L (WithAbs.equiv v.1 y)
    rw [IsScalarTower.algebraMap_apply K M L]
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_EmbeddingNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

section RelativeAdeles

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [NumberField K]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K M]

/-- A field embedding inside an ambient Galois extension, extended to
relative adèles. -/
def adeleEmbedding (f : L →ₐ[K] M) :
    RelativeAdeleRing K L →ₐ[
      NumberField.AdeleRing (𝓞 K) K]
      RelativeAdeleRing K M :=
  scalarEmbedding
    (NumberField.AdeleRing (𝓞 K) K) f

/-- The induced homomorphism on relative idèles. -/
def ideleEmbedding (f : L →ₐ[K] M) :
    RelativeIdeleGroup K L →*
      RelativeIdeleGroup K M :=
  Units.map (adeleEmbedding f).toMonoidHom

end RelativeAdeles

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_NormLocalOrder
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod
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


theorem absNorm_eq_card_intrinsicAdicResidueField
    (K : Type u) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    [ValuativeRel (v.adicCompletion K)]
    [(Valued.v :
      Valuation (v.adicCompletion K)
        (WithZero (Multiplicative ℤ))).Compatible] :
    Ideal.absNorm v.asIdeal =
      Nat.card 𝓀[v.adicCompletion K] := by
  calc
    Ideal.absNorm v.asIdeal =
        Nat.card
          (Valued.ResidueField (v.adicCompletion K)) := by
      rw [Ideal.absNorm_apply]
      exact
        Nat.card_congr
          (GlobalClassFieldTheory.ClassFieldAxiom.ringOfIntegersQuotientEquivAdicResidueField
            (K := K) v).toEquiv
    _ = Nat.card 𝓀[v.adicCompletion K] := by
      exact
        (Nat.card_congr
          (intrinsicResidueFieldEquivValuedResidueField
            (v.adicCompletion K)).toEquiv).symm

end FiniteIdeleGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_FinitePlaceCompletionInstances
attribute [-instance] _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Canonical structures on finite completions

This module installs the complete discrete valuation, characteristic-zero,
and finite residue-field structures used by finite-place class-field
arithmetic.
-/

open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The distinguished valuation on a finite completion of a number field is
complete discrete. -/
noncomputable instance finitePlaceAdicCompletion_isCompleteDiscrete
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
      (Valued.v :
        Valuation (v₀.adicCompletion K)
          (WithZero (Multiplicative ℤ))) where
  isRankOneDiscrete := inferInstance
  isAdicComplete :=
    ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete

/-- The residue field of a finite completion of a number field is finite. -/
noncomputable instance finitePlaceAdicCompletion_residueFinite
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    Finite
      (IsLocalRing.ResidueField
        (Valued.v :
          Valuation (v₀.adicCompletion K)
            (WithZero (Multiplicative ℤ))).valuationSubring) := by
  change Finite (Valued.ResidueField (v₀.adicCompletion K))
  exact _root_.finite_adicCompletion_residueField K v₀

end GlobalClassFieldTheory.ClassFieldAxiom

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local fields

A local-field package here is a chosen complete discretely valued field with
finite residue field.  The topology-first mathlib class remains available
through imports; this file only adds the chosen-valuation API needed downstream.
-/

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

/-- A local field with a chosen complete discrete valuation and finite residue field. -/
structure LocalField (K : Type u) [Field K] extends CompleteDVF.{u, v} K where
  /-- The residue field of the chosen complete discrete valuation is finite. -/
  [residueFinite : Finite toCompleteDVF.residueField]

attribute [instance] LocalField.residueFinite

namespace LocalField

variable {K : Type u} [Field K]

/-- The residue field of a local field package. -/
abbrev residueField (F : LocalField.{u, v} K) : Type u :=
  F.toCompleteDVF.residueField

/-- The valuation subring of a local field package. -/
abbrev valuationSubring (F : LocalField.{u, v} K) : Type u :=
  F.toCompleteDVF.valuationSubring

/-- The residue map of a local field package. -/
abbrev residueMap (F : LocalField.{u, v} K) :
    RingHom F.valuationSubring F.residueField :=
  F.toCompleteDVF.residueMap

/-- The residue characteristic of a local field. -/
noncomputable abbrev residueCharacteristic (F : LocalField.{u, v} K) : ℕ :=
  ringChar F.residueField

/-- Establishes the inequality `F.residueCharacteristic ≠ 0`. -/
theorem residueCharacteristic_ne_zero (F : LocalField.{u, v} K) :
    F.residueCharacteristic ≠ 0 :=
  CharP.ringChar_ne_zero_of_finite F.residueField

/-- Proves the primality statement `Nat.Prime F.residueCharacteristic`. -/
theorem residueCharacteristic_prime (F : LocalField.{u, v} K) :
    Nat.Prime F.residueCharacteristic := by
  change Nat.Prime (ringChar F.toCompleteDVF.residueField)
  let : NoZeroDivisors F.toCompleteDVF.residueField :=
    GroupWithZero.noZeroDivisors
  exact CharP.prime_ringChar F.toCompleteDVF.residueField

/-- The target has the stated characteristic: `CharP F.residueField F.residueCharacteristic`. -/
instance residueField_charP_residueCharacteristic (F : LocalField.{u, v} K) :
    CharP F.residueField F.residueCharacteristic :=
  ringChar.charP (R := F.residueField)

/-- Registers the mathematical fact `Fact F.residueCharacteristic.Prime` for typeclass inference. -/
instance residueCharacteristic.fact_prime (F : LocalField.{u, v} K) :
    Fact F.residueCharacteristic.Prime :=
  ⟨F.residueCharacteristic_prime⟩

/-- The residue characteristic vanishes after reduction modulo the maximal
ideal.  This is the first characteristic input in the converse direction of
the local-field structure theory, the local-field structure classification. -/
theorem residueCharacteristic_natCast_residue_eq_zero
    (F : LocalField.{u, v} K) :
    F.residueMap (F.residueCharacteristic : F.valuationSubring) = 0 := by
  calc
    F.residueMap (F.residueCharacteristic : F.valuationSubring)
        = (F.residueCharacteristic : F.residueField) := by
          exact map_natCast F.residueMap F.residueCharacteristic
    _ = 0 := by
      exact ringChar.Nat.cast_ringChar (R := F.residueField)

/-- In mixed characteristic, the residue characteristic is a nonzero element of
the field even though it reduces to zero. -/
theorem natCast_residueCharacteristic_ne_zero_of_charZero
    (F : LocalField.{u, v} K) [CharZero K] :
    (F.residueCharacteristic : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr F.residueCharacteristic_ne_zero

/-- Every integer lies in the valuation subring.  This is the denominator
control input for the mixed-characteristic branch of the local-field structure classification. -/
theorem valuation_intCast_le_one (F : LocalField.{u, v} K) (z : ℤ) :
    F.toCompleteDVF.valuation (z : K) ≤ 1 := by
  have hmem :
      ((z : F.valuationSubring) : K) ∈
        F.toCompleteDVF.valuation.valuationSubring :=
    (z : F.valuationSubring).property
  have hcast :
      ((z : F.valuationSubring) : K) = (z : K) := by
    exact map_intCast F.toCompleteDVF.valuation.valuationSubring.subtype z
  rw [← hcast]
  exact
    (F.toCompleteDVF.mem_valuationSubring_iff
      ((z : F.valuationSubring) : K)).1 hmem

/-- Every natural number lies in the valuation subring. -/
theorem valuation_natCast_le_one (F : LocalField.{u, v} K) (n : ℕ) :
    F.toCompleteDVF.valuation (n : K) ≤ 1 := by
  simpa using F.valuation_intCast_le_one (n : ℤ)

/-- In a reduced rational number, if the denominator is divisible by the
residue characteristic then the numerator is not. -/
theorem not_residueCharacteristic_dvd_rat_num_of_dvd_den
    (F : LocalField.{u, v} K) (q : ℚ)
    (hden : F.residueCharacteristic ∣ q.den) :
    ¬ (F.residueCharacteristic : ℤ) ∣ q.num := by
  intro hnum
  have hnumNat : F.residueCharacteristic ∣ q.num.natAbs :=
    (Int.natCast_dvd.mp hnum)
  have hp_one : F.residueCharacteristic = 1 :=
    Nat.eq_one_of_dvd_coprimes q.reduced hnumNat hden
  exact F.residueCharacteristic_prime.ne_one hp_one

end LocalField
end LocalFieldTheory.DiscreteValuationField
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_CompleteRangeRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Range restriction for complete discretely valued fields

This file specializes multiplicative-range restriction to `CompleteDVF` and
transports residue finiteness, adic completeness, cyclicity, and discreteness.
-/

noncomputable section

universe u v

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- Restrict the chosen valuation of a complete DVF to its actual
multiplicative range.  This keeps the valuation ring, maximal ideal, and
residue field unchanged while eliminating irrelevant ambient value-group
elements. -/
def mrangeRestrict (F : CompleteDVF.{u, v} K) :
    _root_.Valuation K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
  WithZeroValuation.mrangeRestrict F.valuation

/--
The defining evaluation formula for `mrangeRestrict` is `((CompleteDVF.mrangeRestrict F) x :
F.ValueGroup) = F.valuation x`.
-/
@[simp]
theorem mrangeRestrict_apply (F : CompleteDVF.{u, v} K) (x : K) :
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) x : F.ValueGroup) = F.valuation x :=
  rfl

/-- The residue field remains finite after restricting the value group to the
actual multiplicative range. -/
theorem mrangeRestrict_residueField_finite
    (F : CompleteDVF.{u, v} K) [Finite F.residueField] :
    Finite (IsLocalRing.ResidueField (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).valuationSubring) :=
  Finite.of_equiv F.residueField
    (WithZeroValuation.residueFieldEquivMrangeRestrict
      F.valuation).toEquiv

/-- The actual multiplicative range of a complete-DVF valuation is generated
by the image of a discrete valuation generator. -/
theorem mrangeRestrict_units_isCyclic
    (F : CompleteDVF.{u, v} K) :
    IsCyclic (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ := by
  let γ : F.ValueGroupˣ :=
    _root_.Valuation.IsRankOneDiscrete.generator F.valuation
  have hγrange : (γ : F.ValueGroup) ∈ Set.range F.valuation :=
    _root_.Valuation.IsRankOneDiscrete.generator_mem_range K F.valuation
  let γm : MonoidHom.mrange F.valuation.toMonoidWithZeroHom :=
    ⟨(γ : F.ValueGroup), hγrange⟩
  have hγm_ne : γm ≠ 0 := by
    intro hzero
    have hγzero : (γ : F.ValueGroup) = 0 := by
      simpa [γm] using
        congrArg
          (fun z : MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom => (z : F.ValueGroup))
          hzero
    exact Units.ne_zero γ hγzero
  let δ : (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ :=
    Units.mk0 γm hγm_ne
  have htop : Subgroup.zpowers δ = ⊤ := by
    rw [eq_top_iff]
    intro η _
    have hη_ne : ((η : MonoidHom.mrange
        F.valuation.toMonoidWithZeroHom) : F.ValueGroup) ≠ 0 := by
      intro hzero
      have hηzero :
          (η : MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom) = 0 := by
        ext
        exact hzero
      exact Units.ne_zero η hηzero
    obtain ⟨x, hx⟩ :=
      MonoidHom.mem_mrange.mp
        ((η : MonoidHom.mrange
          F.valuation.toMonoidWithZeroHom).2)
    let ηΓ : F.ValueGroupˣ :=
      Units.mk0
        (((η : MonoidHom.mrange
          F.valuation.toMonoidWithZeroHom) : F.ValueGroup))
        hη_ne
    have hηΓ_mem :
        ηΓ ∈ MonoidWithZeroHom.valueGroup
          (MonoidWithZeroHom.ofClass F.valuation) :=
      MonoidWithZeroHom.mem_valueGroup
        (MonoidWithZeroHom.ofClass F.valuation) ⟨x, hx⟩
    rw [← _root_.Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup
      F.valuation, Subgroup.mem_zpowers_iff] at hηΓ_mem
    rcases hηΓ_mem with ⟨z, hz⟩
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨z, ?_⟩
    let φ :
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ →*
          F.ValueGroupˣ :=
      Units.map (MonoidHom.mrange F.valuation.toMonoidWithZeroHom).subtype
    have hsub_inj :
        Function.Injective
          ((MonoidHom.mrange F.valuation.toMonoidWithZeroHom).subtype) := by
      intro a b h
      exact Subtype.ext h
    have hφinj : Function.Injective φ :=
      Units.map_injective hsub_inj
    have hφδ : φ δ = γ := by
      apply Units.ext
      rfl
    have hφη : φ η = ηΓ := by
      apply Units.ext
      rfl
    apply hφinj
    calc
      φ (δ ^ z) = φ δ ^ z := map_zpow φ δ z
      _ = γ ^ z := by rw [hφδ]
      _ = ηΓ := hz
      _ = φ η := hφη.symm
  exact (isCyclic_iff_exists_zpowers_eq_top).2 ⟨δ, htop⟩

/-- The range-restricted valuation is nontrivial whenever the original
complete-DVF valuation is nontrivial. -/
theorem mrangeRestrict_isNontrivial
    (F : CompleteDVF.{u, v} K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsNontrivial := by
  rcases _root_.Valuation.IsNontrivial.exists_val_nontrivial
      (v := F.valuation) with ⟨x, hx0, hx1⟩
  refine ⟨⟨x, ?_, ?_⟩⟩
  · intro hx
    exact hx0 (by
      have h :=
        congrArg
          (fun z : MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom => (z : F.ValueGroup)) hx
      simpa [CompleteDVF.mrangeRestrict, WithZeroValuation.mrangeRestrict] using h)
  · intro hx
    exact hx1 (by
      have h :=
        congrArg
          (fun z : MonoidHom.mrange
            F.valuation.toMonoidWithZeroHom => (z : F.ValueGroup)) hx
      simpa [CompleteDVF.mrangeRestrict, WithZeroValuation.mrangeRestrict] using h)

/-- Restricting a complete-DVF valuation to its actual multiplicative range
preserves rank-one discreteness. -/
theorem mrangeRestrict_isRankOneDiscrete
    (F : CompleteDVF.{u, v} K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsRankOneDiscrete := by
  have :
      IsCyclic
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_units_isCyclic F)
  have : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsNontrivial :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isNontrivial F)
  have :
      IsCyclic (MonoidWithZeroHom.valueGroup
        (MonoidWithZeroHom.ofClass
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F))) :=
    Subgroup.isCyclic_of_le (show
      MonoidWithZeroHom.valueGroup
        (MonoidWithZeroHom.ofClass
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F)) ≤
          ⊤ from le_top)
  infer_instance

/-- The range-restricted valuation is rank one as a valuation into its actual
value group. -/
@[implicit_reducible]
noncomputable def mrangeRestrict_rankOne
    (F : CompleteDVF.{u, v} K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).RankOne := by
  haveI : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsNontrivial :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isNontrivial F)
  haveI :
      IsCyclic
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom)ˣ :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_units_isCyclic F)
  exact WithZeroValuation.rankOneOfUnitsIsCyclic (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F)

end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_IntegerValuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

/-- Valuation of the logarithm-series term `x^n / n`, with a fixed
ramification-index scale in the denominator valuation. -/
theorem ofWithZeroValuation_val_pow_div_natCast_scaled
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (e : ℕ) (x : Kˣ) (hnK : (n : K) ≠ 0)
    (hnval :
      v (n : K) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n : ℤ)))) :
    (ofWithZeroValuation v).val
        (x ^ n / Units.mk0 (n : K) hnK) =
      (n : ℤ) * (ofWithZeroValuation v).val x -
        (e : ℤ) * (padicValNat p n : ℤ) := by
  rw [(ofWithZeroValuation v).val_div, (ofWithZeroValuation v).val_pow,
    ofWithZeroValuation_val_natCast_scaled v e hnK hnval]

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_RangeRestrictedTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Topology of range-restricted complete discretely valued fields

This file equips the multiplicative-range valuation with its valued and normed
field structures and transports adic completeness, compactness, properness,
and completeness.
-/

noncomputable section

universe u v

open Filter WithZero
open scoped NNReal Valued Filter WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The canonical `Valued` structure attached to the range-restricted complete
DVF valuation. -/
@[implicit_reducible]
noncomputable def mrangeRestrictValued
    (F : CompleteDVF.{u, v} K) :
    Valued K (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
  Valued.mk' (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F)

@[instance_reducible]
noncomputable def mrangeRestrictValued_rankOne
    (F : CompleteDVF.{u, v} K) :
    (@Valued.v K _
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) _
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)).RankOne := by
  change
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).RankOne
  exact
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_rankOne F

/-- The rank-one normalized complete-DVF valuation supplies the normed-field
structure expected by mathlib's finite-dimensional closed-subspace theorem. -/
@[implicit_reducible]
noncomputable def mrangeRestrict_nontriviallyNormedField
    (F : CompleteDVF.{u, v} K) :
    NontriviallyNormedField K :=
  Valued.toNontriviallyNormedField
    (L := K)
    (Γ₀ := MonoidHom.mrange F.valuation.toMonoidWithZeroHom)
    (val := LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    (hv := mrangeRestrictValued_rankOne F)

/-- For the topology induced by the range-restricted rank-one valuation, the
valuation ring has its maximal-ideal adic topology. -/
theorem mrangeRestrict_integer_isAdic
    (F : CompleteDVF.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    letI : NontriviallyNormedField K :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
    IsAdic (𝓂[K]) := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let : Valued K Γ :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let : NontriviallyNormedField K :=
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F)
  have : IsCyclic Γˣ := by
    simpa [Γ] using
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_units_isCyclic F)
  let : MulArchimedean Γ :=
    WithZeroValuation.units_isCyclic_mulArchimedean Γ
  have : (Valued.v : _root_.Valuation K Γ).IsRankOneDiscrete := by
    change
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F).IsRankOneDiscrete
    exact
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_isRankOneDiscrete F)
  exact ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdic

end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_SeriesValuationEstimates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/-- Real lower bound for the valuation of `x^n / n`, with a fixed
ramification-index scale in the denominator valuation. -/
theorem ofWithZeroValuation_val_pow_div_natCast_scaled_real_lower_bound
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : (n : K) ≠ 0)
    (hnval :
      v (n : K) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n : ℤ))))
    {c : ℝ} (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    (n : ℝ) * c - (e : ℝ) * Real.logb (p : ℝ) (n : ℝ) ≤
      ((ofWithZeroValuation v).val
        (x ^ n / Units.mk0 (n : K) hnK) : ℝ) := by
  have hterm :=
    ofWithZeroValuation_val_pow_div_natCast_scaled
      (v := v) (p := p) (n := n) e x hnK hnval
  have hlin :
      (n : ℝ) * c ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) :=
    mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)
  have hden_base :
      (padicValNat p n : ℝ) ≤ Real.logb (p : ℝ) (n : ℝ) :=
    padicValNat_le_real_logb (p := p) n
  have hden :
      (e : ℝ) * (padicValNat p n : ℝ) ≤
        (e : ℝ) * Real.logb (p : ℝ) (n : ℝ) :=
    mul_le_mul_of_nonneg_left hden_base (Nat.cast_nonneg e)
  have hmain :
      (n : ℝ) * c - (e : ℝ) * Real.logb (p : ℝ) (n : ℝ) ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) -
          (e : ℝ) * (padicValNat p n : ℝ) := by
    linarith
  calc
    (n : ℝ) * c - (e : ℝ) * Real.logb (p : ℝ) (n : ℝ) ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) -
          (e : ℝ) * (padicValNat p n : ℝ) := hmain
    _ =
        ((ofWithZeroValuation v).val
          (x ^ n / Units.mk0 (n : K) hnK) : ℝ) := by
      rw [hterm]
      norm_num [Int.cast_sub, Int.cast_mul]

/-- The valuations of the logarithm-series terms `x^(n+1)/(n+1)` tend to
`+∞` when the natural-number denominators have a fixed ramification-index
scale in their `p`-adic valuation. -/
theorem ofWithZeroValuation_val_pow_succ_div_natCast_scaled_tendsto_atTop
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
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
          ((n + 1 : ℕ) : ℝ) * c -
            (e : ℝ) * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ))
        atTop atTop :=
    tendsto_nat_succ_mul_const_sub_const_mul_logb_atTop
      (p := p) (c := c) (C := (e : ℝ)) hcpos
  have hle :
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) * c -
          (e : ℝ) * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) ≤ᶠ[atTop]
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) : ℝ)) := by
    exact Eventually.of_forall fun n => by
      simpa [Nat.cast_add, Nat.cast_one] using
        ofWithZeroValuation_val_pow_div_natCast_scaled_real_lower_bound
          (v := v) (p := p) (e := e) (n := n + 1) x
          (hnK n) (hnval n) hc
  exact tendsto_atTop_mono' atTop hle hsource

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_UniformizerIntegerValuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.ofWithZeroValuation_val _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integer valuations from complete-DVF uniformizers

A chosen uniformizer determines the exponent of every nonzero field value and
therefore an integer-valued multiplicative valuation on field units.
-/

noncomputable section

universe u v

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The nonzero value of a field unit, regarded as a unit of the ambient value
group. -/
noncomputable def fieldUnitValueUnit
    (F : CompleteDVF.{u, v} K) (x : Kˣ) : F.ValueGroupˣ :=
  Units.mk0 (F.valuation (x : K))
    ((_root_.Valuation.ne_zero_iff F.valuation).2 x.ne_zero)

/-- Establishes the identity `(CompleteDVF.fieldUnitValueUnit F) (1 : Kˣ) = 1`. -/
@[simp]
theorem fieldUnitValueUnit_one (F : CompleteDVF.{u, v} K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) (1 : Kˣ) = 1 := by
  ext
  simp [fieldUnitValueUnit]

/--
`fieldUnitValueUnit` satisfies the multiplication formula `(CompleteDVF.fieldUnitValueUnit F) (x *
y) = (CompleteDVF.fieldUnitValueUnit F) x * (CompleteDVF.fieldUnitValueUnit F) y`.
-/
@[simp]
theorem fieldUnitValueUnit_mul
    (F : CompleteDVF.{u, v} K) (x y : Kˣ) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) (x * y) =
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x * (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) y := by
  ext
  simp [fieldUnitValueUnit]

/-- The value of a chosen uniformizer, regarded as a unit of the ambient value
group. -/
noncomputable def uniformizerValueUnit
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    F.ValueGroupˣ :=
  Units.mk0 (F.valuation (π : K)) hπ.val_ne_zero

/-- The value of every field unit is an integral power of the value of a chosen
uniformizer. -/
theorem exists_uniformizerValueUnit_zpow_eq_fieldUnitValueUnit
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    ∃ n : ℤ,
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^ n = (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x := by
  have hxmem :
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x ∈
        MonoidWithZeroHom.valueGroup
          (MonoidWithZeroHom.ofClass F.valuation) := by
    exact
      MonoidWithZeroHom.mem_valueGroup
        (MonoidWithZeroHom.ofClass F.valuation)
        (show (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x : F.ValueGroup)) ∈
            Set.range F.valuation from
          ⟨(x : K), by simp [fieldUnitValueUnit]⟩)
  rw [hπ.zpowers_eq_valueGroup, Subgroup.mem_zpowers_iff] at hxmem
  simpa [uniformizerValueUnit] using hxmem

/-- Integral powers of the value of a uniformizer are indexed uniquely. -/
theorem uniformizerValueUnit_zpow_inj
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {m n : ℤ} :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^ m =
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^ n ↔
      m = n := by
  constructor
  · intro h
    have hvalue :
        F.valuation (π : K) ^ m =
          F.valuation (π : K) ^ n := by
      simpa [uniformizerValueUnit, Units.val_zpow_eq_zpow_val] using
        congrArg (fun γ : F.ValueGroupˣ => (γ : F.ValueGroup)) h
    exact
      (zpow_right_inj₀ hπ.val_pos (ne_of_lt hπ.val_lt_one)).1 hvalue
  · intro h
    rw [h]

/-- The integer exponent of the value of a field unit with respect to a chosen
uniformizer. -/
noncomputable def uniformizerValueExponent
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) : ℤ :=
  Classical.choose
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.exists_uniformizerValueUnit_zpow_eq_fieldUnitValueUnit F) hπ x)

/-- The chosen exponent really recovers the value of the field unit. -/
theorem uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x =
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x :=
  Classical.choose_spec
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.exists_uniformizerValueUnit_zpow_eq_fieldUnitValueUnit F) hπ x)

/-- The integer-valued multiplicative valuation on `Kˣ` attached to a chosen
uniformizer of an arbitrary complete DVF.  Its value is the exponent of the
field-unit value as a power of the uniformizer value. -/
noncomputable def multiplicativeIntegerValuationOfUniformizer
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    MultiplicativeIntegerValuation Kˣ where
  val x := (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x
  map_one := by
    apply ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_inj F) hπ).1
    rw [(LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]
    simp
  map_mul x y := by
    apply ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_inj F) hπ).1
    calc
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ (x * y) =
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) (x * y) := by
        rw [(LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]
      _ = (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x * (LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) y := by
        rw [(LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul F)]
      _ =
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x *
            (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ y := by
        rw [(LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F),
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]
      _ =
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^
            ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x +
              (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ y) := by
        rw [← zpow_add]

/--
Establishes the identity `((CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ).val x =
(CompleteDVF.uniformizerValueExponent F) hπ x`.
-/
@[simp]
theorem multiplicativeIntegerValuationOfUniformizer_val
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ).val x =
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x :=
  rfl

/-- The chosen uniformizer has integer value one for the attached valuation. -/
theorem multiplicativeIntegerValuationOfUniformizer_isUniformizer
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ).IsUniformizer
      (Units.mk0 (π : K) hπ.ne_zero) := by
  change (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ (Units.mk0 (π : K) hπ.ne_zero) = 1
  apply ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_inj F) hπ).1
  rw [(LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]
  ext
  simp [fieldUnitValueUnit, uniformizerValueUnit]

/-- The zero subgroup of the attached integer-valued valuation is exactly the
valuation-subring unit group. -/
theorem multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup
    (F : CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ).zeroSubgroup =
      F.valuation.valuationSubring.unitGroup := by
  ext x
  rw [LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.mem_zeroSubgroup_iff,
    _root_.Valuation.mem_unitGroup_iff]
  change (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent F) hπ x = 0 ↔
    F.valuation (x : K) = 1
  constructor
  · intro hx
    have hvalue :=
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F) hπ x
    rw [hx, zpow_zero] at hvalue
    have hvalue' :=
      congrArg (fun γ : F.ValueGroupˣ => (γ : F.ValueGroup)) hvalue
    simpa [fieldUnitValueUnit] using hvalue'.symm
  · intro hx
    apply ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_inj F) hπ).1
    rw [(LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]
    ext
    simp [fieldUnitValueUnit, hx]

end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_ValuationSubringUnitMap
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Valuation-subring units inside field units

This file defines the canonical homomorphism from units of a complete-DVF
valuation ring to units of its fraction field.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The inclusion `O_K^* -> K^*` for the chosen valuation ring of a complete
DVF. -/
noncomputable def valuationSubringUnitsToFieldUnits
    (F : CompleteDVF.{u, v} K) : F.valuationSubringˣ →* Kˣ :=
  F.valuation.valuationSubring.unitGroup.subtype.comp
    F.valuation.valuationSubring.unitGroupMulEquiv.symm.toMonoidHom

/--
The defining evaluation formula for `coe_valuationSubringUnitsToFieldUnits` is
`(((CompleteDVF.valuationSubringUnitsToFieldUnits F) a : Kˣ) : K) = (a : F.valuationSubring)`.
-/
@[simp] theorem coe_valuationSubringUnitsToFieldUnits_apply
    (F : CompleteDVF.{u, v} K) (a : F.valuationSubringˣ) :
    (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits F) a : Kˣ) : K) =
      (a : F.valuationSubring) := by
  change
    ((F.valuation.valuationSubring.unitGroupMulEquiv.symm a : Kˣ) : K) =
      (a : K)
  exact _root_.ValuationSubring.coe_unitGroupMulEquiv_symm_apply
    (A := F.valuation.valuationSubring) (K := K) a


end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_DenominatorValuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

/-- Package a standard `ℤᵐ⁰`-valued complete discrete valuation with finite
residue field as a local field. -/
def ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    LocalField.{u, 0} K where
  toCompleteDVF :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      instValueGroup := coherentWithZeroMultiplicativeIntGroup
      valuation := v
      instCompleteDiscrete := inferInstance }
  residueFinite := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance

/-- The ramification index `e = v_K(p)` of a standard mixed-characteristic
local field, obtained from the exponent of the value of its residue
characteristic `p`. -/
def ramificationIndexOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K] : ℕ :=
  Int.toNat
    (-WithZero.log
      (v ((ofWithZeroValuation v).residueCharacteristic : K)))

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCoreBase_ProductArgument
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/-- The formal product argument is the power-series image of the corresponding
finite polynomial. -/
theorem formalLogOnePlusProductArgument_eq_coe_polynomial
    (A : Type*) [CommRing A] :
    formalLogOnePlusProductArgument A =
      (formalLogOnePlusProductArgumentPolynomial A :
        MvPowerSeries (Fin 2) A) := by
  simp [formalLogOnePlusProductArgument,
    formalLogOnePlusProductArgumentPolynomial]

/-- Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductArgument A) = 0`. -/
theorem formalLogOnePlusProductArgument_coeff_eq_zero_of_not_basic
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ)
    (hleft : e ≠ Finsupp.single (0 : Fin 2) 1)
    (hright : e ≠ Finsupp.single (1 : Fin 2) 1)
    (hmixed :
      e ≠
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1) :
    MvPowerSeries.coeff e (formalLogOnePlusProductArgument A) = 0 := by
  rw [formalLogOnePlusProductArgument_coeff]
  simp [hleft, hright, hmixed]

/-- Proves the bound `e (0 : Fin 2) ≤ 1`. -/
theorem formalLogOnePlusProductArgument_coeff_ne_zero_left_coord_le_one
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ)
    (hcoeff : MvPowerSeries.coeff e
      (formalLogOnePlusProductArgument A) ≠ 0) :
    e (0 : Fin 2) ≤ 1 := by
  by_contra hle
  have hgt : 1 < e (0 : Fin 2) := Nat.lt_of_not_ge hle
  have hleft : e ≠ Finsupp.single (0 : Fin 2) 1 := by
    intro he
    have hcoord : e (0 : Fin 2) ≤ 1 := by simp [he]
    exact (not_le_of_gt hgt) hcoord
  have hright : e ≠ Finsupp.single (1 : Fin 2) 1 := by
    intro he
    have hcoord : e (0 : Fin 2) ≤ 1 := by simp [he]
    exact (not_le_of_gt hgt) hcoord
  have hmixed :
      e ≠
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1 := by
    intro he
    have hcoord : e (0 : Fin 2) ≤ 1 := by simp [he]
    exact (not_le_of_gt hgt) hcoord
  exact hcoeff
    (formalLogOnePlusProductArgument_coeff_eq_zero_of_not_basic
      A e hleft hright hmixed)

/-- Proves the bound `e (1 : Fin 2) ≤ 1`. -/
theorem formalLogOnePlusProductArgument_coeff_ne_zero_right_coord_le_one
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ)
    (hcoeff : MvPowerSeries.coeff e
      (formalLogOnePlusProductArgument A) ≠ 0) :
    e (1 : Fin 2) ≤ 1 := by
  by_contra hle
  have hgt : 1 < e (1 : Fin 2) := Nat.lt_of_not_ge hle
  have hleft : e ≠ Finsupp.single (0 : Fin 2) 1 := by
    intro he
    have hcoord : e (1 : Fin 2) ≤ 1 := by simp [he]
    exact (not_le_of_gt hgt) hcoord
  have hright : e ≠ Finsupp.single (1 : Fin 2) 1 := by
    intro he
    have hcoord : e (1 : Fin 2) ≤ 1 := by simp [he]
    exact (not_le_of_gt hgt) hcoord
  have hmixed :
      e ≠
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1 := by
    intro he
    have hcoord : e (1 : Fin 2) ≤ 1 := by simp [he]
    exact (not_le_of_gt hgt) hcoord
  exact hcoeff
    (formalLogOnePlusProductArgument_coeff_eq_zero_of_not_basic
      A e hleft hright hmixed)

/--
Establishes the identity `e = Finsupp.single (0 : Fin 2) 1 ∨ e = Finsupp.single (1 : Fin 2) 1 ∨ e
= Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1`.
-/
theorem formalLogOnePlusProductArgument_coeff_ne_zero_eq_basic
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ)
    (hcoeff : MvPowerSeries.coeff e
      (formalLogOnePlusProductArgument A) ≠ 0) :
    e = Finsupp.single (0 : Fin 2) 1 ∨
      e = Finsupp.single (1 : Fin 2) 1 ∨
        e =
          Finsupp.single (0 : Fin 2) 1 +
            Finsupp.single (1 : Fin 2) 1 := by
  have hleftle :
      e (0 : Fin 2) ≤ 1 :=
    formalLogOnePlusProductArgument_coeff_ne_zero_left_coord_le_one A e hcoeff
  have hrightle :
      e (1 : Fin 2) ≤ 1 :=
    formalLogOnePlusProductArgument_coeff_ne_zero_right_coord_le_one A e hcoeff
  have hzeroCoeff :
      MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ)
        (formalLogOnePlusProductArgument A) = 0 := by
    simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using
      formalLogOnePlusProductArgument_constantCoeff A
  have hnotzero : e ≠ 0 := by
    intro he
    exact hcoeff (by simpa [he] using hzeroCoeff)
  rcases (Nat.le_one_iff_eq_zero_or_eq_one).1 hleftle with hleft0 | hleft1
  · rcases (Nat.le_one_iff_eq_zero_or_eq_one).1 hrightle with hright0 | hright1
    · exfalso
      exact hnotzero
        (finsupp_fin_two_eq_zero_of_coords_eq_zero e hleft0 hright0)
    · exact Or.inr <| Or.inl <|
        finsupp_fin_two_eq_single_right_of_coords_eq e hleft0 hright1
  · rcases (Nat.le_one_iff_eq_zero_or_eq_one).1 hrightle with hright0 | hright1
    · exact Or.inl <|
        finsupp_fin_two_eq_single_left_of_coords_eq e hleft1 hright0
    · exact Or.inr <| Or.inr <|
        finsupp_fin_two_eq_mixed_of_coords_eq_one e hleft1 hright1


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCoreBase_BasicFactors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/--
Characterizes `formalLogOnePlusProductArgumentBasicFactorLabel m = (1 : Fin 3)` by the equivalent
condition `m = Finsupp.single (1 : Fin 2) 1`.
-/
theorem formalLogOnePlusProductArgumentBasicFactorLabel_eq_one
    {m : Fin 2 →₀ ℕ} :
    formalLogOnePlusProductArgumentBasicFactorLabel m = (1 : Fin 3) ↔
      m = Finsupp.single (1 : Fin 2) 1 := by
  unfold formalLogOnePlusProductArgumentBasicFactorLabel
  by_cases hleft : m = Finsupp.single (0 : Fin 2) 1
  · simp [hleft, finsupp_fin_two_single_left_ne_single_right]
  · by_cases hright : m = Finsupp.single (1 : Fin 2) 1
    · have hrightLeft :
          Finsupp.single (1 : Fin 2) 1 ≠
            Finsupp.single (0 : Fin 2) 1 :=
        finsupp_fin_two_single_left_ne_single_right.symm
      simp [hright, hrightLeft]
    · simp [hleft, hright]

/--
Characterizes `l ∈ formalLogOnePlusProductArgumentBasicFactorProductChoices q` by the equivalent
condition `l.support ⊆ Finset.range q ∧ ∀ i ∈ Finset.range q,
formalLogOnePlusProductArgumentBasicFactor (l i)`.
-/
theorem mem_formalLogOnePlusProductArgumentBasicFactorProductChoices
    {q : ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)} :
    l ∈ formalLogOnePlusProductArgumentBasicFactorProductChoices q ↔
      l.support ⊆ Finset.range q ∧
        ∀ i ∈ Finset.range q,
          formalLogOnePlusProductArgumentBasicFactor (l i) := by
  classical
  rw [formalLogOnePlusProductArgumentBasicFactorProductChoices,
    Finset.mem_finsupp_iff]
  constructor
  · intro h
    exact
      ⟨h.1, fun i hi =>
        mem_formalLogOnePlusProductArgumentBasicFactorFinset.1
          (h.2 i hi)⟩
  · intro h
    exact
      ⟨h.1, fun i hi =>
        mem_formalLogOnePlusProductArgumentBasicFactorFinset.2
          (h.2 i hi)⟩

/--
Characterizes `l ∈ formalLogOnePlusProductArgumentBasicFactorChoices q e` by the equivalent
condition `l ∈ Finset.finsuppAntidiag (Finset.range q) e ∧ ∀ i ∈ Finset.range q,
formalLogOnePlusProductArgumentBasicFactor (l i)`.
-/
theorem mem_formalLogOnePlusProductArgumentBasicFactorChoices
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)} :
    l ∈ formalLogOnePlusProductArgumentBasicFactorChoices q e ↔
      l ∈ Finset.finsuppAntidiag (Finset.range q) e ∧
        ∀ i ∈ Finset.range q,
          formalLogOnePlusProductArgumentBasicFactor (l i) := by
  classical
  simp [formalLogOnePlusProductArgumentBasicFactorChoices]

/--
Establishes the identity `formalLogOnePlusProductArgumentRightChoiceCount q l =
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1`.
-/
theorem formalLogOnePlusProductArgument_rightChoiceCount_eq_labelCount_one
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) :
    formalLogOnePlusProductArgumentRightChoiceCount q l =
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 := by
  classical
  rw [formalLogOnePlusProductArgumentRightChoiceCount,
    formalLogOnePlusProductArgumentBasicFactorLabelCount]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hright : l i = Finsupp.single (1 : Fin 2) 1
  · simp [hright]
  · have hlabel :
        formalLogOnePlusProductArgumentBasicFactorLabel (l i) ≠
          (1 : Fin 3) := by
      intro hone
      exact hright
        (formalLogOnePlusProductArgumentBasicFactorLabel_eq_one.1 hone)
    simp [hright, hlabel]

/--
Establishes the identity `formalLogOnePlusProductArgumentMixedChoiceCount q l =
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2`.
-/
theorem formalLogOnePlusProductArgument_mixedChoiceCount_eq_labelCount_two
    {q : ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentMixedChoiceCount q l =
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 := by
  classical
  rw [formalLogOnePlusProductArgumentMixedChoiceCount,
    formalLogOnePlusProductArgumentBasicFactorLabelCount]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hmixed :
      l i =
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1
  · simp [hmixed]
  · have hlabel :
        formalLogOnePlusProductArgumentBasicFactorLabel (l i) ≠
          (2 : Fin 3) := by
      intro htwo
      rcases hbasic i hi with hleft | hright | hmixed'
      · rw [hleft] at htwo
        simp at htwo
      · rw [hright] at htwo
        simp at htwo
      · exact hmixed hmixed'
    simp [hmixed, hlabel]


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCoreBase_ChoiceCountSystem
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/--
Characterizes `l ∈ formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e` by the
equivalent condition `l ∈ formalLogOnePlusProductArgumentBasicFactorProductChoices q ∧
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 = q - e (1 : Fin 2) ∧
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 = q - e (0 : Fin 2) ∧
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 = e (0 : Fin 2) + e (1 : Fin 2) - q`.
-/
theorem mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)} :
    l ∈ formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e ↔
      l ∈ formalLogOnePlusProductArgumentBasicFactorProductChoices q ∧
        formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 =
            q - e (1 : Fin 2) ∧
          formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 =
            q - e (0 : Fin 2) ∧
            formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 =
              e (0 : Fin 2) + e (1 : Fin 2) - q := by
  classical
  simp [formalLogOnePlusProductArgumentBasicFactorLabelCountChoices]


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCoreBase_ExplicitChoiceCounts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

/-- Proves the bound `q ≤ e (0 : Fin 2) + e (1 : Fin 2)`. -/
theorem formalLogOnePlusProductArgument_choiceCounts_q_le_coord_sum
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    q ≤ e (0 : Fin 2) + e (1 : Fin 2) := by
  have hsum :=
    formalLogOnePlusProductArgument_choiceCounts_total_add_mixed_eq_coord_sum
      hl hbasic
  exact Nat.le.intro hsum

/--
Establishes the identity `formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 = q - e (1 :
Fin 2) ∧ formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 = q - e (0 : Fin 2) ∧
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 = e (0 : Fin 2) + e (1 : Fin 2) - q`.
-/
theorem formalLogOnePlusProductArgument_labelCounts_explicit
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 =
          q - e (1 : Fin 2) ∧
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 =
          q - e (0 : Fin 2) ∧
        formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 =
          e (0 : Fin 2) + e (1 : Fin 2) - q := by
  rcases formalLogOnePlusProductArgument_choiceCounts_explicit
      hl hbasic with ⟨hleft, hright, hmixed⟩
  exact
    ⟨by
      rw [← formalLogOnePlusProductArgument_leftChoiceCount_eq_labelCount_zero]
      exact hleft,
    by
      rw [← formalLogOnePlusProductArgument_rightChoiceCount_eq_labelCount_one]
      exact hright,
    by
      rw [←
        formalLogOnePlusProductArgument_mixedChoiceCount_eq_labelCount_two
          hbasic]
      exact hmixed⟩

/-- Every basic-factor choice satisfies the corresponding three label-count constraints. -/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_subset_labelCountChoices
    (q : ℕ) (e : Fin 2 →₀ ℕ) :
    formalLogOnePlusProductArgumentBasicFactorChoices q e ⊆
      formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e := by
  intro l hl
  rw [mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices]
  rw [mem_formalLogOnePlusProductArgumentBasicFactorChoices] at hl
  have hprod :
      l ∈ formalLogOnePlusProductArgumentBasicFactorProductChoices q := by
    rw [mem_formalLogOnePlusProductArgumentBasicFactorProductChoices]
    exact ⟨(Finset.mem_finsuppAntidiag.mp hl.1).2, hl.2⟩
  exact
    ⟨hprod,
      formalLogOnePlusProductArgument_labelCounts_explicit hl.1 hl.2⟩


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCoreBase_ChoicePositions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Realizing formal-product choices by position sets

This module constructs a basic-factor choice from its mixed and left position
sets and proves the resulting position-count formulas.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/--
Characterizes `formalLogOnePlusProductArgumentBasicFactorLabel m = (2 : Fin 3)` by the equivalent
condition `m = formalLogOnePlusProductArgumentBasicFactorMixed`.
-/
theorem formalLogOnePlusProductArgumentBasicFactorLabel_eq_two_iff_of_basic
    {m : Fin 2 →₀ ℕ}
    (hm : formalLogOnePlusProductArgumentBasicFactor m) :
    formalLogOnePlusProductArgumentBasicFactorLabel m = (2 : Fin 3) ↔
      m = formalLogOnePlusProductArgumentBasicFactorMixed := by
  constructor
  · intro h
    rcases hm with hleft | hright | hmixed
    · simp [hleft] at h
    · simp [hright] at h
    · simpa [formalLogOnePlusProductArgumentBasicFactorMixed] using hmixed
  · intro h
    simp [h, formalLogOnePlusProductArgumentBasicFactorMixed]

/-- Positions below `q` at which `l` has the mixed-factor label. -/
noncomputable def formalLogOnePlusProductArgumentMixedPositions
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : Finset ℕ :=
  (Finset.range q).filter fun i =>
    formalLogOnePlusProductArgumentBasicFactorLabel (l i) = (2 : Fin 3)

/-- Positions below `q` at which `l` has the left-factor label. -/
noncomputable def formalLogOnePlusProductArgumentLeftPositions
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : Finset ℕ :=
  (Finset.range q).filter fun i =>
    formalLogOnePlusProductArgumentBasicFactorLabel (l i) = (0 : Fin 3)

/-- Positions below `q` at which `l` has the right-factor label. -/
noncomputable def formalLogOnePlusProductArgumentRightPositions
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) : Finset ℕ :=
  (Finset.range q).filter fun i =>
    formalLogOnePlusProductArgumentBasicFactorLabel (l i) = (1 : Fin 3)

/--
Establishes the identity `(formalLogOnePlusProductArgumentMixedPositions q l).card =
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2`.
-/
theorem formalLogOnePlusProductArgumentMixedPositions_card
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) :
    (formalLogOnePlusProductArgumentMixedPositions q l).card =
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 2 := by
  simp [formalLogOnePlusProductArgumentMixedPositions,
    formalLogOnePlusProductArgumentBasicFactorLabelCount, Finset.sum_boole]

/--
Establishes the identity `(formalLogOnePlusProductArgumentLeftPositions q l).card =
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0`.
-/
theorem formalLogOnePlusProductArgumentLeftPositions_card
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) :
    (formalLogOnePlusProductArgumentLeftPositions q l).card =
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 0 := by
  simp [formalLogOnePlusProductArgumentLeftPositions,
    formalLogOnePlusProductArgumentBasicFactorLabelCount, Finset.sum_boole]

/--
Establishes the identity `(formalLogOnePlusProductArgumentRightPositions q l).card =
formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1`.
-/
theorem formalLogOnePlusProductArgumentRightPositions_card
    (q : ℕ) (l : ℕ →₀ (Fin 2 →₀ ℕ)) :
    (formalLogOnePlusProductArgumentRightPositions q l).card =
      formalLogOnePlusProductArgumentBasicFactorLabelCount q l 1 := by
  simp [formalLogOnePlusProductArgumentRightPositions,
    formalLogOnePlusProductArgumentBasicFactorLabelCount, Finset.sum_boole]

/--
Establishes the identity `formalLogOnePlusProductArgumentMixedPositions q
(formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L) = M`.
-/
theorem formalLogOnePlusProductArgumentMixedPositions_choiceFromMixedLeft
    {q : ℕ} {M L : Finset ℕ} (hM : M ⊆ Finset.range q) :
    formalLogOnePlusProductArgumentMixedPositions q
        (formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L) = M := by
  ext i
  constructor
  · intro hi
    have hq : i ∈ Finset.range q := (Finset.mem_filter.mp hi).1
    have hlabel :
        formalLogOnePlusProductArgumentBasicFactorLabel
            (formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i) =
          (2 : Fin 3) :=
      (Finset.mem_filter.mp hi).2
    by_cases hMi : i ∈ M
    · exact hMi
    · by_cases hLi : i ∈ L
      · simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hq,
          hMi, hLi, formalLogOnePlusProductArgumentBasicFactorLeft] at hlabel
      · simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hq,
          hMi, hLi, formalLogOnePlusProductArgumentBasicFactorRight] at hlabel
  · intro hMi
    have hq : i ∈ Finset.range q := hM hMi
    simp [formalLogOnePlusProductArgumentMixedPositions, hq, hMi,
      formalLogOnePlusProductArgumentBasicFactorMixed]

/--
Establishes the identity `formalLogOnePlusProductArgumentLeftPositions q
(formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L) = L`.
-/
theorem formalLogOnePlusProductArgumentLeftPositions_choiceFromMixedLeft
    {q : ℕ} {M L : Finset ℕ} (hL : L ⊆ Finset.range q \ M) :
    formalLogOnePlusProductArgumentLeftPositions q
        (formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L) = L := by
  ext i
  constructor
  · intro hi
    have hq : i ∈ Finset.range q := (Finset.mem_filter.mp hi).1
    have hlabel :
        formalLogOnePlusProductArgumentBasicFactorLabel
            (formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i) =
          (0 : Fin 3) :=
      (Finset.mem_filter.mp hi).2
    by_cases hMi : i ∈ M
    · simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hq,
        hMi, formalLogOnePlusProductArgumentBasicFactorMixed] at hlabel
    · by_cases hLi : i ∈ L
      · exact hLi
      · simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hq,
          hMi, hLi, formalLogOnePlusProductArgumentBasicFactorRight] at hlabel
  · intro hLi
    have hq : i ∈ Finset.range q := (Finset.mem_sdiff.mp (hL hLi)).1
    have hMi : i ∉ M := (Finset.mem_sdiff.mp (hL hLi)).2
    simp [formalLogOnePlusProductArgumentLeftPositions, hq, hMi, hLi,
      formalLogOnePlusProductArgumentBasicFactorLeft]

/--
Establishes the identity `formalLogOnePlusProductArgumentRightPositions q
(formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L) = Finset.range q \ (M ∪ L)`.
-/
theorem formalLogOnePlusProductArgumentRightPositions_choiceFromMixedLeft
    {q : ℕ} {M L : Finset ℕ} (hL : L ⊆ Finset.range q \ M) :
    formalLogOnePlusProductArgumentRightPositions q
        (formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L) =
      Finset.range q \ (M ∪ L) := by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_sdiff]
    have hq : i ∈ Finset.range q := (Finset.mem_filter.mp hi).1
    have hlabel :
        formalLogOnePlusProductArgumentBasicFactorLabel
            (formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L i) =
          (1 : Fin 3) :=
      (Finset.mem_filter.mp hi).2
    refine ⟨hq, ?_⟩
    rw [Finset.mem_union]
    intro hML
    rcases hML with hMi | hLi
    · simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hq,
        hMi, formalLogOnePlusProductArgumentBasicFactorMixed] at hlabel
    · have hMi : i ∉ M := (Finset.mem_sdiff.mp (hL hLi)).2
      simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hq,
        hMi, hLi, formalLogOnePlusProductArgumentBasicFactorLeft] at hlabel
  · intro hi
    rw [Finset.mem_sdiff] at hi
    rcases hi with ⟨hq, hnot⟩
    have hMi : i ∉ M := by
      intro h
      exact hnot (Finset.mem_union_left L h)
    have hLi : i ∉ L := by
      intro h
      exact hnot (Finset.mem_union_right M h)
    simp [formalLogOnePlusProductArgumentRightPositions, hq, hMi, hLi,
      formalLogOnePlusProductArgumentBasicFactorRight]

/--
Establishes the identity `(formalLogOnePlusProductArgumentRightPositions q
(formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L)).card = q - a`.
-/
theorem formalLogOnePlusProductArgumentRightPositions_choiceFromMixedLeft_card
    {q a b : ℕ} {M L : Finset ℕ}
    (hMsub : M ⊆ Finset.range q) (hMcard : M.card = a + b - q)
    (hLsub : L ⊆ Finset.range q \ M) (hLcard : L.card = q - b)
    (hleft : a ≤ q) (hright : b ≤ q) (hsum : q ≤ a + b) :
    (formalLogOnePlusProductArgumentRightPositions q
      (formalLogOnePlusProductArgumentChoiceFromMixedLeft q M L)).card =
        q - a := by
  rw [formalLogOnePlusProductArgumentRightPositions_choiceFromMixedLeft hLsub]
  have hLrange : L ⊆ Finset.range q := fun i hi =>
    (Finset.mem_sdiff.mp (hLsub hi)).1
  have hdisj : Disjoint M L := by
    rw [Finset.disjoint_left]
    intro i hMi hLi
    exact (Finset.mem_sdiff.mp (hLsub hLi)).2 hMi
  have hunionSub : M ∪ L ⊆ Finset.range q := by
    intro i hi
    rcases Finset.mem_union.mp hi with hMi | hLi
    · exact hMsub hMi
    · exact hLrange hLi
  rw [Finset.card_sdiff_of_subset hunionSub, Finset.card_range]
  rw [Finset.card_union_of_disjoint hdisj, hMcard, hLcard]
  omega


end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalCore
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology

/-!
# Choice-count combinatorics for the formal logarithm product

This module completes the formal logarithm core by identifying the basic-factor
choices with pairs of finite position sets and evaluating their cardinality.
The formal-series identities and the underlying position calculus live in
`FormalCoreBase`.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/--
Establishes the membership statement `(⟨formalLogOnePlusProductArgumentMixedPositions q l,
formalLogOnePlusProductArgumentLeftPositions q l⟩ : Σ _ : Finset ℕ, Finset ℕ) ∈
formalLogOnePlusProductArgumentMixedLeftChoices q (e (0 : Fin 2)) (e (1 : Fin 2))`.
-/
theorem formalLogOnePlusProductArgument_toMixedLeft_mem
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl :
      l ∈ formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e) :
    (⟨formalLogOnePlusProductArgumentMixedPositions q l,
        formalLogOnePlusProductArgumentLeftPositions q l⟩ :
      Σ _ : Finset ℕ, Finset ℕ) ∈
      formalLogOnePlusProductArgumentMixedLeftChoices q
        (e (0 : Fin 2)) (e (1 : Fin 2)) := by
  rw [mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices] at hl
  rcases hl with ⟨_hprod, hlabel0, _hlabel1, hlabel2⟩
  rw [formalLogOnePlusProductArgumentMixedLeftChoices, Finset.mem_sigma]
  constructor
  · rw [Finset.mem_powersetCard]
    exact
      ⟨fun i hi => (Finset.mem_filter.mp hi).1,
        by
          rw [formalLogOnePlusProductArgumentMixedPositions_card, hlabel2]⟩
  · rw [Finset.mem_powersetCard]
    constructor
    · intro i hi
      rw [Finset.mem_sdiff]
      constructor
      · exact (Finset.mem_filter.mp hi).1
      · intro hmix
        have h0 :
            formalLogOnePlusProductArgumentBasicFactorLabel (l i) =
              (0 : Fin 3) :=
          (Finset.mem_filter.mp hi).2
        have h2 :
            formalLogOnePlusProductArgumentBasicFactorLabel (l i) =
              (2 : Fin 3) :=
          (Finset.mem_filter.mp hmix).2
        omega
    · rw [formalLogOnePlusProductArgumentLeftPositions_card, hlabel0]

/--
Establishes the membership statement `formalLogOnePlusProductArgumentChoiceFromMixedLeft q P.1 P.2
∈ formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e`.
-/
theorem formalLogOnePlusProductArgument_fromMixedLeft_mem
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    {P : Σ _ : Finset ℕ, Finset ℕ}
    (hleft : e (0 : Fin 2) ≤ q) (hright : e (1 : Fin 2) ≤ q)
    (hsum : q ≤ e (0 : Fin 2) + e (1 : Fin 2))
    (hP :
      P ∈ formalLogOnePlusProductArgumentMixedLeftChoices q
        (e (0 : Fin 2)) (e (1 : Fin 2))) :
    formalLogOnePlusProductArgumentChoiceFromMixedLeft q P.1 P.2 ∈
      formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e := by
  rw [formalLogOnePlusProductArgumentMixedLeftChoices, Finset.mem_sigma] at hP
  rcases hP with ⟨hMmem, hLmem⟩
  rw [Finset.mem_powersetCard] at hMmem hLmem
  rcases hMmem with ⟨hMsub, hMcard⟩
  rcases hLmem with ⟨hLsub, hLcard⟩
  rw [mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_formalLogOnePlusProductArgumentBasicFactorProductChoices]
    refine ⟨?_, ?_⟩
    · exact Finsupp.support_onFinset_subset
    · intro i hi
      by_cases hMi : i ∈ P.1
      · simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hi,
          hMi, formalLogOnePlusProductArgumentBasicFactorMixed,
          formalLogOnePlusProductArgumentBasicFactor]
      · by_cases hLi : i ∈ P.2
        · simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hi,
            hMi, hLi, formalLogOnePlusProductArgumentBasicFactorLeft,
            formalLogOnePlusProductArgumentBasicFactor]
        · simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hi,
            hMi, hLi, formalLogOnePlusProductArgumentBasicFactorRight,
            formalLogOnePlusProductArgumentBasicFactor]
  · rw [← formalLogOnePlusProductArgumentLeftPositions_card,
      formalLogOnePlusProductArgumentLeftPositions_choiceFromMixedLeft hLsub,
      hLcard]
  · rw [← formalLogOnePlusProductArgumentRightPositions_card]
    exact
      formalLogOnePlusProductArgumentRightPositions_choiceFromMixedLeft_card
        hMsub hMcard hLsub hLcard hleft hright hsum
  · rw [← formalLogOnePlusProductArgumentMixedPositions_card,
      formalLogOnePlusProductArgumentMixedPositions_choiceFromMixedLeft hMsub,
      hMcard]

/--
Establishes the identity `formalLogOnePlusProductArgumentChoiceFromMixedLeft q
(formalLogOnePlusProductArgumentMixedPositions q l) (formalLogOnePlusProductArgumentLeftPositions
q l) = l`.
-/
theorem formalLogOnePlusProductArgument_from_to_choice
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl :
      l ∈ formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e) :
    formalLogOnePlusProductArgumentChoiceFromMixedLeft q
      (formalLogOnePlusProductArgumentMixedPositions q l)
      (formalLogOnePlusProductArgumentLeftPositions q l) = l := by
  rw [mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices] at hl
  rcases hl with ⟨hprod, _h0, _h1, _h2⟩
  rw [mem_formalLogOnePlusProductArgumentBasicFactorProductChoices] at hprod
  rcases hprod with ⟨hsupp, hbasic⟩
  ext i a
  by_cases hi : i ∈ Finset.range q
  · have hb := hbasic i hi
    by_cases h2 :
        formalLogOnePlusProductArgumentBasicFactorLabel (l i) =
          (2 : Fin 3)
    · have hmixed :
          l i = formalLogOnePlusProductArgumentBasicFactorMixed :=
        (formalLogOnePlusProductArgumentBasicFactorLabel_eq_two_iff_of_basic
          hb).1 h2
      simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hi,
        formalLogOnePlusProductArgumentMixedPositions,
        formalLogOnePlusProductArgumentLeftPositions, hi, hmixed,
        formalLogOnePlusProductArgumentBasicFactorMixed]
    · by_cases h0 :
        formalLogOnePlusProductArgumentBasicFactorLabel (l i) =
          (0 : Fin 3)
      · have hleft :
            l i = formalLogOnePlusProductArgumentBasicFactorLeft := by
          simpa [formalLogOnePlusProductArgumentBasicFactorLeft] using
            (formalLogOnePlusProductArgumentBasicFactorLabel_eq_zero.1 h0)
        simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hi,
          formalLogOnePlusProductArgumentMixedPositions,
          formalLogOnePlusProductArgumentLeftPositions, hi, hleft,
          formalLogOnePlusProductArgumentBasicFactorLeft]
      · have h1 :
          formalLogOnePlusProductArgumentBasicFactorLabel (l i) =
            (1 : Fin 3) := by
          generalize hlabel :
            formalLogOnePlusProductArgumentBasicFactorLabel (l i) = j
          fin_cases j
          · exact False.elim (h0 hlabel)
          · rfl
          · exact False.elim (h2 hlabel)
        have hright :
            l i = formalLogOnePlusProductArgumentBasicFactorRight := by
          simpa [formalLogOnePlusProductArgumentBasicFactorRight] using
            (formalLogOnePlusProductArgumentBasicFactorLabel_eq_one.1 h1)
        simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_mem hi,
          formalLogOnePlusProductArgumentMixedPositions,
          formalLogOnePlusProductArgumentLeftPositions, hi, hright,
          formalLogOnePlusProductArgumentBasicFactorRight]
  · have hli : l i = 0 := by
      exact Finsupp.notMem_support_iff.mp (fun hsup => hi (hsupp hsup))
    simp [formalLogOnePlusProductArgumentChoiceFromMixedLeft_apply_of_not_mem hi,
      hli]

/--
Establishes the identity `(⟨formalLogOnePlusProductArgumentMixedPositions q
(formalLogOnePlusProductArgumentChoiceFromMixedLeft q P.1 P.2),
formalLogOnePlusProductArgumentLeftPositions q (formalLogOnePlusProductArgumentChoiceFromMixedLeft
q P.1 P.2)⟩ : Σ _ : Finset ℕ, Finset ℕ) = P`.
-/
theorem formalLogOnePlusProductArgument_to_from_pair
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    {P : Σ _ : Finset ℕ, Finset ℕ}
    (hP :
      P ∈ formalLogOnePlusProductArgumentMixedLeftChoices q
        (e (0 : Fin 2)) (e (1 : Fin 2))) :
    (⟨formalLogOnePlusProductArgumentMixedPositions q
        (formalLogOnePlusProductArgumentChoiceFromMixedLeft q P.1 P.2),
      formalLogOnePlusProductArgumentLeftPositions q
        (formalLogOnePlusProductArgumentChoiceFromMixedLeft q P.1 P.2)⟩ :
      Σ _ : Finset ℕ, Finset ℕ) = P := by
  rw [formalLogOnePlusProductArgumentMixedLeftChoices, Finset.mem_sigma] at hP
  rcases P with ⟨M, L⟩
  rcases hP with ⟨hMmem, hLmem⟩
  rw [Finset.mem_powersetCard] at hMmem hLmem
  rcases hMmem with ⟨hMsub, _hMcard⟩
  rcases hLmem with ⟨hLsub, _hLcard⟩
  simp [formalLogOnePlusProductArgumentMixedPositions_choiceFromMixedLeft hMsub,
    formalLogOnePlusProductArgumentLeftPositions_choiceFromMixedLeft hLsub]

/--
Establishes the identity `(formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e).card =
(formalLogOnePlusProductArgumentMixedLeftChoices q (e (0 : Fin 2)) (e (1 : Fin 2))).card`.
-/
theorem formalLogOnePlusProductArgumentBasicFactorLabelCountChoices_card_eq_mixedLeftChoices_card
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    (hleft : e (0 : Fin 2) ≤ q) (hright : e (1 : Fin 2) ≤ q)
    (hsum : q ≤ e (0 : Fin 2) + e (1 : Fin 2)) :
    (formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e).card =
      (formalLogOnePlusProductArgumentMixedLeftChoices q
        (e (0 : Fin 2)) (e (1 : Fin 2))).card := by
  refine Finset.card_bij'
    (fun l _ =>
      (⟨formalLogOnePlusProductArgumentMixedPositions q l,
        formalLogOnePlusProductArgumentLeftPositions q l⟩ :
        Σ _ : Finset ℕ, Finset ℕ))
    (fun P _ => formalLogOnePlusProductArgumentChoiceFromMixedLeft q P.1 P.2)
    ?_ ?_ ?_ ?_
  · intro l hl
    exact formalLogOnePlusProductArgument_toMixedLeft_mem hl
  · intro P hP
    exact formalLogOnePlusProductArgument_fromMixedLeft_mem
      hleft hright hsum hP
  · intro l hl
    exact formalLogOnePlusProductArgument_from_to_choice hl
  · intro P hP
    exact formalLogOnePlusProductArgument_to_from_pair hP

/-- Under the coordinate bounds, every label-count choice is a valid basic-factor choice. -/
theorem formalLogOnePlusProductArgumentBasicFactorLabelCountChoices_subset_choices
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    (hleft : e (0 : Fin 2) ≤ q) (hright : e (1 : Fin 2) ≤ q)
    (hsum : q ≤ e (0 : Fin 2) + e (1 : Fin 2)) :
    formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e ⊆
      formalLogOnePlusProductArgumentBasicFactorChoices q e := by
  intro l hl
  rw [mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices] at hl
  rw [mem_formalLogOnePlusProductArgumentBasicFactorChoices]
  rcases hl with ⟨hprod, hlabel0, hlabel1, hlabel2⟩
  rw [mem_formalLogOnePlusProductArgumentBasicFactorProductChoices] at hprod
  rcases hprod with ⟨hsupp, hbasic⟩
  refine ⟨?_, hbasic⟩
  rw [Finset.mem_finsuppAntidiag]
  refine ⟨?_, hsupp⟩
  ext j
  fin_cases j
  · rw [Finsupp.finsetSum_apply]
    have hcoord :=
      formalLogOnePlusProductArgument_leftCoord_sum_eq_choiceCounts
        (q := q) (l := l) hbasic
    have hleftCount :
        formalLogOnePlusProductArgumentLeftChoiceCount q l =
          q - e (1 : Fin 2) := by
      rw [formalLogOnePlusProductArgument_leftChoiceCount_eq_labelCount_zero]
      exact hlabel0
    have hmixedCount :
        formalLogOnePlusProductArgumentMixedChoiceCount q l =
          e (0 : Fin 2) + e (1 : Fin 2) - q := by
      rw [formalLogOnePlusProductArgument_mixedChoiceCount_eq_labelCount_two
        hbasic]
      exact hlabel2
    have htarget :
        (∑ i ∈ Finset.range q, (l i) (0 : Fin 2)) =
          e (0 : Fin 2) := by
      rw [hcoord, hleftCount, hmixedCount]
      omega
    simpa using htarget
  · rw [Finsupp.finsetSum_apply]
    have hcoord :=
      formalLogOnePlusProductArgument_rightCoord_sum_eq_choiceCounts
        (q := q) (l := l) hbasic
    have hrightCount :
        formalLogOnePlusProductArgumentRightChoiceCount q l =
          q - e (0 : Fin 2) := by
      rw [formalLogOnePlusProductArgument_rightChoiceCount_eq_labelCount_one]
      exact hlabel1
    have hmixedCount :
        formalLogOnePlusProductArgumentMixedChoiceCount q l =
          e (0 : Fin 2) + e (1 : Fin 2) - q := by
      rw [formalLogOnePlusProductArgument_mixedChoiceCount_eq_labelCount_two
        hbasic]
      exact hlabel2
    have htarget :
        (∑ i ∈ Finset.range q, (l i) (1 : Fin 2)) =
          e (1 : Fin 2) := by
      rw [hcoord, hrightCount, hmixedCount]
      omega
    simpa using htarget

/--
Establishes the identity `(formalLogOnePlusProductArgumentBasicFactorChoices q e).card =
Nat.choose q (e (0 : Fin 2) + e (1 : Fin 2) - q) * Nat.choose (q - (e (0 : Fin 2) + e (1 : Fin 2)
- q)) (q - e (1 : Fin 2))`.
-/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_card_eq_choose_mul_choose
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    (hleft : e (0 : Fin 2) ≤ q) (hright : e (1 : Fin 2) ≤ q)
    (hsum : q ≤ e (0 : Fin 2) + e (1 : Fin 2)) :
    (formalLogOnePlusProductArgumentBasicFactorChoices q e).card =
      Nat.choose q (e (0 : Fin 2) + e (1 : Fin 2) - q) *
        Nat.choose
          (q - (e (0 : Fin 2) + e (1 : Fin 2) - q))
          (q - e (1 : Fin 2)) := by
  have hEq :
      formalLogOnePlusProductArgumentBasicFactorChoices q e =
        formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e := by
    apply Finset.Subset.antisymm
    · exact
        formalLogOnePlusProductArgumentBasicFactorChoices_subset_labelCountChoices
          q e
    · exact
        formalLogOnePlusProductArgumentBasicFactorLabelCountChoices_subset_choices
          hleft hright hsum
  rw [hEq]
  rw [formalLogOnePlusProductArgumentBasicFactorLabelCountChoices_card_eq_mixedLeftChoices_card
    hleft hright hsum]
  rw [formalLogOnePlusProductArgumentMixedLeftChoices_card]

/-- Proves the bound `e (0 : Fin 2) ≤ q`. -/
theorem formalLogOnePlusProductArgument_choiceCounts_left_coord_le_q
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    e (0 : Fin 2) ≤ q := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨hleft, _hright, htotal⟩
  have hq :
      q =
        e (0 : Fin 2) +
          formalLogOnePlusProductArgumentRightChoiceCount q l := by
    calc
      q =
        formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l := htotal.symm
      _ =
        (formalLogOnePlusProductArgumentLeftChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
            formalLogOnePlusProductArgumentRightChoiceCount q l := by
        simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ =
        e (0 : Fin 2) +
          formalLogOnePlusProductArgumentRightChoiceCount q l := by
        rw [hleft]
  exact Nat.le.intro hq.symm

/-- Proves the bound `e (1 : Fin 2) ≤ q`. -/
theorem formalLogOnePlusProductArgument_choiceCounts_right_coord_le_q
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    e (1 : Fin 2) ≤ q := by
  rcases formalLogOnePlusProductArgument_choiceCounts_system
      hl hbasic with ⟨_hleft, hright, htotal⟩
  have hq :
      q =
        e (1 : Fin 2) +
          formalLogOnePlusProductArgumentLeftChoiceCount q l := by
    calc
      q =
        formalLogOnePlusProductArgumentLeftChoiceCount q l +
            formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l := htotal.symm
      _ =
        (formalLogOnePlusProductArgumentRightChoiceCount q l +
          formalLogOnePlusProductArgumentMixedChoiceCount q l) +
            formalLogOnePlusProductArgumentLeftChoiceCount q l := by
        simp only [Nat.add_left_comm, Nat.add_comm]
      _ =
        e (1 : Fin 2) +
          formalLogOnePlusProductArgumentLeftChoiceCount q l := by
        rw [hright]
  exact Nat.le.intro hq.symm

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_FormalProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/-- Proves the bound `e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q ∧ q ≤ e (0 : Fin 2) + e (1 : Fin 2)`. -/
theorem formalLogOnePlusProductArgument_choiceCounts_q_range
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q ∧
      q ≤ e (0 : Fin 2) + e (1 : Fin 2) := by
  exact
    ⟨formalLogOnePlusProductArgument_choiceCounts_left_coord_le_q
        hl hbasic,
      formalLogOnePlusProductArgument_choiceCounts_right_coord_le_q
        hl hbasic,
      formalLogOnePlusProductArgument_choiceCounts_q_le_coord_sum
        hl hbasic⟩

/-- Proves the bound `e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q ∧ q ≤ e (0 : Fin 2) + e (1 : Fin 2)`. -/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_nonempty_q_range
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    (h :
      (formalLogOnePlusProductArgumentBasicFactorChoices q e).Nonempty) :
    e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q ∧
      q ≤ e (0 : Fin 2) + e (1 : Fin 2) := by
  rcases h with ⟨l, hl⟩
  rw [mem_formalLogOnePlusProductArgumentBasicFactorChoices] at hl
  exact formalLogOnePlusProductArgument_choiceCounts_q_range hl.1 hl.2

/--
Establishes the identity `(∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i)
(formalLogOnePlusProductArgument A)) = 1`.
-/
theorem formalLogOnePlusProductArgument_pow_term_prod_eq_one_of_factors_basic
    (A : Type*) [CommRing A] {q : ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hbasic : ∀ i ∈ Finset.range q,
      l i = Finsupp.single (0 : Fin 2) 1 ∨
        l i = Finsupp.single (1 : Fin 2) 1 ∨
          l i =
            Finsupp.single (0 : Fin 2) 1 +
              Finsupp.single (1 : Fin 2) 1) :
    (∏ i ∈ Finset.range q,
      MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A)) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  rcases hbasic i hi with hleft | hrightOrMixed
  · simp [hleft]
  · rcases hrightOrMixed with hright | hmixed
    · simp [hright]
    · simp [hmixed]

/--
Establishes the identity `(∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i)
(formalLogOnePlusProductArgument A)) = 1`.
-/
theorem formalLogOnePlusProductArgument_pow_term_prod_eq_one_of_basicFactor
    (A : Type*) [CommRing A] {q : ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    (∏ i ∈ Finset.range q,
      MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A)) = 1 :=
  formalLogOnePlusProductArgument_pow_term_prod_eq_one_of_factors_basic
    A (fun i hi => by
      simpa [formalLogOnePlusProductArgumentBasicFactor] using hbasic i hi)

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = ∑ l ∈
Finset.finsuppAntidiag (Finset.range q) e, if ∀ i ∈ Finset.range q,
formalLogOnePlusProductArgumentBasicFactor (l i) then (1 : A) else 0`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_sum_basicFactor
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
      ∑ l ∈ Finset.finsuppAntidiag (Finset.range q) e,
        if ∀ i ∈ Finset.range q,
            formalLogOnePlusProductArgumentBasicFactor (l i)
        then (1 : A) else 0 := by
  classical
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hbasic :
      ∀ i ∈ Finset.range q,
        formalLogOnePlusProductArgumentBasicFactor (l i)
  · rw [formalLogOnePlusProductArgument_pow_term_prod_eq_one_of_basicFactor
      A hbasic]
    rw [ite_eq_left hbasic]
  · have hprodZero :
        (∏ i ∈ Finset.range q,
          MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A)) = 0 := by
      by_contra hprodNe
      apply hbasic
      intro i hi
      exact
        formalLogOnePlusProductArgument_coeff_ne_zero_eq_basic A (l i) (by
          intro hzero
          exact hprodNe (Finset.prod_eq_zero hi hzero))
    rw [hprodZero]
    rw [ite_eq_right hbasic]

/--
Establishes the identity `(∑ l ∈ Finset.finsuppAntidiag (Finset.range q) e, if ∀ i ∈ Finset.range
q, formalLogOnePlusProductArgumentBasicFactor (l i) then (1 : A) else 0) =
((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A)`.
-/
theorem formalLogOnePlusProductArgument_basicFactor_sum_eq_card_choices
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ) :
    (∑ l ∈ Finset.finsuppAntidiag (Finset.range q) e,
      if ∀ i ∈ Finset.range q,
          formalLogOnePlusProductArgumentBasicFactor (l i)
      then (1 : A) else 0) =
      ((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A) := by
  classical
  simp [formalLogOnePlusProductArgumentBasicFactorChoices]

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A)`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_card_choices
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
      ((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A) := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_sum_basicFactor,
    formalLogOnePlusProductArgument_basicFactor_sum_eq_card_choices]

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_left_coord_lt
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hleft : q < e (0 : Fin 2)) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0 := by
  classical
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_eq_zero
  intro l hl
  rw [Finset.mem_finsuppAntidiag] at hl
  by_cases hprod :
      ∏ i ∈ Finset.range q,
        MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A) = 0
  · exact hprod
  · exfalso
    have hfactor :
        ∀ i ∈ Finset.range q,
          MvPowerSeries.coeff (l i)
            (formalLogOnePlusProductArgument A) ≠ 0 := by
      intro i hi hzero
      exact hprod (Finset.prod_eq_zero hi hzero)
    have hcoord :
        (∑ i ∈ Finset.range q, l i (0 : Fin 2)) = e (0 : Fin 2) := by
      simpa [Finsupp.finsetSum_apply] using
        congrArg (fun m : Fin 2 →₀ ℕ => m (0 : Fin 2)) hl.1
    have hsum_le :
        (∑ i ∈ Finset.range q, l i (0 : Fin 2)) ≤
          ∑ _i ∈ Finset.range q, 1 := by
      exact Finset.sum_le_sum fun i hi =>
        formalLogOnePlusProductArgument_coeff_ne_zero_left_coord_le_one
          A (l i) (hfactor i hi)
    have hcoord_le : e (0 : Fin 2) ≤ q := by
      simpa [hcoord] using hsum_le
    exact (not_lt_of_ge hcoord_le) hleft

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_right_coord_lt
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hright : q < e (1 : Fin 2)) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0 := by
  classical
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_eq_zero
  intro l hl
  rw [Finset.mem_finsuppAntidiag] at hl
  by_cases hprod :
      ∏ i ∈ Finset.range q,
        MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A) = 0
  · exact hprod
  · exfalso
    have hfactor :
        ∀ i ∈ Finset.range q,
          MvPowerSeries.coeff (l i)
            (formalLogOnePlusProductArgument A) ≠ 0 := by
      intro i hi hzero
      exact hprod (Finset.prod_eq_zero hi hzero)
    have hcoord :
        (∑ i ∈ Finset.range q, l i (1 : Fin 2)) = e (1 : Fin 2) := by
      simpa [Finsupp.finsetSum_apply] using
        congrArg (fun m : Fin 2 →₀ ℕ => m (1 : Fin 2)) hl.1
    have hsum_le :
        (∑ i ∈ Finset.range q, l i (1 : Fin 2)) ≤
          ∑ _i ∈ Finset.range q, 1 := by
      exact Finset.sum_le_sum fun i hi =>
        formalLogOnePlusProductArgument_coeff_ne_zero_right_coord_le_one
          A (l i) (hfactor i hi)
    have hcoord_le : e (1 : Fin 2) ≤ q := by
      simpa [hcoord] using hsum_le
    exact (not_lt_of_ge hcoord_le) hright

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_degree_lt
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hdegree : Finsupp.degree e < q) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0 := by
  have hnil :
      MvPowerSeries.constantCoeff (formalLogOnePlusProductArgument A) ^ 1 =
        0 := by
    simp [formalLogOnePlusProductArgument_constantCoeff A]
  exact
    MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent
      (f := formalLogOnePlusProductArgument A) (m := 1) hnil
      (d := e) (n := q) (by
        have hs : Finsupp.degree e + 1 ≤ q :=
          Nat.succ_le_of_lt hdegree
        simpa [Nat.add_comm] using hs)

/--
Establishes the identity `PowerSeries.coeff q (PowerSeries.log A) •
MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.
-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_degree_lt
    (A : Type*) [CommRing A] [Algebra ℚ A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hdegree : Finsupp.degree e < q) :
    PowerSeries.coeff q (PowerSeries.log A) •
        MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
      0 := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_degree_lt
    A q e hdegree]
  simp

/--
Establishes the identity `PowerSeries.coeff q (PowerSeries.log A) •
MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.
-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_left_coord_lt
    (A : Type*) [CommRing A] [Algebra ℚ A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hleft : q < e (0 : Fin 2)) :
    PowerSeries.coeff q (PowerSeries.log A) •
        MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
      0 := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_left_coord_lt
    A q e hleft]
  simp

/--
Establishes the identity `PowerSeries.coeff q (PowerSeries.log A) •
MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.
-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_right_coord_lt
    (A : Type*) [CommRing A] [Algebra ℚ A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hright : q < e (1 : Fin 2)) :
    PowerSeries.coeff q (PowerSeries.log A) •
        MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
      0 := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_right_coord_lt
    A q e hright]
  simp

/-- Expands a coefficient of the logarithm substituted at the product
argument as a finite sum bounded by the total degree of the exponent. -/
theorem formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      ∑ q ∈ Finset.range (Finsupp.degree e + 1),
        PowerSeries.coeff q (PowerSeries.log A) •
          MvPowerSeries.coeff e
            ((formalLogOnePlusProductArgument A) ^ q) := by
  rw [PowerSeries.coeff_subst
    (formalLogOnePlusProductArgument_hasSubst A) (PowerSeries.log A) e]
  apply finsum_eq_sum_of_support_subset
  intro q hq
  by_contra hmem
  rw [Finset.mem_coe, Finset.mem_range] at hmem
  have hdegree : Finsupp.degree e < q := Nat.lt_of_succ_le
    (Nat.le_of_not_gt hmem)
  exact hq
    (formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_degree_lt
      A q e hdegree)

/-- Refines the coefficient expansion to powers at least as large as both
coordinates of the exponent. -/
theorem formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ_filter_coord_le
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      ∑ q ∈
        (Finset.range (Finsupp.degree e + 1)).filter
          (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
        PowerSeries.coeff q (PowerSeries.log A) •
          MvPowerSeries.coeff e
            ((formalLogOnePlusProductArgument A) ^ q) := by
  rw [formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ]
  exact
    (Finset.sum_subset (Finset.filter_subset _ _) (fun q hq hnot => by
      by_cases hleft : e (0 : Fin 2) ≤ q
      · by_cases hright : e (1 : Fin 2) ≤ q
        · exfalso
          exact hnot (by simpa [hleft, hright] using hq)
        · exact
            formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_right_coord_lt
              A q e (Nat.lt_of_not_ge hright)
      · exact
          formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_left_coord_lt
            A q e (Nat.lt_of_not_ge hleft))).symm

/--
Establishes the divisibility statement `(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
formalLogOnePlusProductArgument A - MvPowerSeries.X (0 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_sub_leftVariable_dvd_rightVariable
    (A : Type*) [CommRing A] :
    (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
      formalLogOnePlusProductArgument A -
        MvPowerSeries.X (0 : Fin 2) := by
  let X0 : MvPowerSeries (Fin 2) A := MvPowerSeries.X (0 : Fin 2)
  let X1 : MvPowerSeries (Fin 2) A := MvPowerSeries.X (1 : Fin 2)
  refine ⟨1 + X0, ?_⟩
  change formalLogOnePlusProductArgument A - X0 = X1 * (1 + X0)
  simp [formalLogOnePlusProductArgument]
  ring

/--
Establishes the divisibility statement `(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
(formalLogOnePlusProductArgument A) ^ d - (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A)
^ d`.
-/
theorem formalLogOnePlusProductArgument_pow_sub_leftVariable_pow_dvd_rightVariable
    (A : Type*) [CommRing A] (d : ℕ) :
    (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
      (formalLogOnePlusProductArgument A) ^ d -
        (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d := by
  exact
    (formalLogOnePlusProductArgument_sub_leftVariable_dvd_rightVariable A).trans
      (sub_dvd_pow_sub_pow
        (formalLogOnePlusProductArgument A)
        (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) d)

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
((formalLogOnePlusProductArgument A) ^ d) = MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d)`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_single_left
    (A : Type*) [CommRing A] (d n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        ((formalLogOnePlusProductArgument A) ^ d) =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d) := by
  have hdiv :=
    formalLogOnePlusProductArgument_pow_sub_leftVariable_pow_dvd_rightVariable
      A d
  have hcoeffSub :
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        ((formalLogOnePlusProductArgument A) ^ d -
          (MvPowerSeries.X (0 : Fin 2) :
            MvPowerSeries (Fin 2) A) ^ d) = 0 := by
    have hvanish :=
      (MvPowerSeries.X_pow_dvd_iff
        (s := (1 : Fin 2)) (n := 1)
        (φ := (formalLogOnePlusProductArgument A) ^ d -
          (MvPowerSeries.X (0 : Fin 2) :
            MvPowerSeries (Fin 2) A) ^ d)).1
        (by simpa using hdiv)
    exact hvanish (Finsupp.single (0 : Fin 2) n) (by
      have h10 : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
      simp [Finsupp.single_eq_of_ne h10])
  rw [map_sub] at hcoeffSub
  exact sub_eq_zero.mp hcoeffSub

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
(PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) = PowerSeries.coeff n
(PowerSeries.log A)`.
-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_single_left
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      PowerSeries.coeff n (PowerSeries.log A) := by
  rw [PowerSeries.coeff_subst
    (formalLogOnePlusProductArgument_hasSubst A) (PowerSeries.log A)
    (Finsupp.single (0 : Fin 2) n)]
  rw [finsum_eq_single _ n]
  · rw [formalLogOnePlusProductArgument_pow_coeff_single_left]
    simp [formalLogOnePlusLeftVariable_pow_coeff]
  · intro d hd
    rw [formalLogOnePlusProductArgument_pow_coeff_single_left]
    rw [formalLogOnePlusLeftVariable_pow_coeff]
    have hsingle :
        Finsupp.single (0 : Fin 2) n ≠ Finsupp.single (0 : Fin 2) d := by
      intro h
      apply hd
      have hcoord := congrArg (fun e : Fin 2 →₀ ℕ => e (0 : Fin 2)) h
      simpa using hcoord.symm
    simp [hsingle]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusRightVariableLogSubst A) = 0`.
-/
theorem formalLogOnePlusRightVariableLogSubst_coeff_of_ne_axis
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : ∀ d : ℕ, e ≠ Finsupp.single (1 : Fin 2) d) :
    MvPowerSeries.coeff e (formalLogOnePlusRightVariableLogSubst A) = 0 := by
  simp [formalLogOnePlusRightVariableLogSubst, PowerSeries.coeff_subst_single, he]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
(formalLogOnePlusProductRightSide A) = PowerSeries.coeff n (PowerSeries.log A)`.
-/
theorem formalLogOnePlusProductRightSide_coeff_single_left
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        (formalLogOnePlusProductRightSide A) =
      PowerSeries.coeff n (PowerSeries.log A) := by
  rw [formalLogOnePlusProductRightSide_coeff,
    formalLogOnePlusLeftVariableLogSubst_coeff_single]
  have hright :
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
          (formalLogOnePlusRightVariableLogSubst A) = 0 := by
    by_cases hn : n = 0
    · subst n
      simpa [Finsupp.single_zero] using
        formalLogOnePlusRightVariableLogSubst_coeff_single A 0
    · exact
        formalLogOnePlusRightVariableLogSubst_coeff_of_ne_axis A
          (Finsupp.single (0 : Fin 2) n)
          (fun d h => by
            apply hn
            have hcoord :=
              congrArg (fun e : Fin 2 →₀ ℕ => e (0 : Fin 2)) h
            simpa using hcoord)
  simp [hright]

/-- Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0`. -/
theorem formalLogOnePlusProductRightSide_coeff_of_ne_axes
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (heLeft : ∀ d : ℕ, e ≠ Finsupp.single (0 : Fin 2) d)
    (heRight : ∀ d : ℕ, e ≠ Finsupp.single (1 : Fin 2) d) :
    MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0 := by
  rw [formalLogOnePlusProductRightSide_coeff]
  simp [formalLogOnePlusLeftVariableLogSubst_coeff_of_ne_axis A e heLeft,
    formalLogOnePlusRightVariableLogSubst_coeff_of_ne_axis A e heRight]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
(PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) = MvPowerSeries.coeff
(Finsupp.single (0 : Fin 2) n) (formalLogOnePlusProductRightSide A)`.
-/
theorem formalLogOnePlusProductFormula_coeff_single_left
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        (formalLogOnePlusProductRightSide A) := by
  rw [formalLogOnePlusProductArgument_logSubst_coeff_single_left,
    formalLogOnePlusProductRightSide_coeff_single_left]

/-- Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0`. -/
theorem formalLogOnePlusProductRightSide_coeff_of_pos_coords
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0 :=
  formalLogOnePlusProductRightSide_coeff_of_ne_axes A e
    (finsupp_fin_two_ne_single_left_of_right_pos e hright)
    (finsupp_fin_two_ne_single_right_of_left_pos e hleft)

/-- On the left coordinate axis, the substituted logarithm and the proposed
right-hand side have the same coefficient. -/
theorem formalLogOnePlusProductFormula_coeff_of_right_coord_zero
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : e (1 : Fin 2) = 0) :
    MvPowerSeries.coeff e
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) := by
  rw [finsupp_fin_two_eq_single_left_of_right_eq_zero e he]
  exact formalLogOnePlusProductFormula_coeff_single_left A (e (0 : Fin 2))

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = 0`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_of_right_coord_zero
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : e (1 : Fin 2) = 0) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) = 0 := by
  simp [formalLogOnePlusProductFormulaDefect,
    formalLogOnePlusProductFormula_coeff_of_right_coord_zero A e he]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = ∑ q ∈
(Finset.range (Finsupp.degree e + 1)).filter (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
PowerSeries.coeff q (PowerSeries.log A) • MvPowerSeries.coeff e
((formalLogOnePlusProductArgument A) ^ q)`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_sum_range_degree_succ_filter_coord_le
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) =
      ∑ q ∈
        (Finset.range (Finsupp.degree e + 1)).filter
          (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
        PowerSeries.coeff q (PowerSeries.log A) •
          MvPowerSeries.coeff e
            ((formalLogOnePlusProductArgument A) ^ q) := by
  simp [formalLogOnePlusProductFormulaDefect,
    formalLogOnePlusProductRightSide_coeff_of_pos_coords A e hleft hright,
    formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ_filter_coord_le]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = ∑ q ∈
(Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 :
Fin 2) ≤ q), PowerSeries.coeff q (PowerSeries.log A) • MvPowerSeries.coeff e
((formalLogOnePlusProductArgument A) ^ q)`.
-/
theorem formalProductDefect_coeff_pos_eq_filtered_sum
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) =
      ∑ q ∈
        (Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter
          (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
        PowerSeries.coeff q (PowerSeries.log A) •
          MvPowerSeries.coeff e
            ((formalLogOnePlusProductArgument A) ^ q) := by
  rw [formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_sum_range_degree_succ_filter_coord_le
    A e hleft hright]
  rw [finsupp_fin_two_degree_eq]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = ∑ q ∈
(Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 :
Fin 2) ≤ q), PowerSeries.coeff q (PowerSeries.log A) • (∑ l ∈ Finset.finsuppAntidiag
(Finset.range q) e, if ∀ i ∈ Finset.range q, formalLogOnePlusProductArgumentBasicFactor (l i) then
(1 : A) else 0)`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_sum_basicFactor
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) =
      ∑ q ∈
        (Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter
          (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
        PowerSeries.coeff q (PowerSeries.log A) •
          (∑ l ∈ Finset.finsuppAntidiag (Finset.range q) e,
            if ∀ i ∈ Finset.range q,
                formalLogOnePlusProductArgumentBasicFactor (l i)
            then (1 : A) else 0) := by
  rw [formalProductDefect_coeff_pos_eq_filtered_sum
    A e hleft hright]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_sum_basicFactor]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = ∑ q ∈
(Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 :
Fin 2) ≤ q), PowerSeries.coeff q (PowerSeries.log A) •
((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A)`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_sum_card_choices
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) =
      ∑ q ∈
        (Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter
          (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
        PowerSeries.coeff q (PowerSeries.log A) •
          ((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A) := by
  rw [formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_sum_basicFactor
    A e hleft hright]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [formalLogOnePlusProductArgument_basicFactor_sum_eq_card_choices]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = 0`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_zero
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) = 0 := by
  rw [formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_sum_card_choices
    A e hleft hright]
  let S :=
    (Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter
      (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q)
  let T : ℕ → ℚ := fun q =>
    (((-1 : ℚ) ^ (q - 1) / (q : ℚ)) *
      ((Nat.choose q (e (0 : Fin 2) + e (1 : Fin 2) - q) *
        Nat.choose
          (q - (e (0 : Fin 2) + e (1 : Fin 2) - q))
          (q - e (1 : Fin 2)) : ℕ) : ℚ))
  change
    (∑ q ∈ S,
      PowerSeries.coeff q (PowerSeries.log A) •
        ((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A)) = 0
  calc
    (∑ q ∈ S,
      PowerSeries.coeff q (PowerSeries.log A) •
        ((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A))
        = ∑ q ∈ S, algebraMap ℚ A (T q) := by
          apply Finset.sum_congr rfl
          intro q hq
          have hqmem := (Finset.mem_filter.mp hq)
          have hqleft : e (0 : Fin 2) ≤ q := hqmem.2.1
          have hqright : e (1 : Fin 2) ≤ q := hqmem.2.2
          have hqsum : q ≤ e (0 : Fin 2) + e (1 : Fin 2) :=
            Nat.lt_succ_iff.mp (Finset.mem_range.mp hqmem.1)
          rw [formalLogOnePlusProductArgumentBasicFactorChoices_card_eq_choose_mul_choose
            hqleft hqright hqsum]
          have hqpos : 0 < q := lt_of_lt_of_le hleft hqleft
          obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
            (Nat.ne_of_gt hqpos)
          simp [T, smul_eq_mul, pow_succ]
    _ = algebraMap ℚ A (∑ q ∈ S, T q) := by
          rw [map_sum]
    _ = 0 := by
          rw [formalLogOnePlusProduct_rational_mixed_sum_eq_zero
            (e (0 : Fin 2)) (e (1 : Fin 2)) hleft hright]
          simp

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = 0`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_eq_zero
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) = 0 := by
  by_cases h0 : e (0 : Fin 2) = 0
  · exact formalLogOnePlusProductFormulaDefect_coeff_of_left_coord_zero
      A e h0
  · by_cases h1 : e (1 : Fin 2) = 0
    · exact formalLogOnePlusProductFormulaDefect_coeff_of_right_coord_zero
        A e h1
    · exact formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_zero
        A e (Nat.pos_of_ne_zero h0) (Nat.pos_of_ne_zero h1)

/-- The formal logarithm product formula
`log ((1 + X) * (1 + Y)) = log (1 + X) + log (1 + Y)`. -/
theorem formalLogOnePlusProductFormula
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A) =
      formalLogOnePlusProductRightSide A := by
  ext e
  have h := formalLogOnePlusProductFormulaDefect_coeff_eq_zero A e
  have hsub :
      MvPowerSeries.coeff e
          (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) -
        MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0 := by
    simpa [formalLogOnePlusProductFormulaDefect] using h
  exact sub_eq_zero.mp hsub

/-- For each fixed degree `q`, the polynomial product argument has the expected
finite monomial evaluation at `(x,y)`.  This is the finite-stage bridge used
before turning the substituted formal logarithm into the field-valued product
logarithm. -/
theorem formalLogOnePlusProductArgument_pow_monomialValue_sum_eq
    (A : Type*) [CommRing A] (x y : A) (q : ℕ) :
    (∑ d ∈ (formalLogOnePlusProductArgumentPolynomial A ^ q).support,
      MvPowerSeries.coeff d ((formalLogOnePlusProductArgument A) ^ q) *
        mvPowerSeriesMonomialValue
          (fun i : Fin 2 => if i = 0 then x else y) d) =
      (x + y + x * y) ^ q := by
  classical
  let P : MvPolynomial (Fin 2) A :=
    formalLogOnePlusProductArgumentPolynomial A
  let a : Fin 2 → A := fun i => if i = 0 then x else y
  have hpow :
      ((P ^ q : MvPolynomial (Fin 2) A) : MvPowerSeries (Fin 2) A) =
        (formalLogOnePlusProductArgument A) ^ q := by
    simp [P, formalLogOnePlusProductArgument_eq_coe_polynomial]
  calc
    (∑ d ∈ (formalLogOnePlusProductArgumentPolynomial A ^ q).support,
      MvPowerSeries.coeff d ((formalLogOnePlusProductArgument A) ^ q) *
        mvPowerSeriesMonomialValue
          (fun i : Fin 2 => if i = 0 then x else y) d)
        =
      ∑ d ∈ (P ^ q).support,
        (P ^ q).coeff d * d.prod (fun i e => a i ^ e) := by
          subst P
          subst a
          apply Finset.sum_congr rfl
          intro d hd
          rw [← hpow, MvPolynomial.coeff_coe]
          simp [mvPowerSeriesMonomialValue]
    _ = MvPolynomial.eval a (P ^ q) := by
          rw [MvPolynomial.eval_eq]
          simp [Finsupp.prod]
    _ = (MvPolynomial.eval a P) ^ q := by
          simp
    _ = (x + y + x * y) ^ q := by
          simp [P, a]

/-- For each fixed degree `q`, the monomial family coming from the `q`-th
power of the product argument is finitely supported and sums to
`(x + y + xy)^q`. -/
theorem hasSum_formalLogOnePlusProductArgument_pow_monomialValue_pair
    (A : Type*) [CommRing A] [TopologicalSpace A] (x y : A) (q : ℕ) :
    HasSum
      (fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d ((formalLogOnePlusProductArgument A) ^ q) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d)
      ((x + y + x * y) ^ q) := by
  classical
  let P : MvPolynomial (Fin 2) A :=
    formalLogOnePlusProductArgumentPolynomial A
  let term : (Fin 2 →₀ ℕ) → A := fun d =>
    MvPowerSeries.coeff d ((formalLogOnePlusProductArgument A) ^ q) *
      mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) d
  have hpow :
      ((P ^ q : MvPolynomial (Fin 2) A) : MvPowerSeries (Fin 2) A) =
        (formalLogOnePlusProductArgument A) ^ q := by
    simp [P, formalLogOnePlusProductArgument_eq_coe_polynomial]
  have hzero :
      ∀ d ∉ (formalLogOnePlusProductArgumentPolynomial A ^ q).support,
        term d = 0 := by
    intro d hd
    have hcoeff_poly :
        (formalLogOnePlusProductArgumentPolynomial A ^ q).coeff d = 0 :=
      by
        by_contra hne
        exact hd (MvPolynomial.mem_support_iff.mpr hne)
    have hcoeff_poly_P : (P ^ q).coeff d = 0 := by
      simpa [P] using hcoeff_poly
    have hcoeff :
        MvPowerSeries.coeff d
            ((formalLogOnePlusProductArgument A) ^ q) = 0 := by
      rw [← hpow]
      rw [MvPolynomial.coeff_coe]
      exact hcoeff_poly_P
    simp [term, hcoeff]
  have hfinite : HasSum term
      (∑ d ∈ (formalLogOnePlusProductArgumentPolynomial A ^ q).support,
        term d) :=
    hasSum_sum_of_ne_finset_zero hzero
  have hsum :
      (∑ d ∈ (formalLogOnePlusProductArgumentPolynomial A ^ q).support,
        term d) =
        (x + y + x * y) ^ q := by
    simpa [term] using
      formalLogOnePlusProductArgument_pow_monomialValue_sum_eq A x y q
  simpa [hsum, term] using hfinite

/-- Fixed-degree product-argument monomial evaluation after multiplying by an
outer logarithm coefficient. -/
theorem hasSum_formalLogOnePlusProductArgument_pow_monomialValue_pair_mul_left
    (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalSemiring A]
    (c x y : A) (q : ℕ) :
    HasSum
      (fun d : Fin 2 →₀ ℕ =>
        c * MvPowerSeries.coeff d ((formalLogOnePlusProductArgument A) ^ q) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d)
      (c * (x + y + x * y) ^ q) := by
  refine
    ((hasSum_formalLogOnePlusProductArgument_pow_monomialValue_pair
      A x y q).mul_left c).congr_fun ?_
  intro d
  ring

/-- Field- or ring-valued monomial-sum form of the formal logarithm product
identity.  Unlike `formalLogOnePlusProductFormula_aeval`, this statement only
uses equality of the coefficient functions and `HasSum` uniqueness, so it does
not require the target ring to carry a linear topology. -/
theorem formalLogOnePlusProductFormula_hasSum_monomialValue_eq
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A] [T2Space A]
    {a : Fin 2 → A} {L R : A}
    (hleft :
      HasSum
        (fun d : Fin 2 →₀ ℕ =>
          MvPowerSeries.coeff d
              (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) *
            mvPowerSeriesMonomialValue a d) L)
    (hright :
      HasSum
        (fun d : Fin 2 →₀ ℕ =>
          MvPowerSeries.coeff d (formalLogOnePlusProductRightSide A) *
            mvPowerSeriesMonomialValue a d) R) :
    L = R := by
  rw [formalLogOnePlusProductFormula A] at hleft
  exact hleft.unique hright

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpSeries_SeriesTerms
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/-- The `n`-th field logarithm-series term is the evaluation of the
`(n+1)`-st coefficient of the formal series `log(1+X)` at `x`. -/
theorem powerSeries_log_coeff_mul_pow_eq_signedLogSeriesTermField
    [Algebra ℚ K] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) :
    PowerSeries.coeff (n + 1) (PowerSeries.log K) *
        x ^ (n + 1) =
      signedLogSeriesTermField x hnK n := by
  have hcoeff :
      algebraMap ℚ K (((-1 : ℚ) ^ n) / (((n + 1 : ℕ) : ℚ))) =
        (-1 : K) ^ n / (((n + 1 : ℕ) : K)) := by
    rw [map_div₀, map_pow, map_neg]
    rw [(algebraMap ℚ K).map_one]
    congr 1
    exact map_natCast (algebraMap ℚ K) (n + 1)
  have hsign : (-1 : ℚ) ^ (n + 1 + 1) = (-1 : ℚ) ^ n := by
    rw [show n + 1 + 1 = n + 2 by omega, pow_add]
    norm_num
  rw [PowerSeries.coeff_log, ite_eq_right (Nat.succ_ne_zero n), hsign, hcoeff]
  simp [signedLogSeriesTermField, logSeriesTermField, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm]

/-! ### Exponential-series terms -/

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Analytic_LogExpAdditivity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology

/-!
# Scaled logarithm additivity for local fields

This file supplies the unconditional summability and regrouping step needed to
evaluate the formal identity
`log ((1 + X) * (1 + Y)) = log (1 + X) + log (1 + Y)` in a complete discretely
valued field whose normalized valuation restricts to `e * v_p` on the natural
numbers.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- If the `d`-coefficient of `(X + Y + XY)^q` is nonzero, then its total
degree is at least `q`. -/
theorem formalLogOnePlusProductArgument_pow_coeff_ne_zero_q_le_coord_sum
    [Algebra ℚ K] (q : ℕ) (d : Fin 2 →₀ ℕ)
    (hcoeff :
      MvPowerSeries.coeff d
          ((formalLogOnePlusProductArgument K) ^ q) ≠ 0) :
    q ≤ d 0 + d 1 := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_card_choices] at hcoeff
  have hcard :
      (formalLogOnePlusProductArgumentBasicFactorChoices q d).card ≠ 0 := by
    intro hzero
    apply hcoeff
    simp [hzero]
  exact
    (formalLogOnePlusProductArgumentBasicFactorChoices_nonempty_q_range
      (Finset.card_ne_zero.mp hcard)).2.2

/-- Each nonzero term in the substituted logarithm Sigma-family is bounded by
the larger of the corresponding one-variable logarithm terms. -/
theorem valuation_formalLogOnePlusProductArgument_sigmaTerm_le_max
    [Algebra ℚ K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} (e : ℕ)
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    {x y : K}
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hvy : v y < (1 : WithZero (Multiplicative ℤ)))
    (q : ℕ) (d : Fin 2 →₀ ℕ) :
    v (PowerSeries.coeff q (PowerSeries.log K) *
        MvPowerSeries.coeff d
          ((formalLogOnePlusProductArgument K) ^ q) *
        mvPowerSeriesMonomialValue
          (fun i : Fin 2 => if i = 0 then x else y) d) ≤
      max
        (v (PowerSeries.coeff q (PowerSeries.log K) * x ^ q))
        (v (PowerSeries.coeff q (PowerSeries.log K) * y ^ q)) := by
  by_cases hc :
      MvPowerSeries.coeff d
          ((formalLogOnePlusProductArgument K) ^ q) = 0
  · simp [hc]
  · have hq : q ≤ d 0 + d 1 :=
      formalLogOnePlusProductArgument_pow_coeff_ne_zero_q_le_coord_sum q d hc
    have hcoeff :
        v (MvPowerSeries.coeff d
            ((formalLogOnePlusProductArgument K) ^ q)) ≤ 1 := by
      rw [formalLogOnePlusProductArgument_pow_coeff_eq_card_choices]
      exact valuation_natCast_le_one_ofWithZeroValuation_scaled v e hnval _
    have hmono :=
      valuation_mvPowerSeriesMonomialValue_pair_le_max_pow
        v hvx hvy q d hq
    rw [v.map_mul, v.map_mul, v.map_mul, v.map_mul, v.map_pow, v.map_pow]
    calc
      v (PowerSeries.coeff q (PowerSeries.log K)) *
          v (MvPowerSeries.coeff d
            ((formalLogOnePlusProductArgument K) ^ q)) *
          v (mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d) ≤
        v (PowerSeries.coeff q (PowerSeries.log K)) * 1 *
          max (v x ^ q) (v y ^ q) := by gcongr
      _ = max
          (v (PowerSeries.coeff q (PowerSeries.log K)) * v x ^ q)
          (v (PowerSeries.coeff q (PowerSeries.log K)) * v y ^ q) := by
        simp [mul_max]

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_WithZeroValuationTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The direct topology of a standard multiplicative integer valuation

This file transfers completeness from the actual-range restriction of a
complete discrete valuation back to the topology obtained directly from
`Valued.mk' v`.
-/

noncomputable section

universe u

open Filter
open scoped Valued
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace WithZeroValuationTopology

variable {K : Type u} [Field K]

/-- The complete-DVF package attached to a standard `ℤᵐ⁰`-valued complete
discrete valuation. -/
def completeDVF
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete v] : CompleteDVF.{u, 0} K where
  ValueGroup := WithZero (Multiplicative ℤ)
  valuation := v
  instCompleteDiscrete := inferInstance

/-- Restricting a standard `ℤᵐ⁰`-valued valuation to its actual range does not
change the uniform structure on the field. -/
theorem valuedMk_uniformSpace_eq_mrangeRestrict
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete v] :
    (Valued.mk' v).toUniformSpace =
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued (completeDVF v)).toUniformSpace := by
  let w :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
      (completeDVF v)
  have hequiv : v.IsEquiv w := by
    intro x y
    rw [← Subtype.coe_le_coe]
    rfl
  change (Valued.mk' v).toUniformSpace = (Valued.mk' w).toUniformSpace
  apply le_antisymm
  · rw [le_iff_uniformContinuous_id]
    simpa using hequiv.symm.uniformContinuous
  · rw [le_iff_uniformContinuous_id]
    simpa using hequiv.uniformContinuous

end WithZeroValuationTopology
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicQp
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Mixed-characteristic input for the `Qp` branch of the local-field structure classification

This file keeps the converse direction of the local-field structure theory, the local-field structure classification focused on the mixed-characteristic case.  The key point proved here is
that the actual range-restricted local-field valuation still restricts on
`ℚ` to the usual `p`-adic valuation, where `p` is the residue characteristic.
-/

noncomputable section

universe u v

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

open scoped WithZero

variable {K : Type u} [Field K]

/-- The actual value group used by the range-restricted topology of a local
field package. -/
abbrev mrangeValueGroup (F : LocalField.{u, v} K) : Type v :=
  MonoidHom.mrange
    F.toCompleteDVF.valuation.toMonoidWithZeroHom

/-- The rational prime subfield of a mixed-characteristic local field. -/
abbrev ratSubfield (_F : LocalField.{u, v} K) [CharZero K] : Subfield K :=
  (algebraMap ℚ K).fieldRange

/-- Establishes the membership statement `(q : K) ∈ F.ratSubfield`. -/
theorem ratCast_mem_ratSubfield
    (F : LocalField.{u, v} K) [CharZero K] (q : ℚ) :
    (q : K) ∈ F.ratSubfield := by
  simp [ratSubfield]

/-- The closed subfield generated by `ℚ` inside a mixed-characteristic local
field, with the range-restricted valuation topology.  This is the candidate
copy of `ℚ_[p]` in the converse direction of the local-field structure classification. -/
noncomputable def qpadicClosureSubfield
    (F : LocalField.{u, v} K) [CharZero K] : Subfield K := by
  letI : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  exact F.ratSubfield.topologicalClosure

/-- Proves the bound `F.ratSubfield ≤ F.qpadicClosureSubfield`. -/
theorem ratSubfield_le_qpadicClosureSubfield
    (F : LocalField.{u, v} K) [CharZero K] :
    F.ratSubfield ≤ F.qpadicClosureSubfield := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  simpa [qpadicClosureSubfield] using
    (Subfield.le_topologicalClosure F.ratSubfield)

/-- Establishes the membership statement `(q : K) ∈ F.qpadicClosureSubfield`. -/
theorem ratCast_mem_qpadicClosureSubfield
    (F : LocalField.{u, v} K) [CharZero K] (q : ℚ) :
    (q : K) ∈ F.qpadicClosureSubfield :=
  F.ratSubfield_le_qpadicClosureSubfield (F.ratCast_mem_ratSubfield q)

/-- The closed subfield generated by the rationals is topologically closed. -/
theorem qpadicClosureSubfield_isClosed
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    IsClosed (F.qpadicClosureSubfield : Set K) := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  simpa [qpadicClosureSubfield] using
    (Subfield.isClosed_topologicalClosure F.ratSubfield)

/-- The rational subfield has dense image in its `p`-adic closure subfield. -/
theorem ratSubfield_denseRange_in_qpadicClosureSubfield
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    DenseRange
      (Set.inclusion
        (show (F.ratSubfield : Set K) ⊆
          (F.qpadicClosureSubfield : Set K) from
          F.ratSubfield_le_qpadicClosureSubfield)) := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  refine (denseRange_inclusion_iff
    (show (F.ratSubfield : Set K) ⊆
      (F.qpadicClosureSubfield : Set K) from
      F.ratSubfield_le_qpadicClosureSubfield)).2 ?_
  intro x hx
  exact hx

/-- The rational embedding, with codomain restricted to the closed `Qp`
candidate inside `K`. -/
noncomputable def ratCastToQpadicClosureSubfield
    (F : LocalField.{u, v} K) [CharZero K] :
    ℚ →+* F.qpadicClosureSubfield :=
  (Rat.castHom K).codRestrict F.qpadicClosureSubfield
    (fun q => F.ratCast_mem_qpadicClosureSubfield q)

/--
The defining evaluation formula for `ratCastToQpadicClosureSubfield` is
`((F.ratCastToQpadicClosureSubfield q : F.qpadicClosureSubfield) : K) = q`.
-/
@[simp]
theorem ratCastToQpadicClosureSubfield_apply
    (F : LocalField.{u, v} K) [CharZero K] (q : ℚ) :
    ((F.ratCastToQpadicClosureSubfield q :
      F.qpadicClosureSubfield) : K) = q :=
  rfl

/-- The rational embedding from the `p`-adically valued rational type synonym
to the closed `Qp` candidate inside `K`. -/
noncomputable def ratCastWithValToQpadicClosureSubfield
    (F : LocalField.{u, v} K) [CharZero K] :
    WithVal (Rat.padicValuation F.residueCharacteristic) →+*
      F.qpadicClosureSubfield :=
  (F.ratCastToQpadicClosureSubfield).comp
    (WithVal.equiv
      (Rat.padicValuation F.residueCharacteristic)).toRingHom

/--
The defining evaluation formula for `ratCastWithValToQpadicClosureSubfield` is
`((F.ratCastWithValToQpadicClosureSubfield q : F.qpadicClosureSubfield) : K) = ((WithVal.equiv
(Rat.padicValuation F.residueCharacteristic) q : ℚ) : K)`.
-/
@[simp]
theorem ratCastWithValToQpadicClosureSubfield_apply
    (F : LocalField.{u, v} K) [CharZero K]
    (q : WithVal (Rat.padicValuation F.residueCharacteristic)) :
    ((F.ratCastWithValToQpadicClosureSubfield q :
      F.qpadicClosureSubfield) : K) =
      ((WithVal.equiv
        (Rat.padicValuation F.residueCharacteristic) q : ℚ) : K) :=
  rfl

/-- The p-adically valued rational embedding has dense range in the closed
`Qp` candidate. -/
theorem ratCastWithValToQpadicClosureSubfield_denseRange
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    DenseRange F.ratCastWithValToQpadicClosureSubfield := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let i : ↥(F.ratSubfield : Set K) → F.qpadicClosureSubfield :=
    Set.inclusion
      (show (F.ratSubfield : Set K) ⊆
        (F.qpadicClosureSubfield : Set K) from
        F.ratSubfield_le_qpadicClosureSubfield)
  let j : WithVal (Rat.padicValuation F.residueCharacteristic) →
      ↥(F.ratSubfield : Set K) :=
    fun q =>
      ⟨((WithVal.equiv
        (Rat.padicValuation F.residueCharacteristic) q : ℚ) : K),
        F.ratCast_mem_ratSubfield
          ((WithVal.equiv
            (Rat.padicValuation F.residueCharacteristic) q : ℚ))⟩
  have hi : DenseRange i := by
    simpa only [i] using
      F.ratSubfield_denseRange_in_qpadicClosureSubfield
  have hj : Function.Surjective j := by
    intro z
    rcases z.2 with ⟨q, hq⟩
    refine ⟨(WithVal.equiv
      (Rat.padicValuation F.residueCharacteristic)).symm q, ?_⟩
    ext
    simpa [j, ratSubfield] using hq
  have hcomp : DenseRange (i ∘ j) :=
    hi.comp hj.denseRange (continuous_inclusion _)
  have hfun : i ∘ j = F.ratCastWithValToQpadicClosureSubfield := by
    funext q
    apply Subtype.ext
    rfl
  rw [hfun] at hcomp
  exact hcomp

/-- The ordinary rational embedding has dense range in the closed `Qp`
candidate. -/
theorem ratCastToQpadicClosureSubfield_denseRange
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    DenseRange F.ratCastToQpadicClosureSubfield := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  apply DenseRange.of_comp
    (g := WithVal.equiv
      (Rat.padicValuation F.residueCharacteristic))
  simpa [Function.comp_def, ratCastWithValToQpadicClosureSubfield]
    using F.ratCastWithValToQpadicClosureSubfield_denseRange

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The integral lattice of a mixed-characteristic local field

This file identifies the integer ring of a mixed-characteristic local field
with the integral closure of the p-adic integers.  In particular it supplies
the finite free `Z_p` lattice of rank `[K : Q_p]` used in the proof of
the mixed-characteristic field-unit structure theorem.  The comparison is made for the canonical copy of `Q_p`
constructed in the local-field structure classification, not for a separately assumed scalar action.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

open scoped WithZero nonZeroDivisors
open Module

variable {K : Type u} [Field K]

/-! ### Canonical mixed-characteristic scalar context -/

/-- The DVR valuation on `Q_p` has closed unit ball equal to the usual
subring `Z_p`. -/
theorem padicDVRValuation_le_one_iff_norm_le_one
    (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    Examples.Qp.padicDVRValuation p x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ :=
      IsDiscreteValuationRing.exists_lift_of_le_one
        (A := ℤ_[p]) (K := ℚ_[p]) hx
    have hzx : (z : ℚ_[p]) = x := by
      simpa using hz
    rw [← hzx]
    exact PadicInt.norm_le_one z
  · intro hx
    let z : ℤ_[p] := ⟨x, hx⟩
    have hz :
        Examples.Qp.padicDVRValuation p (z : ℚ_[p]) ≤ 1 :=
      (Examples.Qp.padicIntEquivValuationSubring p z).property
    simpa [z] using hz

/-! ### the canonical `Z_p` integral basis -/

/-! ### The canonical `Z_p` action on `U^r` -/

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_GroupTheory_PowerIndex
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valueModResidueDegreeHom_apply _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Power indices in commutative groups

Reusable kernel, quotient, product, and additive-transport formulas for
`n`-th powers in commutative groups.  The basic power map and its image and
kernel are mathlib's `powMonoidHom`, `MonoidHom.range`, and `MonoidHom.ker`.
-/

noncomputable section

namespace LocalFieldTheory

open LocalFieldTheory.DiscreteValuationField
open scoped Int

section NthPowers

universe uG uH uU

variable (G : Type uG) (H : Type uH) (U : Type uU)
variable [CommGroup G] [CommGroup H] [CommGroup U]


/-- For multiplicative integers, the range of the `n`-th power map is the subgroup of additive
multiples of `n`. -/
theorem powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup
    (n : ℕ) :
    (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range =
      integerMultipleSubgroup (n : ℤ) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    rw [mem_integerMultipleSubgroup_iff, powMonoidHom_apply, Int.toAdd_pow]
    exact ⟨y.toAdd, by ring⟩
  · intro hx
    rw [mem_integerMultipleSubgroup_iff] at hx
    rcases hx with ⟨k, hk⟩
    rw [MonoidHom.mem_range]
    refine ⟨Multiplicative.ofAdd k, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [powMonoidHom_apply, Int.toAdd_pow, toAdd_ofAdd, hk]
    ring

/-- For nonzero `n`, multiplicative integers modulo `n`-th powers form a finite quotient. -/
theorem finite_multiplicativeInt_nthPowerQuotient
    {n : ℕ} (hn : n ≠ 0) :
    Finite (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) := by
  rw [powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup]
  have hnabs : (n : ℤ).natAbs ≠ 0 := by simpa using hn
  let : NeZero (n : ℤ).natAbs := ⟨hnabs⟩
  exact Finite.of_equiv
    (Multiplicative (ZMod (n : ℤ).natAbs))
    (valueModIntegerMultipleSubgroupEquivZMod (n : ℤ)).symm.toEquiv

/-- For nonzero `n`, the multiplicative-integer power quotient has cardinality `n`. -/
theorem card_multiplicativeInt_nthPowerQuotient
    {n : ℕ} (hn : n ≠ 0)
    [Finite (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range)] :
    Nat.card
        (Multiplicative ℤ ⧸ (powMonoidHom n : (Multiplicative ℤ) →* (Multiplicative ℤ)).range) = n := by
  rw [Nat.card_congr
    ((QuotientGroup.quotientMulEquivOfEq
      (powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup n)).trans
        (valueModIntegerMultipleSubgroupEquivZMod (n : ℤ))).toEquiv]
  rw [Nat.card_congr
    (Multiplicative.toAdd :
      Multiplicative (ZMod ((n : ℤ).natAbs)) ≃ ZMod ((n : ℤ).natAbs))]
  have hnabs : (n : ℤ).natAbs ≠ 0 := by simpa using hn
  let : NeZero (n : ℤ).natAbs := ⟨hnabs⟩
  have hcard : Nat.card (ZMod ((n : ℤ).natAbs)) = (n : ℤ).natAbs :=
    Nat.card_zmod ((n : ℤ).natAbs)
  simp at hcard ⊢

end NthPowers

end LocalFieldTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Padic_NonarchimedeanLocalField
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/-- The canonical multiplicative valuation of `ℚ_p` is at most one exactly
when the p-adic norm is at most one. -/
theorem mulValuation_le_one_iff_norm_le_one
    (x : ℚ_[p]) :
    Padic.mulValuation (p := p) x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  · rw [Padic.norm_le_one_iff_val_nonneg]
    change (if x = 0 then 0 else WithZero.exp (-x.valuation)) ≤ 1 ↔
      0 ≤ x.valuation
    rw [ite_eq_right hx, ← WithZero.exp_zero, WithZero.exp_le_exp, neg_nonpos]

/-- The integer ring defined by the canonical valuative relation on `ℚ_p`
consists exactly of the elements of norm at most one. -/
theorem integer_mem_iff_norm_le_one (x : ℚ_[p]) :
    x ∈ (ValuativeRel.valuation ℚ_[p]).integer ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff,
    ← Valuation.vle_one_iff (ValuativeRel.valuation ℚ_[p]),
    Valuation.vle_one_iff (Padic.mulValuation (p := p)),
    mulValuation_le_one_iff_norm_le_one]

end LocalFieldTheory.Padic
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Padic_PrincipalUnits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Principal units of the p-adic field

This file identifies the standard p-adic integer and complete-DVF models,
computes their principal-unit quotients, and records the logarithm/exponential
power formulas used by local cyclotomic norm calculations.
-/

noncomputable section

open scoped ValuativeRel WithZero

namespace LocalFieldTheory.Padic

open LocalFieldTheory
open ValuationTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (p : ℕ) [Fact p.Prime]

/-- The valuative integer ring of `ℚ_p` is canonically equivalent to
`ℤ_p`. -/
noncomputable def integerRingEquivPadicInt :
    𝒪[ℚ_[p]] ≃+* ℤ_[p] where
  toFun x := ⟨x, (integer_mem_iff_norm_le_one p x).1 x.property⟩
  invFun x := ⟨x, (integer_mem_iff_norm_le_one p x).2 x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- The equivalence with `ℤ_p` preserves the underlying element of `ℚ_p`. -/
@[simp] theorem integerRingEquivPadicInt_coe (x : 𝒪[ℚ_[p]]) :
    ((integerRingEquivPadicInt p x : ℤ_[p]) : ℚ_[p]) = (x : ℚ_[p]) := rfl

end LocalFieldTheory.Padic

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_LocalResidueArithmetic
attribute [-instance] _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Residue arithmetic for finite-place power indices

This file relates global ideal norms to the residue fields and ramification
invariants of the corresponding finite completions.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]


/-- The ideal norm is the cardinality of the residue field of the
corresponding adic completion. -/
theorem absNorm_eq_card_adicResidueField
    (v : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm v.asIdeal =
      Nat.card
        (Valued.ResidueField (v.adicCompletion K)) := by
  rw [Ideal.absNorm_apply]
  exact
    Nat.card_congr
      (ringOfIntegersQuotientEquivAdicResidueField
        v).toEquiv


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_CyclotomicPrimeBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- The tensor-product compositum of `L` and the prime cyclotomic
base field.  Its field structure is constructed below from coprime
degrees. -/
abbrev PrimeCyclotomicPushout (p : ℕ) :=
  PrimeCyclotomicBase K p ⊗[K] L

end KummerTheory
end
end


