-- Prove2me | Definitions.Def_OAIQ244Duke043
-- name    : OAIQ244Duke043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:39:52.18432+00:00
-- url     : https://prove2.me/theorems/120f8598-f33b-45e6-8a6f-11023fd3f6bd
-- title:
--   Definitions bundle OAIQ244Duke043 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 134 declarations of OpenAI's Lean: 35 definitions, 1 instance and 98 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLevel`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicChosenFinitePlaceExtension`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletion`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedPrimitiveRoot`, `LocalClassFieldTheory.A`, `LubinTate.SameUniformizer.approximation`, `LubinTate.SameUniformizer.correctDegree`, `LubinTate.SameUniformizer.correctList`, `LubinTate.SameUniformizer.correctedIntertwiner`, `LubinTate.SameUniformizer.correctionCoefficient`, `LubinTate.SameUniformizer.correctionStep`, `LubinTate.SameUniformizer.intertwinerApproximation`, `LubinTate.SameUniformizer.monomialCorrection`, `LubinTate.SameUniformizer.normalizedDefectCoefficient`, `LubinTate.SameUniformizer.recursiveIntertwiner`, `LubinTate.SameUniformizer.standardLubinTateEndomorphism`, `LubinTate.SameUniformizer.standardSeries`, `LubinTate.SameUniformizer.standardSeries'`, `LubinTate.chosenStandardLubinTatePrimitiveRoot`, `LubinTate.standardLubinTateBaseUniformizerUnit`, `LubinTate.standardLubinTateChangedUniformizer`, `LubinTate.standardLubinTateChangedUniformizerUnit`, `LubinTate.standardLubinTateLevelCompleteDVF`, `LubinTate.standardLubinTateLevelField`, `LubinTate.standardLubinTateLevelGenerator`, `LubinTate.standardLubinTateLevelPowerBasis`, `LubinTate.standardLubinTatePolynomial`, `LubinTate.standardLubinTatePolynomialIterate`, `LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure`, `LubinTate.standardLubinTatePrimitivePointInteger`, `LubinTate.standardLubinTatePrimitivePolynomial`, `LubinTate.standardLubinTatePrimitivePolynomialOverField`, `LubinTate.standardLubinTateSeries`, `LubinTate.standardLubinTateUnitFactorFieldUnit`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Adele_InfinitePlaceTensorBlock`, `AlgebraicNumberTheory_RayClass_Topology`, `GlobalClassFieldTheory_Reciprocity_CyclotomicTorsionFixedField`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicLocalization`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormalization`, `LubinTate_FiniteLevel_ChangedUniformizer`, `LubinTate_FiniteLevel_DivisionPolynomial`, `LubinTate_FiniteLevel_NormSubgroup`, `LubinTate_FiniteLevel_NormUniformizer`, `LubinTate_FiniteLevel_PrimitiveEisenstein`, `LubinTate_FiniteLevel_PrimitiveRoot`, `LubinTate_FiniteLevel_PrimitiveTorsion`, `LubinTate_FiniteLevel_PrimitiveUniformizer`, `LubinTate_FormalModule_CoefficientEquation`, `LubinTate_FormalModule_DegreeStabilization`, `LubinTate_FormalModule_RecursiveCoefficient`, `LubinTate_FormalModule_RecursiveCorrection`, `LubinTate_FormalModule_RecursiveIntertwiner`, `LubinTate_FormalModule_Reduction`, `LubinTate_FormalModule_StandardFormalGroup`, `LubinTate_FormalModule_StandardSeries`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke025`, `OAIQ244Duke028`, `OAIQ244Duke029`, `OAIQ244Duke030` and `OAIQ244Duke033` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke047`, `OAIQ244Duke049`, `OAIQ244Duke050`, `OAIQ244Duke051` and `OAIQ244Duke052`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
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
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
import Definitions.Def_OAIQ244Duke025
import Definitions.Def_OAIQ244Duke028
import Definitions.Def_OAIQ244Duke029
import Definitions.Def_OAIQ244Duke030
import Definitions.Def_OAIQ244Duke033

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_InfinitePlaceTensorBlock
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.decompositionField_decompositionField_integerMap_isLocalHom _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.HilbertRamification.decompositionField_decompositionField_integerMap_apply _root_.HilbertRamification.decompositionField_decompositionField_residueFieldEquiv_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
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

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open HilbertRamification

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [NumberField L] in
/-- The canonical comparisons from concrete infinite-place completions to
absolute-value completions commute with the completion maps in a tower of
number fields. -/
theorem infinitePlaceCompletionAlgEquiv_algebraMap
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v) :
    letI : w.1.LiesOver v.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
    let u : AbsoluteValueExtension v.1 L :=
      ⟨w.1, fun x =>
        congrArg (fun q : InfinitePlace K => q.1 x) hw⟩
    letI : Algebra v.1.Completion u.1.Completion :=
      AbsoluteValue.completionAlgebra v.1 u.1 u.2
    RingHom.comp
        (algebraMap v.1.Completion u.1.Completion)
        (infinitePlaceCompletionAlgEquiv v).toRingEquiv =
      RingHom.comp
        (infinitePlaceCompletionAlgEquiv w).toRingEquiv
        (algebraMap v.Completion w.Completion) := by
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  let u : AbsoluteValueExtension v.1 L :=
    ⟨w.1, fun x =>
      congrArg (fun q : InfinitePlace K => q.1 x) hw⟩
  let : Algebra v.1.Completion u.1.Completion :=
    AbsoluteValue.completionAlgebra v.1 u.1 u.2
  ext x
  refine InfinitePlace.Completion.induction_on v x ?_ ?_
  · exact
      isClosed_eq
        ((AbsoluteValue.completionMap_isometry
            v.1 w.1 u.2).continuous.comp
          (InfinitePlace.Completion.continuous_toCompletion v))
        ((InfinitePlace.Completion.continuous_toCompletion w).comp
          NumberField.LiesOver.continuous_completionMap)
  · intro y
    have hy :
        (y : v.1.Completion) =
          algebraMap K v.1.Completion
            (WithAbs.equiv v.1 y) := by
      rw [← AbsoluteValue.toCompletion_eq_algebraMap]
      simp
    change
      AbsoluteValue.completionMap v.1 u.1 u.2
          (y : v.1.Completion) =
        (NumberField.LiesOver.completionMap
          (v := v) (w := w)
          (y : v.Completion)).toCompletion
    rw [NumberField.LiesOver.completionMap_coe]
    rw [hy, AbsoluteValue.completionMap_coe]
    rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Topology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

/-- Membership in the `n`-th local higher-unit group bounds the norm of
the difference from one by the `n`-th power of a uniformizer norm. -/
theorem localHigherUnit_norm_sub_one_le
    (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (n : ℕ) {x : (v.adicCompletion K)ˣ}
    (hx : x ∈ localHigherUnitGroup v n) :
    ‖(x : v.adicCompletion K) - 1‖ ≤ ‖ϖ‖ ^ n := by
  obtain ⟨y, rfl, hy⟩ :=
    (mem_localHigherUnitGroup_iff v n x).1 hx
  have hyIdeal :
      localIntegralValue v y - 1 ∈
        (IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ n :=
    (localHigherUnitMap_eq_one_iff v n y).1 hy
  have hIdealSet :=
    Valuation.Integers.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
        K v) hϖ n
  have hyVal :
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
          (algebraMap (v.adicCompletionIntegers K)
            (v.adicCompletion K) (localIntegralValue v y - 1)) ≤
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
            (algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K) ϖ) ^ n := by
    exact (Set.ext_iff.mp hIdealSet
      (localIntegralValue v y - 1)).mp hyIdeal
  have hcoe :
      (((y : (v.adicCompletionIntegers K).units) :
          (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        ((localIntegralValue v y :
          v.adicCompletionIntegers K) : v.adicCompletion K) :=
    rfl
  rw [hcoe]
  change
    ‖((localIntegralValue v y :
        v.adicCompletionIntegers K) : v.adicCompletion K) - 1‖ ≤
      ‖((ϖ : v.adicCompletionIntegers K) :
        v.adicCompletion K)‖ ^ n
  rw [← norm_pow]
  apply Valued.toNormedField.norm_le_iff.mpr
  have hyVal' :
      @LE.le ℤᵐ⁰ WithZero.instPreorder.toLE
        ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
          (((localIntegralValue v y :
            v.adicCompletionIntegers K) :
              v.adicCompletion K) - 1))
        ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
          (((ϖ : v.adicCompletionIntegers K) :
            v.adicCompletion K) ^ n)) := by
    have hAlgebraMap :
        ∀ z : v.adicCompletionIntegers K,
          algebraMap (v.adicCompletionIntegers K)
              (v.adicCompletion K) z =
            (z : v.adicCompletion K) :=
      fun _ ↦ rfl
    simpa [hAlgebraMap] using hyVal
  have withZeroPreorder_le :
      ∀ a b : ℤᵐ⁰,
        @LE.le ℤᵐ⁰ WithZero.instPreorder.toLE a b →
          a ≤ b := by
    intro a b hab
    cases a <;> cases b <;>
      simp_all
  exact withZeroPreorder_le _ _ hyVal'

/-- The higher-unit groups form a neighborhood basis of `1` in a finite
local multiplicative group. -/
theorem exists_localHigherUnitGroup_subset
    (v : HeightOneSpectrum (𝓞 K))
    {U : Set (v.adicCompletion K)ˣ}
    (hU : U ∈ 𝓝 (1 : (v.adicCompletion K)ˣ)) :
    ∃ n : ℕ,
      (localHigherUnitGroup v n :
        Set (v.adicCompletion K)ˣ) ⊆ U := by
  have hU' :
      U ∈ Filter.comap
        (Units.val : (v.adicCompletion K)ˣ →
          v.adicCompletion K)
        (𝓝 (1 : v.adicCompletion K)) := by
    have heq :
        𝓝 (1 : (v.adicCompletion K)ˣ) =
          Filter.comap
            (Units.val : (v.adicCompletion K)ˣ →
              v.adicCompletion K)
            (𝓝 (1 : v.adicCompletion K)) := by
      simpa using
        Units.isEmbedding_val₀.nhds_eq_comap
          (1 : (v.adicCompletion K)ˣ)
    rw [← heq]
    exact hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU'
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible
      (v.adicCompletionIntegers K)
  have hϖlt : ‖ϖ‖ < 1 :=
    local_irreducible_norm_lt_one v hϖ
  obtain ⟨n, hn⟩ :
      ∃ n : ℕ, ‖ϖ‖ ^ n < ε :=
    exists_pow_lt_of_lt_one hε hϖlt
  refine ⟨n, ?_⟩
  intro x hx
  apply hVU
  apply hball
  change dist
      (((x : (v.adicCompletion K)ˣ) :
        v.adicCompletion K))
      1 < ε
  rw [dist_eq_norm]
  exact (localHigherUnit_norm_sub_one_le v ϖ hϖ n hx).trans_lt hn

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicTorsionFixedField
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.closedFixingSubgroup_normal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The cyclotomic torsion fixed field

`rationalCyclotomicField` now denotes the actual field `ℚ(μ∞)` inside
`SeparableClosure ℚ`.  Its actual Galois group is therefore the standard
mathlib type
`rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField`; its finite
cyclotomic levels form a divisibility-directed system with supremum the
whole field.  The torsion fixed field is the actual
intermediate field `rationalCyclotomicTorsionFixedField`.

The actual continuous cyclotomic character identifies the full Galois
group with `ℤ̂ˣ`.  Applying infinite Galois correspondence to the actual
torsion closure and the group-theoretic decomposition of `ℤ̂ˣ` gives the
cyclotomic `ℤ̂`-extension.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped IsMulCommutative
open KummerTheory
open ClassFormation

theorem rationalCyclotomicTorsionRestrictionEquiv_apply_mk
    (σ :
      rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField) :
    rationalCyclotomicTorsionRestrictionEquiv
        (QuotientGroup.mk σ) =
      AlgEquiv.restrictNormalHom
        rationalCyclotomicTorsionFixedField σ := by
  exact
    InfiniteGalois.normalAutEquivQuotient_apply
      rationalCyclotomicTorsionClosure σ

theorem rationalCyclotomicTorsionRestrictionEquiv_symm_restrictNormal
    (σ :
      rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField) :
    rationalCyclotomicTorsionRestrictionEquiv.symm
        (AlgEquiv.restrictNormalHom
          rationalCyclotomicTorsionFixedField σ) =
      QuotientGroup.mk σ := by
  apply rationalCyclotomicTorsionRestrictionEquiv.symm_apply_eq.mpr
  exact (rationalCyclotomicTorsionRestrictionEquiv_apply_mk σ).symm

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicLocalization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.rationalCyclotomicCharacterPrimeProduct_apply _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.completionProductUnitsEquivRightCosets_apply_coe _root_.LocalClassFieldTheory.conjugateExtensionCompletionRingEquiv_toCompletion _root_.LocalClassFieldTheory.localTensorEvaluation_tmul _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalClassFieldTheory.rightCosetCompletionUnitsEquiv_apply_coe _root_.LocalClassFieldTheory.rightCosetExtensionEquiv_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.infinitePlace_mult_smul _root_.restrictAbsoluteValueExtensionToIntermediate_apply
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

/-- The chosen extension of the rational finite-place absolute value to
the actual `m`-th cyclotomic level. -/
noncomputable def rationalCyclotomicChosenFinitePlaceExtension
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    AbsoluteValueExtension
      (rationalCyclotomicAdicAbsoluteValue v)
      (KummerTheory.rationalCyclotomicLevel m) :=
  chosenFinitePlaceExtension
    (L := KummerTheory.rationalCyclotomicLevel m) v

/-- The canonical algebra structure on the selected extension completion
over the rational finite completion. -/
noncomputable instance rationalCyclotomicCompletionAlgebra
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra (rationalCyclotomicAdicAbsoluteValue v).Completion
      (rationalCyclotomicChosenFinitePlaceExtension m v).1.Completion :=
  AbsoluteValue.completionAlgebra
    (rationalCyclotomicAdicAbsoluteValue v)
    (rationalCyclotomicChosenFinitePlaceExtension m v).1
    (rationalCyclotomicChosenFinitePlaceExtension m v).2

/-- The actual algebraic localization of the rational cyclotomic level at `v`. -/
abbrev rationalCyclotomicLocalizedCompletion
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :=
  LocalizedCompletion
    (rationalCyclotomicAdicAbsoluteValue v)
    (rationalCyclotomicChosenFinitePlaceExtension m v)

section RationalGlobalToLocalized

theorem rationalCyclotomicLocalizedCompletion_charZero
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    CharZero (rationalCyclotomicLocalizedCompletion m v) :=
  charZero_of_injective_ringHom
    ((AbsoluteValue.toAlgebraicLocalization
      (rationalCyclotomicAdicAbsoluteValue v)
      (rationalCyclotomicChosenFinitePlaceExtension m v).1
      (rationalCyclotomicChosenFinitePlaceExtension m v).2).comp
      (algebraMap ℚ (KummerTheory.rationalCyclotomicLevel m))).injective

attribute [local instance] rationalCyclotomicLocalizedCompletion_charZero

/-- The actual global-to-local embedding of the selected rational
cyclotomic level, regarded as a rational algebra homomorphism. -/
noncomputable def rationalCyclotomicGlobalToLocalizedAlgHom
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    KummerTheory.rationalCyclotomicLevel m →ₐ[ℚ]
      rationalCyclotomicLocalizedCompletion m v :=
  (AbsoluteValue.toAlgebraicLocalization
    (rationalCyclotomicAdicAbsoluteValue v)
    (rationalCyclotomicChosenFinitePlaceExtension m v).1
    (rationalCyclotomicChosenFinitePlaceExtension m v).2).toRatAlgHom

/-- The named rational algebra homomorphism has the canonical
global-to-local ring homomorphism as its underlying map. -/
@[simp]
theorem rationalCyclotomicGlobalToLocalizedAlgHom_apply
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ))
    (x : KummerTheory.rationalCyclotomicLevel m) :
    rationalCyclotomicGlobalToLocalizedAlgHom m v x =
      AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicAdicAbsoluteValue v)
        (rationalCyclotomicChosenFinitePlaceExtension m v).1
        (rationalCyclotomicChosenFinitePlaceExtension m v).2 x :=
  rfl

/-- The image of the selected global primitive root in the algebraic
localization at `v`. -/
noncomputable def rationalCyclotomicLocalizedPrimitiveRoot
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    rationalCyclotomicLocalizedCompletion m v :=
  AbsoluteValue.toAlgebraicLocalization
    (rationalCyclotomicAdicAbsoluteValue v)
    (rationalCyclotomicChosenFinitePlaceExtension m v).1
    (rationalCyclotomicChosenFinitePlaceExtension m v).2
    (rationalCyclotomicLevelPrimitiveRoot m)

/-- The selected localized root is the actual global-to-local image of
the selected global primitive root. -/
@[simp]
theorem rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ)) :
    rationalCyclotomicGlobalToLocalizedAlgHom m v
        (rationalCyclotomicLevelPrimitiveRoot m) =
      rationalCyclotomicLocalizedPrimitiveRoot m v :=
  rfl

end RationalGlobalToLocalized

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_CoefficientEquation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- A chosen uniformizer reduces to zero in the residue field. -/
theorem residueMap_uniformizer_eq_zero
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    F.residueMap π = 0 :=
  (F.toCompleteDVF.residue_eq_zero_iff π).2
    (F.toCompleteDVF.uniformizer_mem_maximalIdeal hπ)

/-- An element reducing to zero is divisible by the chosen uniformizer. -/
theorem uniformizer_dvd_of_residueMap_eq_zero
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {a : F.valuationSubring} (ha : F.residueMap a = 0) :
    π ∣ a := by
  have hmem : a ∈ F.maximalIdeal :=
    (F.toCompleteDVF.residue_eq_zero_iff a).1 ha
  have hspan :
      a ∈ Ideal.span ({π} : Set F.valuationSubring) := by
    simpa [F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ] using hmem
  exact Ideal.mem_span_singleton.mp hspan

/-- Every positive power of a uniformizer reduces to zero. -/
theorem residueMap_uniformizer_pow_eq_zero
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {r : ℕ} (hr : r ≠ 0) :
    F.residueMap (π ^ r) = 0 := by
  simp [map_pow, residueMap_uniformizer_eq_zero hπ, hr]

/-- For positive `r`, the factor `1 - pi ^ r` is a unit of `O_K`. -/
theorem isUnit_one_sub_uniformizer_pow
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {r : ℕ} (hr : r ≠ 0) :
    IsUnit (1 - π ^ r) := by
  apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
  intro hunit
  have hresidue_ne : F.residueMap (π ^ r) ≠ 0 :=
    (F.toCompleteDVF.residue_ne_zero_iff_isUnit (π ^ r)).2 hunit
  exact hresidue_ne (residueMap_uniformizer_pow_eq_zero hπ hr)

/-- The scalar coefficient equation in positive total degree has a
unique solution in the valuation ring. -/
theorem existsUnique_one_sub_uniformizer_pow_mul_eq
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {r : ℕ} (hr : r ≠ 0) (b : F.valuationSubring) :
    ∃! x : F.valuationSubring, (1 - π ^ r) * x = b :=
  existsUnique_mul_eq_of_isUnit
    (isUnit_one_sub_uniformizer_pow hπ hr) b

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_StandardSeries
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The standard Lubin--Tate series

For a uniformizer `π`, the polynomial power series

`π X + X ^ q`,

where `q` is the cardinality of the residue field, is a Lubin--Tate
series.  This gives the general formal-module construction a canonical
polynomial input without making an equal-characteristic assumption.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- A uniformizer makes `π X + X ^ q` into a Lubin--Tate series. -/
noncomputable def standardLubinTateSeries
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    LubinTateSeries F π where
  toPowerSeries := standardLubinTatePowerSeries F π
  constantCoeff_eq_zero := by
    have hq0 : Nat.card F.residueField ≠ 0 :=
      Nat.ne_of_gt (lt_trans Nat.zero_lt_one
        (Finite.one_lt_card (α := F.residueField)))
    simp [standardLubinTatePowerSeries, hq0]
  coeff_one_eq_uniformizer := by
    have hq : 1 ≠ Nat.card F.residueField :=
      (Finite.one_lt_card (α := F.residueField)).ne
    simp [standardLubinTatePowerSeries, PowerSeries.coeff_X_pow, hq]
  map_residue_eq_frobenius := by
    simp [standardLubinTatePowerSeries,
      SameUniformizer.residueMap_uniformizer_eq_zero hπ]

namespace LubinTateSeries

/-- The underlying series of the standard Lubin--Tate input is literally
`π X + X ^ q`. -/
@[simp]
theorem standardLubinTateSeries_toPowerSeries
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    (standardLubinTateSeries hπ).toPowerSeries =
      standardLubinTatePowerSeries F π :=
  rfl

end LubinTateSeries
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_DivisionPolynomial
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Standard Lubin--Tate division polynomials

For a local field `F` and an element `π` of its valuation ring, this file
packages the polynomial

`f(X) = X ^ q + π * X`,

where `q` is the cardinality of the residue field.  Its compositional iterates
and the factors

`Qₙ(X) = (f^[n](X)) ^ (q - 1) + π`

are defined over the valuation ring itself.  These constructions do not use
an equal-characteristic model.  In particular, they apply unchanged to the
standard Lubin--Tate series over a mixed-characteristic local field.

The factorization

`f^[n+1](X) = f^[n](X) * Qₙ(X)`

is purely polynomial.  No assertion about roots, irreducibility, or finite
Lubin--Tate extensions is made here.
-/

noncomputable section

open scoped Polynomial PowerSeries

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The polynomial `X ^ q + π * X` underlying the standard Lubin--Tate
series. -/
noncomputable def standardLubinTatePolynomial
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    Polynomial F.valuationSubring :=
  Polynomial.X ^ Nat.card F.residueField +
    Polynomial.C π * Polynomial.X

/-- Evaluation of the standard polynomial has the expected two-term
formula. -/
@[simp]
theorem standardLubinTatePolynomial_eval
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    (x : F.valuationSubring) :
    (standardLubinTatePolynomial F π).eval x =
      x ^ Nat.card F.residueField + π * x := by
  simp [standardLubinTatePolynomial]

/-- Coercing the standard polynomial to a power series gives the standard
Lubin--Tate power series. -/
@[simp]
theorem standardLubinTatePolynomial_toPowerSeries
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    ((standardLubinTatePolynomial F π :
        Polynomial F.valuationSubring) :
      PowerSeries F.valuationSubring) =
        standardLubinTatePowerSeries F π := by
  simp [standardLubinTatePolynomial, standardLubinTatePowerSeries,
    add_comm]

/-- For a uniformizer, coercing the standard polynomial gives the underlying
series of the bundled standard Lubin--Tate input. -/
@[simp]
theorem standardLubinTatePolynomial_toPowerSeries_eq_series
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    ((standardLubinTatePolynomial F π :
        Polynomial F.valuationSubring) :
      PowerSeries F.valuationSubring) =
        (standardLubinTateSeries hπ).toPowerSeries := by
  rw [standardLubinTatePolynomial_toPowerSeries,
    LubinTateSeries.standardLubinTateSeries_toPowerSeries]

/-- The standard Lubin--Tate polynomial has degree `q`. -/
theorem standardLubinTatePolynomial_natDegree
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    (standardLubinTatePolynomial F π).natDegree =
      Nat.card F.residueField := by
  rw [standardLubinTatePolynomial]
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow _
  · rw [Polynomial.natDegree_X_pow]
    calc
      (Polynomial.C π * Polynomial.X).natDegree ≤ 1 := by
        simpa only [pow_one] using
          Polynomial.natDegree_C_mul_X_pow_le π 1
      _ < Nat.card F.residueField :=
        (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- The standard Lubin--Tate polynomial is monic. -/
theorem standardLubinTatePolynomial_monic
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    (standardLubinTatePolynomial F π).Monic := by
  rw [standardLubinTatePolynomial]
  refine (Polynomial.monic_X_pow _).add_of_left ?_
  calc
    (Polynomial.C π * Polynomial.X).degree ≤ 1 :=
      Polynomial.degree_C_mul_X_le π
    _ < (Polynomial.X ^ Nat.card F.residueField :
        Polynomial F.valuationSubring).degree := by
      rw [Polynomial.degree_X_pow]
      exact_mod_cast (Finite.one_lt_card : 1 < Nat.card F.residueField)

/-- The `n`-fold compositional iterate of the standard polynomial, starting
from `X`. -/
noncomputable def standardLubinTatePolynomialIterate
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    Polynomial F.valuationSubring :=
  (standardLubinTatePolynomial F π).comp^[n] Polynomial.X

/-- The zeroth compositional iterate is `X`. -/
@[simp]
theorem standardLubinTatePolynomialIterate_zero
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    standardLubinTatePolynomialIterate F π 0 = Polynomial.X := by
  simp [standardLubinTatePolynomialIterate]

/-- A successor iterate is obtained by one further composition with the
standard polynomial. -/
theorem standardLubinTatePolynomialIterate_succ
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePolynomialIterate F π (n + 1) =
      (standardLubinTatePolynomial F π).comp
        (standardLubinTatePolynomialIterate F π n) := by
  rw [standardLubinTatePolynomialIterate,
    Function.iterate_succ_apply']
  rfl

/-- The `n`-fold standard compositional iterate has degree `q ^ n`. -/
theorem standardLubinTatePolynomialIterate_natDegree
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePolynomialIterate F π n).natDegree =
      Nat.card F.residueField ^ n := by
  rw [standardLubinTatePolynomialIterate,
    Polynomial.natDegree_iterate_comp,
    standardLubinTatePolynomial_natDegree,
    Polynomial.natDegree_X, mul_one]

/-- Every compositional iterate of the standard polynomial is monic. -/
theorem standardLubinTatePolynomialIterate_monic
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePolynomialIterate F π n).Monic := by
  induction n with
  | zero =>
      simp [standardLubinTatePolynomialIterate]
  | succ n ih =>
      rw [standardLubinTatePolynomialIterate_succ]
      exact (standardLubinTatePolynomial_monic F π).comp ih
        (by
          rw [standardLubinTatePolynomialIterate_natDegree]
          exact pow_ne_zero n
            (ne_of_gt
              (Nat.zero_lt_one.trans
                (Finite.one_lt_card : 1 < Nat.card F.residueField))))

/-- Every standard compositional iterate vanishes at zero. -/
@[simp]
theorem standardLubinTatePolynomialIterate_eval_zero
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePolynomialIterate F π n).eval 0 = 0 := by
  induction n with
  | zero =>
      simp [standardLubinTatePolynomialIterate]
  | succ n ih =>
      rw [standardLubinTatePolynomialIterate_succ,
        Polynomial.eval_comp, ih]
      simp [standardLubinTatePolynomial,
        ne_of_gt
          (Nat.zero_lt_one.trans
            (Finite.one_lt_card : 1 < Nat.card F.residueField))]

/-- The primitive quotient polynomial at level `n + 1`. -/
noncomputable def standardLubinTatePrimitivePolynomial
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    Polynomial F.valuationSubring :=
  standardLubinTatePolynomialIterate F π n ^
      (Nat.card F.residueField - 1) +
    Polynomial.C π

/-- The primitive quotient polynomial has degree `(q - 1) * q ^ n`. -/
theorem standardLubinTatePrimitivePolynomial_natDegree
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial F π n).natDegree =
      (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n := by
  rw [standardLubinTatePrimitivePolynomial]
  have hpos :
      0 < (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n :=
    Nat.mul_pos
      (Nat.sub_pos_of_lt
        (Finite.one_lt_card : 1 < Nat.card F.residueField))
      (Nat.pow_pos Nat.card_pos)
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · rw [Polynomial.natDegree_pow,
      standardLubinTatePolynomialIterate_natDegree]
  · rw [Polynomial.natDegree_pow,
      standardLubinTatePolynomialIterate_natDegree,
      Polynomial.natDegree_C]
    exact hpos

/-- The primitive quotient polynomial is monic. -/
theorem standardLubinTatePrimitivePolynomial_monic
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial F π n).Monic := by
  rw [standardLubinTatePrimitivePolynomial]
  let A := standardLubinTatePolynomialIterate F π n
  have hA : A.Monic :=
    standardLubinTatePolynomialIterate_monic F π n
  have hmain :
      (A ^ (Nat.card F.residueField - 1)).Monic :=
    hA.pow _
  refine hmain.add_of_left ?_
  calc
    (Polynomial.C π).degree ≤ 0 :=
      Polynomial.degree_C_le
    _ < (A ^ (Nat.card F.residueField - 1)).degree := by
      rw [Polynomial.degree_eq_natDegree hmain.ne_zero,
        Polynomial.natDegree_pow,
        standardLubinTatePolynomialIterate_natDegree]
      exact_mod_cast Nat.mul_pos
        (Nat.sub_pos_of_lt
          (Finite.one_lt_card : 1 < Nat.card F.residueField))
        (Nat.pow_pos Nat.card_pos)

/-- The constant coefficient of the primitive quotient polynomial is `π`. -/
@[simp]
theorem standardLubinTatePrimitivePolynomial_coeff_zero
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial F π n).coeff 0 = π := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [standardLubinTatePrimitivePolynomial,
    standardLubinTatePolynomialIterate_eval_zero,
    ne_of_gt
      (Nat.sub_pos_of_lt
        (Finite.one_lt_card : 1 < Nat.card F.residueField))]

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_PrimitiveEisenstein
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Eisenstein property of the standard primitive division polynomials

Let `F` be a local field, let `π` be a uniformizer, and put

`f(X) = X ^ q + π * X`,

where `q` is the cardinality of the residue field.  Reduction modulo the
maximal ideal sends the `n`-fold compositional iterate of `f` to
`X ^ (q ^ n)`.  Consequently, the primitive quotient polynomial

`Qₙ(X) = (f^[n](X)) ^ (q - 1) + π`

reduces to its leading monomial.  Its constant coefficient is the
uniformizer itself, so `Qₙ` is Eisenstein at the maximal ideal and hence
irreducible over the valuation ring.

The argument is independent of the characteristic of `F`.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- Reduction modulo the maximal ideal sends the standard Lubin--Tate
polynomial to `X ^ q`. -/
theorem standardLubinTatePolynomial_map_residue
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    (standardLubinTatePolynomial F π).map F.residueMap =
      Polynomial.X ^ Nat.card F.residueField := by
  simp [standardLubinTatePolynomial,
    SameUniformizer.residueMap_uniformizer_eq_zero hπ]

/-- Reduction modulo the maximal ideal sends the `n`-fold standard iterate
to `X ^ (q ^ n)`. -/
theorem standardLubinTatePolynomialIterate_map_residue
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTatePolynomialIterate F π n).map F.residueMap =
      Polynomial.X ^ (Nat.card F.residueField ^ n) := by
  induction n with
  | zero =>
      simp [standardLubinTatePolynomialIterate]
  | succ n ih =>
      rw [standardLubinTatePolynomialIterate_succ,
        Polynomial.map_comp,
        standardLubinTatePolynomial_map_residue hπ,
        ih]
      simp [← pow_mul, pow_succ]

/-- Reduction modulo the maximal ideal sends the primitive quotient
polynomial to its leading monomial. -/
theorem standardLubinTatePrimitivePolynomial_map_residue
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial F π n).map F.residueMap =
      Polynomial.X ^
        ((Nat.card F.residueField - 1) *
          Nat.card F.residueField ^ n) := by
  simp [standardLubinTatePrimitivePolynomial,
    standardLubinTatePolynomialIterate_map_residue hπ,
    SameUniformizer.residueMap_uniformizer_eq_zero hπ,
    ← pow_mul, Nat.mul_comm]

/-- The standard primitive quotient polynomial is Eisenstein at the maximal
ideal of the valuation ring. -/
theorem standardLubinTatePrimitivePolynomial_isEisensteinAt
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial F π n).IsEisensteinAt
      F.maximalIdeal := by
  let Q := standardLubinTatePrimitivePolynomial F π n
  let d :=
    (Nat.card F.residueField - 1) *
      Nat.card F.residueField ^ n
  have hmonic : Q.Monic :=
    standardLubinTatePrimitivePolynomial_monic F π n
  have hprime : F.maximalIdeal.IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal F.valuationSubring).isPrime
  refine hmonic.isEisensteinAt_of_mem_of_notMem hprime.ne_top ?_ ?_
  · intro i hi
    have hcoeff :
        F.residueMap (Q.coeff i) =
          (Polynomial.X ^ d : Polynomial F.residueField).coeff i := by
      simpa only [Q, d, Polynomial.coeff_map] using
        congrArg (fun p : Polynomial F.residueField ↦ p.coeff i)
          (standardLubinTatePrimitivePolynomial_map_residue hπ n)
    have hid : i < d := by
      simpa [Q, d,
        standardLubinTatePrimitivePolynomial_natDegree] using hi
    have hzero : F.residueMap (Q.coeff i) = 0 := by
      rw [hcoeff]
      simp [Polynomial.coeff_X_pow, ne_of_lt hid]
    exact (F.toCompleteDVF.residue_eq_zero_iff (Q.coeff i)).1 hzero
  · simpa [Q] using
      F.toCompleteDVF.uniformizer_not_mem_maximalIdeal_sq hπ

/-- Every standard primitive quotient polynomial is primitive. -/
theorem standardLubinTatePrimitivePolynomial_isPrimitive
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePrimitivePolynomial F π n).IsPrimitive :=
  (standardLubinTatePrimitivePolynomial_monic F π n).isPrimitive

/-- The standard primitive quotient polynomial is irreducible by
Eisenstein's criterion. -/
theorem standardLubinTatePrimitivePolynomial_irreducible
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Irreducible (standardLubinTatePrimitivePolynomial F π n) := by
  apply (standardLubinTatePrimitivePolynomial_isEisensteinAt hπ n).irreducible
    (IsLocalRing.maximalIdeal.isMaximal F.valuationSubring).isPrime
    (standardLubinTatePrimitivePolynomial_isPrimitive F π n)
  rw [standardLubinTatePrimitivePolynomial_natDegree]
  exact Nat.mul_pos
    (Nat.sub_pos_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField))
    (Nat.pow_pos Nat.card_pos)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_PrimitiveRoot
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Primitive roots and standard Lubin--Tate level fields

For a local field `F` with uniformizer `π`, this file maps the primitive
division polynomial from the valuation ring to the fraction field.  Gauss's
lemma transfers its Eisenstein irreducibility to the field.  We also prove
separability directly, choose a root in `SeparableClosure K`, and identify
the degree of the simple extension generated by that root.

The separability argument works in both mixed and equal characteristic.  It
uses the identity

`(f^[n])'(0) = π ^ n`

for `f(X) = X ^ q + π * X`, together with the fact that `q - 1` is nonzero
in the base field.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The derivative of the standard polynomial at zero is its linear
coefficient. -/
@[simp]
theorem standardLubinTatePolynomial_derivative_eval_zero
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    (standardLubinTatePolynomial F π).derivative.eval 0 = π := by
  simp [standardLubinTatePolynomial, Polynomial.derivative_pow,
    Nat.sub_ne_zero_of_lt
      (Finite.one_lt_card : 1 < Nat.card F.residueField)]

/-- The derivative at zero of the `n`-fold standard iterate is `π ^ n`. -/
@[simp]
theorem standardLubinTatePolynomialIterate_derivative_eval_zero
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePolynomialIterate F π n).derivative.eval 0 =
      π ^ n := by
  induction n with
  | zero =>
      simp [standardLubinTatePolynomialIterate]
  | succ n ih =>
      rw [standardLubinTatePolynomialIterate_succ,
        Polynomial.derivative_comp, Polynomial.eval_mul, ih,
        Polynomial.eval_comp,
        standardLubinTatePolynomialIterate_eval_zero,
        standardLubinTatePolynomial_derivative_eval_zero]
      simp [pow_succ]

/-- The primitive division polynomial after extending coefficients from the
valuation ring to the base field. -/
noncomputable def standardLubinTatePrimitivePolynomialOverField
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    Polynomial K :=
  (standardLubinTatePrimitivePolynomial F π n).map
    (algebraMap F.valuationSubring K)

/-- The field-valued primitive polynomial has the expected formula. -/
theorem standardLubinTatePrimitivePolynomialOverField_formula
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePrimitivePolynomialOverField F π n =
      (standardLubinTatePolynomialIterate F π n).map
          (algebraMap F.valuationSubring K) ^
        (Nat.card F.residueField - 1) +
      Polynomial.C (π : K) := by
  simp [standardLubinTatePrimitivePolynomialOverField,
    standardLubinTatePrimitivePolynomial]

/-- The field-valued primitive polynomial is monic. -/
theorem standardLubinTatePrimitivePolynomialOverField_monic
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePrimitivePolynomialOverField F π n).Monic :=
  (standardLubinTatePrimitivePolynomial_monic F π n).map _

/-- The field-valued primitive polynomial has degree
`(q - 1) * q ^ n`. -/
theorem standardLubinTatePrimitivePolynomialOverField_natDegree
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePrimitivePolynomialOverField F π n).natDegree =
      (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n := by
  rw [standardLubinTatePrimitivePolynomialOverField,
    (standardLubinTatePrimitivePolynomial_monic F π n).natDegree_map,
    standardLubinTatePrimitivePolynomial_natDegree]

/-- Gauss's lemma transfers Eisenstein irreducibility from the valuation
ring to the base field. -/
theorem standardLubinTatePrimitivePolynomialOverField_irreducible
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Irreducible (standardLubinTatePrimitivePolynomialOverField F π n) := by
  let : IsFractionRing F.valuationSubring K :=
    F.toCompleteDVF.toDVF.valuationSubring_isFractionRing
  let : IsIntegrallyClosed F.valuationSubring :=
    F.toCompleteDVF.toDVF.valuationSubring_isIntegrallyClosed
  exact
    (standardLubinTatePrimitivePolynomial_monic F π n).irreducible_iff_irreducible_map_fraction_map.mp
      (standardLubinTatePrimitivePolynomial_irreducible hπ n)

/-- The natural number `q - 1` is nonzero in the local field. -/
theorem residueFieldNatCard_sub_one_cast_ne_zero
    (F : LocalField.{u, v} K) :
    ((Nat.card F.residueField - 1 : ℕ) : K) ≠ 0 := by
  have hcard :
      (Nat.card F.residueField : F.residueField) = 0 := by
    let := Fintype.ofFinite F.residueField
    rw [Nat.card_eq_fintype_card, Nat.cast_card_eq_zero]
  have hres :
      ((Nat.card F.residueField - 1 : ℕ) : F.residueField) ≠ 0 := by
    rw [Nat.cast_sub
      (Nat.le_of_lt
        (Finite.one_lt_card : 1 < Nat.card F.residueField)), hcard]
    simp
  intro hfield
  have hvaluation :
      ((Nat.card F.residueField - 1 : ℕ) : F.valuationSubring) = 0 := by
    apply Subtype.ext
    simpa using hfield
  have hreszero :
      ((Nat.card F.residueField - 1 : ℕ) : F.residueField) = 0 := by
    simpa using congrArg F.residueMap hvaluation
  exact hres hreszero

/-- The field-valued primitive polynomial has nonzero derivative. -/
theorem standardLubinTatePrimitivePolynomialOverField_derivative_ne_zero
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTatePrimitivePolynomialOverField F π n).derivative ≠ 0 := by
  let A :=
    (standardLubinTatePolynomialIterate F π n).map
      (algebraMap F.valuationSubring K)
  have hAmonic : A.Monic :=
    (standardLubinTatePolynomialIterate_monic F π n).map _
  have hAderivativeAtZero :
      A.derivative.eval 0 = (π : K) ^ n := by
    calc
      A.derivative.eval 0 =
          algebraMap F.valuationSubring K
            ((standardLubinTatePolynomialIterate F π n).derivative.eval 0) := by
        dsimp [A]
        rw [Polynomial.derivative_map, Polynomial.eval_zero_map,
          Algebra.algebraMap_ofSubsemiring_apply]
      _ = (π : K) ^ n := by
        rw [standardLubinTatePolynomialIterate_derivative_eval_zero,
          map_pow]
        rfl
  have hAderivative : A.derivative ≠ 0 := by
    intro hzero
    apply pow_ne_zero n hπ.ne_zero
    calc
      (π : K) ^ n = A.derivative.eval 0 :=
        hAderivativeAtZero.symm
      _ = 0 := by rw [hzero, Polynomial.eval_zero]
  rw [standardLubinTatePrimitivePolynomialOverField_formula]
  change
    (A ^ (Nat.card F.residueField - 1) +
      Polynomial.C (π : K)).derivative ≠ 0
  rw [Polynomial.derivative_add, Polynomial.derivative_pow,
    Polynomial.derivative_C, add_zero]
  exact mul_ne_zero
    (mul_ne_zero
      (Polynomial.C_ne_zero.mpr
        (residueFieldNatCard_sub_one_cast_ne_zero F))
      (pow_ne_zero _ hAmonic.ne_zero))
    hAderivative

/-- The field-valued primitive polynomial is separable. -/
theorem standardLubinTatePrimitivePolynomialOverField_separable
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTatePrimitivePolynomialOverField F π n).Separable :=
  (Polynomial.separable_iff_derivative_ne_zero
    (standardLubinTatePrimitivePolynomialOverField_irreducible hπ n)).2
      (standardLubinTatePrimitivePolynomialOverField_derivative_ne_zero hπ n)

/-- The primitive polynomial has a root in the chosen separable closure. -/
theorem exists_standardLubinTatePrimitivePolynomialOverField_root
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    ∃ x : SeparableClosure K,
      ((standardLubinTatePrimitivePolynomialOverField F π n).map
        (algebraMap K (SeparableClosure K))).IsRoot x := by
  let ι := algebraMap K (SeparableClosure K)
  let Q := standardLubinTatePrimitivePolynomialOverField F π n
  have hnat : 0 < (Q.map ι).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective ι.injective,
      standardLubinTatePrimitivePolynomialOverField_natDegree]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt
        (Finite.one_lt_card : 1 < Nat.card F.residueField))
      (Nat.pow_pos Nat.card_pos)
  have hdegree : (Q.map ι).degree ≠ 0 :=
    ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hnat)
  have hseparable : (Q.map ι).Separable :=
    (standardLubinTatePrimitivePolynomialOverField_separable hπ n).map
  exact IsSepClosed.exists_root (Q.map ι) hdegree hseparable

/-- A chosen primitive level-`n+1` root in `SeparableClosure K`. -/
noncomputable def chosenStandardLubinTatePrimitiveRoot
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    SeparableClosure K :=
  Classical.choose
    (exists_standardLubinTatePrimitivePolynomialOverField_root hπ n)

/-- The chosen primitive element is a root of the field-valued primitive
polynomial. -/
theorem chosenStandardLubinTatePrimitiveRoot_isRoot
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    ((standardLubinTatePrimitivePolynomialOverField F π n).map
      (algebraMap K (SeparableClosure K))).IsRoot
        (chosenStandardLubinTatePrimitiveRoot hπ n) :=
  Classical.choose_spec
    (exists_standardLubinTatePrimitivePolynomialOverField_root hπ n)

/-- The chosen primitive root is integral over the base field. -/
theorem chosenStandardLubinTatePrimitiveRoot_isIntegral
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    IsIntegral K (chosenStandardLubinTatePrimitiveRoot hπ n) := by
  refine
    ⟨standardLubinTatePrimitivePolynomialOverField F π n,
      standardLubinTatePrimitivePolynomialOverField_monic F π n, ?_⟩
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using
    (chosenStandardLubinTatePrimitiveRoot_isRoot hπ n)

/-- The field-valued primitive polynomial is the minimal polynomial of the
chosen root. -/
theorem standardLubinTatePrimitivePolynomialOverField_eq_minpoly
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTatePrimitivePolynomialOverField F π n =
      minpoly K (chosenStandardLubinTatePrimitiveRoot hπ n) := by
  apply minpoly.eq_of_irreducible_of_monic
    (standardLubinTatePrimitivePolynomialOverField_irreducible hπ n)
    _
    (standardLubinTatePrimitivePolynomialOverField_monic F π n)
  rw [Polynomial.aeval_def]
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using
    (chosenStandardLubinTatePrimitiveRoot_isRoot hπ n)

/-- The simple extension generated by the chosen primitive root. -/
@[reducible]
noncomputable def standardLubinTateLevelField
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.adjoin K
    {chosenStandardLubinTatePrimitiveRoot hπ n}

/-- Every standard Lubin--Tate level field is finite-dimensional over the
base field. -/
theorem standardLubinTateLevelField_finiteDimensional
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    FiniteDimensional K (standardLubinTateLevelField hπ n) :=
  IntermediateField.adjoin.finiteDimensional
    (chosenStandardLubinTatePrimitiveRoot_isIntegral hπ n)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_PrimitiveTorsion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Primitive Lubin--Tate torsion points

This file records the exact torsion level of the primitive roots chosen in
`PrimitiveRoot`.  The standard division-polynomial iterates are first mapped
from the valuation ring to the base field and to its fixed separable closure.
Their evaluations satisfy the expected additivity under composition.

For a root of the primitive level-`n + 1` factor, the factorization of the
next iterate shows that the level-`n + 1` iterate vanishes.  The primitive
equation and nonvanishing of the uniformizer show that the level-`n` iterate
does not vanish.  All arguments are characteristic-independent.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The `n`-fold standard iterate after extending coefficients to the fixed
separable closure of the base field. -/
noncomputable def standardLubinTatePolynomialIterateOverSeparableClosure
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    Polynomial (SeparableClosure K) :=
  (standardLubinTatePolynomialIterate F π n).map
    ((algebraMap K (SeparableClosure K)).comp
      (algebraMap F.valuationSubring K))

/-- Evaluation of the separable-closure-valued iterate is evaluation over
the valuation ring with the composite coefficient embedding. -/
@[simp]
theorem standardLubinTatePolynomialIterateOverSeparableClosure_eval
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    (n : ℕ) (x : SeparableClosure K) :
    (standardLubinTatePolynomialIterateOverSeparableClosure F π n).eval x =
      Polynomial.eval₂
        ((algebraMap K (SeparableClosure K)).comp
          (algebraMap F.valuationSubring K))
        x (standardLubinTatePolynomialIterate F π n) := by
  rw [standardLubinTatePolynomialIterateOverSeparableClosure,
    Polynomial.eval_map]

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_PrimitiveUniformizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
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

/-- The canonical power basis of the simple standard Lubin--Tate level
extension. -/
noncomputable def standardLubinTateLevelPowerBasis
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    PowerBasis K (standardLubinTateLevelField hπ n) :=
  IntermediateField.adjoin.powerBasis
    (chosenStandardLubinTatePrimitiveRoot_isIntegral hπ n)

/-- The chosen primitive root, regarded as an element of its standard level
field. -/
noncomputable def standardLubinTateLevelGenerator
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTateLevelField hπ n :=
  (standardLubinTateLevelPowerBasis hπ n).gen

/-- The level-field generator is the chosen primitive root after inclusion
into the separable closure. -/
@[simp]
theorem standardLubinTateLevelGenerator_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    ((standardLubinTateLevelGenerator hπ n :
        standardLubinTateLevelField hπ n) : SeparableClosure K) =
      chosenStandardLubinTatePrimitiveRoot hπ n := by
  simp [standardLubinTateLevelGenerator,
    standardLubinTateLevelPowerBasis,
    IntermediateField.adjoin.powerBasis_gen]

/-- The minimal polynomial of the level-field generator is the standard
primitive division polynomial over the base field. -/
theorem standardLubinTateLevelPowerBasis_minpoly
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    minpoly K (standardLubinTateLevelPowerBasis hπ n).gen =
      standardLubinTatePrimitivePolynomialOverField F π n := by
  change
    minpoly K
        (IntermediateField.adjoin.powerBasis
          (chosenStandardLubinTatePrimitiveRoot_isIntegral hπ n)).gen =
      standardLubinTatePrimitivePolynomialOverField F π n
  rw [IntermediateField.adjoin.powerBasis_gen,
    IntermediateField.minpoly_gen,
    ← standardLubinTatePrimitivePolynomialOverField_eq_minpoly hπ n]

/-- The integral primitive polynomial annihilates the level-field
generator. -/
theorem standardLubinTateLevelGenerator_aeval_primitivePolynomial
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Polynomial.aeval (standardLubinTateLevelGenerator hπ n)
        (standardLubinTatePrimitivePolynomial F π n) = 0 := by
  let Q := standardLubinTatePrimitivePolynomial F π n
  calc
    Polynomial.aeval (standardLubinTateLevelGenerator hπ n) Q =
        Polynomial.aeval (standardLubinTateLevelGenerator hπ n)
          (Q.map (algebraMap F.valuationSubring K)) := by
            symm
            exact Polynomial.aeval_map_algebraMap K
              (standardLubinTateLevelGenerator hπ n) Q
    _ = Polynomial.aeval (standardLubinTateLevelGenerator hπ n)
        (minpoly K (standardLubinTateLevelPowerBasis hπ n).gen) := by
          rw [standardLubinTateLevelPowerBasis_minpoly hπ n]
          rfl
    _ = 0 :=
      minpoly.aeval K (standardLubinTateLevelPowerBasis hπ n).gen

noncomputable local instance
    standardLubinTateLevelField_finiteDimensionalInstance
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    FiniteDimensional K (standardLubinTateLevelField hπ n) :=
  standardLubinTateLevelField_finiteDimensional hπ n

local instance standardLubinTateLevelField_isSeparableInstance
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    Algebra.IsSeparable K (standardLubinTateLevelField hπ n) :=
  (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := K) (E := SeparableClosure K)).2
    (Algebra.IsSeparable.isSeparable K
      (chosenStandardLubinTatePrimitiveRoot hπ n))

theorem standardLubinTateLevelCompleteDVFData_exists
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    ∃ target : CompleteDVF.{u, 0} (standardLubinTateLevelField hπ n),
      ∃ hExt : F.toCompleteDVF.valuation.HasExtension target.valuation,
        letI : F.toCompleteDVF.valuation.HasExtension target.valuation := hExt
        IsIntegralClosure target.valuationSubring F.valuationSubring
            (standardLubinTateLevelField hπ n) ∧
          degree F.toCompleteDVF.toDVF target.toDVF =
            ramificationIndex F.toCompleteDVF.toDVF target.toDVF *
              residueDegree F.toCompleteDVF.toDVF target.toDVF := by
  exact
    exists_integralClosure_standard_fundamental_identity
      (K := K) (L := standardLubinTateLevelField hπ n)
      F.toCompleteDVF

/-- The complete discrete valuation on a standard Lubin--Tate level field
selected from its actual integral closure over the base valuation ring. -/
noncomputable def standardLubinTateLevelCompleteDVF
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    CompleteDVF.{u, 0} (standardLubinTateLevelField hπ n) :=
  Classical.choose (standardLubinTateLevelCompleteDVFData_exists hπ n)

/-- The target valuation ring is the actual integral closure of the base
valuation ring in the standard level field. -/
theorem standardLubinTateLevelCompleteDVF_isIntegralClosure
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    IsIntegralClosure
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
      F.valuationSubring (standardLubinTateLevelField hπ n) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (standardLubinTateLevelCompleteDVFData_exists hπ n))).1

/-- The level generator is integral over the base valuation ring, witnessed
by the genuine integral primitive division polynomial. -/
theorem standardLubinTateLevelGenerator_isIntegral_over_valuationSubring
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    IsIntegral F.valuationSubring
      (standardLubinTateLevelGenerator hπ n) :=
  ⟨standardLubinTatePrimitivePolynomial F π n,
    standardLubinTatePrimitivePolynomial_monic F π n,
    standardLubinTateLevelGenerator_aeval_primitivePolynomial hπ n⟩

/-- The chosen primitive root belongs to the selected integral-closure
valuation ring. -/
theorem standardLubinTateLevelGenerator_mem_valuationSubring
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTateLevelGenerator hπ n ∈
      (standardLubinTateLevelCompleteDVF hπ n).valuation.valuationSubring := by
  let : IsIntegralClosure
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
      F.valuationSubring (standardLubinTateLevelField hπ n) :=
    standardLubinTateLevelCompleteDVF_isIntegralClosure hπ n
  rcases
      (IsIntegralClosure.isIntegral_iff
        (A := (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
        (R := F.valuationSubring)
        (B := standardLubinTateLevelField hπ n)).1
        (standardLubinTateLevelGenerator_isIntegral_over_valuationSubring
          hπ n) with
    ⟨z, hz⟩
  change
    (standardLubinTateLevelCompleteDVF hπ n).valuation
        (standardLubinTateLevelGenerator hπ n) ≤ 1
  rw [← hz]
  exact z.property

/-- The primitive division point as an element of the chosen level valuation
ring. -/
noncomputable def standardLubinTatePrimitivePointInteger
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  ⟨standardLubinTateLevelGenerator hπ n,
    standardLubinTateLevelGenerator_mem_valuationSubring hπ n⟩

/-- The valuation-ring primitive point has the chosen level generator as its
underlying field element. -/
@[simp]
theorem standardLubinTatePrimitivePointInteger_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    (standardLubinTatePrimitivePointInteger hπ n :
      standardLubinTateLevelField hπ n) =
        standardLubinTateLevelGenerator hπ n :=
  rfl

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_NormUniformizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The standard primitive polynomial over the base field has constant
coefficient `pi`. -/
@[simp]
theorem standardLubinTatePrimitivePolynomialOverField_coeff_zero
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    (standardLubinTatePrimitivePolynomialOverField F π n).coeff 0 =
      (π : K) := by
  simp [standardLubinTatePrimitivePolynomialOverField]

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_NormSubgroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
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

/-- The chosen base uniformizer, regarded as a nonzero field unit. -/
noncomputable def standardLubinTateBaseUniformizerUnit
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    Kˣ :=
  Units.mk0 (π : K) hπ.ne_zero

/-- The chosen uniformizer unit has the expected underlying field
element. -/
@[simp]
theorem standardLubinTateBaseUniformizerUnit_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    (standardLubinTateBaseUniformizerUnit hπ : K) = (π : K) :=
  rfl

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_ChangedUniformizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unit changes of a standard Lubin--Tate uniformizer

For a local field `F`, a chosen uniformizer `π`, and a valuation-ring unit
`u`, the product `uπ` is again a uniformizer.  Consequently all of the
standard finite-level Lubin--Tate constructions are available for `uπ`.

This file packages that elementary, characteristic-independent part of the
changed-uniformizer norm argument.  In particular, the negative primitive
generator at the changed level has norm `uπ`.  It also records the
cancellation step saying that, inside the norm subgroup of the original
`π`-level, membership of `uπ` is equivalent to membership of `u`, since `π`
is already a norm.

The remaining comparison between the `π`-level and the `uπ`-level requires
an actual finite-level intertwining equivalence; no such equivalence is
assumed here.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The unit change `uπ` of a chosen integral uniformizer. -/
def standardLubinTateChangedUniformizer
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    (u : F.valuationSubringˣ) :
    F.valuationSubring :=
  (u : F.valuationSubring) * π

/-- Multiplication by a valuation-ring unit preserves the uniformizer
property. -/
theorem standardLubinTateChangedUniformizer_isUniformizer
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) :
    F.toCompleteDVF.valuation.IsUniformizer
      (standardLubinTateChangedUniformizer F π u : K) := by
  exact hπ.of_associated
    (associated_unit_mul_right π (u : F.valuationSubring) u.isUnit)

/-- A valuation-ring unit regarded as a unit of the base field. -/
noncomputable def standardLubinTateUnitFactorFieldUnit
    (F : LocalField.{u, v} K) (u : F.valuationSubringˣ) :
    Kˣ :=
  CompleteDVF.valuationSubringUnitsToFieldUnits F.toCompleteDVF u

/-- The unit-factor inclusion has the expected underlying field element. -/
@[simp]
theorem standardLubinTateUnitFactorFieldUnit_coe
    (F : LocalField.{u, v} K) (u : F.valuationSubringˣ) :
    (standardLubinTateUnitFactorFieldUnit F u : K) =
      (u : F.valuationSubring) := by
  exact CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply
    F.toCompleteDVF u

/-- The changed uniformizer, regarded as a nonzero base-field unit. -/
noncomputable def standardLubinTateChangedUniformizerUnit
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) :
    Kˣ :=
  standardLubinTateBaseUniformizerUnit
    (standardLubinTateChangedUniformizer_isUniformizer hπ u)

/-- The changed uniformizer unit has underlying field element `uπ`. -/
@[simp]
theorem standardLubinTateChangedUniformizerUnit_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) :
    (standardLubinTateChangedUniformizerUnit hπ u : K) =
      (standardLubinTateChangedUniformizer F π u : K) := by
  exact standardLubinTateBaseUniformizerUnit_coe
    (standardLubinTateChangedUniformizer_isUniformizer hπ u)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormalization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Canonical unramified normalization

The canonical local norm-residue symbol is identified with the field-facing
unramified Artin map. An element of normalized valuation one maps to arithmetic
Frobenius, both algebraically and in the topological abelianization.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped IsMulCommutative ValuativeRel
open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation

abbrev A_p2 (K : Type) [Field K] : Rep ℤ (G_p3 K) :=
  intrinsicAbsoluteUnits K

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_Reduction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- Every coefficient of the defect is divisible by the chosen
uniformizer. -/
theorem uniformizer_dvd_coeff_defect
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) :
    π ∣ MvPowerSeries.coeff d (defect e ebar H) := by
  apply uniformizer_dvd_of_residueMap_eq_zero hπ
  have hcoeff := congrArg (MvPowerSeries.coeff d)
    (map_defect_eq_zero e ebar hH)
  simpa using hcoeff

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_RecursiveCoefficient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Recursive coefficients for Lubin--Tate intertwiners

This module connects the two coefficient-level inputs for the recursive
construction of a same-uniformizer Lubin--Tate intertwiner.  Reduction makes
every coefficient of the current defect divisible by the uniformizer.  In
total degree `m ≥ 2`, the remaining scalar equation has factor
`1 - π ^ (m - 1)`, which is a unit.
-/

noncomputable section

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The coefficient of an intertwining defect after removing one factor of
the chosen uniformizer. -/
noncomputable def normalizedDefectCoefficient
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) :
    F.valuationSubring :=
  Classical.choose (uniformizer_dvd_coeff_defect hπ e ebar hH d)

/-- Multiplying the normalized defect coefficient by the uniformizer recovers
the original coefficient. -/
theorem uniformizer_mul_normalizedDefectCoefficient
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) :
    π * normalizedDefectCoefficient hπ e ebar hH d =
      MvPowerSeries.coeff d (defect e ebar H) := by
  exact
    (Classical.choose_spec
      (uniformizer_dvd_coeff_defect hπ e ebar hH d)).symm

/-- The coefficient added in total degree `d.degree` by the recursive
same-uniformizer intertwiner construction.

Its defining equation is the one which cancels the normalized defect in that
degree.  The hypothesis `2 ≤ d.degree` ensures that the exponent
`d.degree - 1` is positive. -/
noncomputable def correctionCoefficient
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    F.valuationSubring :=
  Classical.choose
    (existsUnique_one_sub_uniformizer_pow_mul_eq hπ
      (by omega : d.degree - 1 ≠ 0)
      (-normalizedDefectCoefficient hπ e ebar hH d))

/-- The recursive correction coefficient satisfies its defining scalar
equation. -/
theorem correctionCoefficient_spec
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    (1 - π ^ (d.degree - 1)) *
        correctionCoefficient hπ e ebar hH d hd =
      -normalizedDefectCoefficient hπ e ebar hH d := by
  exact
    (Classical.choose_spec
      (existsUnique_one_sub_uniformizer_pow_mul_eq hπ
        (by omega : d.degree - 1 ≠ 0)
        (-normalizedDefectCoefficient hπ e ebar hH d))).1

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_DegreeStabilization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The degree-`d` coefficient of the same-uniformizer intertwining defect
depends only on coefficients of the proposed intertwiner through total degree
`d.degree`.

The slightly more general bound `m` is convenient for a recursive tower of
finite approximations: agreement through degree `m` makes every defect
coefficient of degree at most `m` stable. -/
theorem coeff_defect_eq_of_coeff_eq_degree_le
    (e ebar : LubinTateSeries F π)
    {H H' : MvPowerSeries σ F.valuationSubring}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (hH' : MvPowerSeries.constantCoeff H' = 0)
    {m : ℕ}
    (hcoeff : ∀ q : σ →₀ ℕ, q.degree ≤ m →
      MvPowerSeries.coeff q H = MvPowerSeries.coeff q H')
    {d : σ →₀ ℕ} (hd : d.degree ≤ m) :
    MvPowerSeries.coeff d (defect e ebar H) =
      MvPowerSeries.coeff d (defect e ebar H') := by
  let k := m + 1
  have htrunc : H.truncTotal k = H'.truncTotal k := by
    exact
      (truncTotal_succ_eq_iff_coeff_eq_degree_le
        (H := H) (H' := H') m).2 hcoeff
  have hleft :
      (PowerSeries.subst H e.toPowerSeries).truncTotal k =
        (PowerSeries.subst H' e.toPowerSeries).truncTotal k :=
    truncTotal_powerSeries_subst_eq_of_truncTotal_eq
      e hH hH' htrunc
  have hright :
      (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H).truncTotal k =
        (MvPowerSeries.subst
          (fun i : σ ↦ inVariable ebar i) H').truncTotal k :=
    truncTotal_inVariables_subst_eq_of_truncTotal_eq ebar htrunc
  have hdefect :
      (defect e ebar H).truncTotal k =
        (defect e ebar H').truncTotal k := by
    calc
      (defect e ebar H).truncTotal k =
          (PowerSeries.subst H e.toPowerSeries).truncTotal k -
            (MvPowerSeries.subst
              (fun i : σ ↦ inVariable ebar i) H).truncTotal k := by
        rw [defect, map_sub]
      _ = (PowerSeries.subst H' e.toPowerSeries).truncTotal k -
            (MvPowerSeries.subst
              (fun i : σ ↦ inVariable ebar i) H').truncTotal k := by
        rw [hleft, hright]
      _ = (defect e ebar H').truncTotal k := by
        rw [defect, map_sub]
  have hd' : d.degree < k := by
    dsimp only [k]
    exact Nat.lt_succ_iff.mpr hd
  calc
    MvPowerSeries.coeff d (defect e ebar H) =
        ((defect e ebar H).truncTotal k).coeff d :=
      (MvPowerSeries.coeff_truncTotal (defect e ebar H) hd').symm
    _ = ((defect e ebar H').truncTotal k).coeff d := by
      rw [hdefect]
    _ = MvPowerSeries.coeff d (defect e ebar H') :=
      MvPowerSeries.coeff_truncTotal (defect e ebar H') hd'

omit [Fintype σ] in
theorem linearInVariableStabilization_constantCoeff
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries.constantCoeff
        (linearInVariableStabilization π i) = 0 := by
  rw [linearInVariableStabilization, map_mul,
    MvPowerSeries.constantCoeff_C,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_zero_X, mul_zero]

theorem linearInVariableStabilization_hasSubst
    (π : F.valuationSubring) :
    MvPowerSeries.HasSubst
      (linearInVariableStabilization (σ := σ) π) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (linearInVariableStabilization_constantCoeff π)

omit [Fintype σ] in
theorem one_le_order_inVariable_stabilization
    (ebar : LubinTateSeries F π) (i : σ) :
    (1 : ℕ∞) ≤ (inVariable ebar i).order :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (constantCoeff_inVariable ebar i)

omit [Fintype σ] in
theorem one_le_order_linearInVariableStabilization
    (π : F.valuationSubring) (i : σ) :
    (1 : ℕ∞) ≤ (linearInVariableStabilization π i).order :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (linearInVariableStabilization_constantCoeff π i)

omit [Fintype σ] in
theorem two_le_order_inVariable_sub_linearInVariableStabilization
    (ebar : LubinTateSeries F π) (i : σ) :
    (2 : ℕ∞) ≤
      (inVariable ebar i -
        linearInVariableStabilization π i).order := by
  classical
  apply MvPowerSeries.nat_le_order
  intro d hd
  rw [map_sub]
  by_cases hdi : d = Finsupp.single i (d i)
  · by_cases hzero : d i = 0
    · have hd0 : d = 0 := by
        rw [hdi, hzero]
        simp
      subst d
      simp [inVariable, linearInVariableStabilization,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.constantCoeff_eq_zero]
    · have hone : d i = 1 := by
        have hdegree : d.degree = d i := by
          simpa only [Finsupp.degree_single] using
            congrArg Finsupp.degree hdi
        have hlt : d i < 2 := by
          rw [← hdegree]
          exact hd
        omega
      have hd1 : d = Finsupp.single i 1 := by
        rw [hdi, hone]
      subst d
      simp [inVariable, linearInVariableStabilization,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.coeff_one_eq_uniformizer]
  · have hsingle : d ≠ Finsupp.single i 1 := by
      intro h
      apply hdi
      rw [h]
      simp
    have hX :
        MvPowerSeries.coeff d
          (MvPowerSeries.X i :
            MvPowerSeries σ F.valuationSubring) = 0 := by
      rw [MvPowerSeries.coeff_X, ite_eq_right hsingle]
    simp [inVariable, linearInVariableStabilization,
      PowerSeries.coeff_subst_single, hdi, hX]

theorem degree_add_one_le_order_subst_monomial_sub_linear_stabilization
    (ebar : LubinTateSeries F π)
    (d : σ →₀ ℕ) (c : F.valuationSubring) :
    ((d.degree + 1 : ℕ) : ℕ∞) ≤
      (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
          (MvPowerSeries.monomial d c) -
        MvPowerSeries.subst
          (linearInVariableStabilization (σ := σ) π)
          (MvPowerSeries.monomial d c)).order := by
  have hprod :
      ((d.degree + 1 : ℕ) : ℕ∞) ≤
        (d.prod (fun i n => (inVariable ebar i) ^ n) -
          d.prod (fun i n =>
            (linearInVariableStabilization π i) ^ n)).order := by
    simpa only [Finsupp.prod, Finsupp.degree_apply] using
      natCast_sum_add_one_le_order_prod_pow_sub_prod_pow_stabilization
        (s := d.support)
        (fun i : σ => inVariable ebar i)
        (linearInVariableStabilization (σ := σ) π)
        (fun i => d i)
        (fun i hi => Finsupp.mem_support_iff.mp hi)
        (fun i _ => one_le_order_inVariable_stabilization ebar i)
        (fun i _ =>
          one_le_order_linearInVariableStabilization π i)
        (fun i _ =>
          two_le_order_inVariable_sub_linearInVariableStabilization
            ebar i)
  rw [
    MvPowerSeries.subst_monomial
      (inVariable_hasSubst ebar) d c,
    MvPowerSeries.subst_monomial
      (linearInVariableStabilization_hasSubst (σ := σ) π) d c,
    ← MvPowerSeries.c_eq_algebraMap]
  rw [show
    MvPowerSeries.C c *
          d.prod (fun i n => (inVariable ebar i) ^ n) -
        MvPowerSeries.C c *
          d.prod (fun i n =>
            (linearInVariableStabilization π i) ^ n) =
      c •
        (d.prod (fun i n => (inVariable ebar i) ^ n) -
          d.prod (fun i n =>
            (linearInVariableStabilization π i) ^ n)) by
    rw [MvPowerSeries.smul_eq_C_mul]
    ring]
  exact hprod.trans MvPowerSeries.le_order_smul

omit [Fintype σ] in
theorem coeff_subst_linearInVariableStabilization_monomial
    (q d : σ →₀ ℕ) (c : F.valuationSubring) :
    MvPowerSeries.coeff q
        (MvPowerSeries.subst
          (linearInVariableStabilization (σ := σ) π)
          (MvPowerSeries.monomial d c)) =
      if q = d then π ^ d.degree * c else 0 := by
  have hlinear :
      (Function.const σ π •
          (MvPowerSeries.X :
            σ → MvPowerSeries σ F.valuationSubring)) =
        linearInVariableStabilization (σ := σ) π := by
    funext i
    simp [linearInVariableStabilization, Pi.smul_apply',
      MvPowerSeries.smul_eq_C_mul]
  rw [← hlinear, ← MvPowerSeries.rescale_eq_subst,
    MvPowerSeries.coeff_rescale]
  by_cases hqd : q = d
  · subst q
    rw [MvPowerSeries.coeff_monomial_same, ite_eq_left rfl]
    simp only [Finsupp.prod, Function.const_apply,
      Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  · rw [MvPowerSeries.coeff_monomial_ne hqd, mul_zero,
      ite_eq_right hqd]

theorem linearForm_eq_sum_monomial_stabilization
    (L : σ → F.valuationSubring) :
    linearForm L =
      ∑ i, MvPowerSeries.monomial
        (Finsupp.single i 1) (L i) := by
  rw [linearForm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← MvPowerSeries.monomial_zero_eq_C_apply,
    MvPowerSeries.X_def,
    MvPowerSeries.monomial_mul_monomial]
  simp

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_RecursiveCorrection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The single monomial inserted at one step of the recursive construction. -/
noncomputable def monomialCorrection
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    MvPowerSeries σ F.valuationSubring :=
  MvPowerSeries.monomial d
    (correctionCoefficient hπ e ebar hH d hd)

/-- Insert the recursive correction into the current approximation. -/
noncomputable def correctedIntertwiner
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    MvPowerSeries σ F.valuationSubring :=
  H + monomialCorrection hπ e ebar hH d hd

omit [Fintype σ] in
theorem one_le_order_inVariable
    (ebar : LubinTateSeries F π) (i : σ) :
    (1 : ℕ∞) ≤ (inVariable ebar i).order :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (constantCoeff_inVariable ebar i)

omit [Fintype σ] in
theorem one_le_order_linearInVariable
    (π : F.valuationSubring) (i : σ) :
    (1 : ℕ∞) ≤ (linearInVariable π i).order :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (linearInVariable_constantCoeff π i)

omit [Fintype σ] in
theorem two_le_order_inVariable_sub_linearInVariable
    (ebar : LubinTateSeries F π) (i : σ) :
    (2 : ℕ∞) ≤ (inVariable ebar i - linearInVariable π i).order := by
  classical
  apply MvPowerSeries.nat_le_order
  intro d hd
  have hdNat : d.degree < 2 := by
    exact_mod_cast hd
  rw [map_sub]
  by_cases hdi : d = Finsupp.single i (d i)
  · by_cases hzero : d i = 0
    · have hd0 : d = 0 := by
        rw [hdi, hzero]
        simp
      subst d
      simp [inVariable, linearInVariable,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.constantCoeff_eq_zero]
    · have hone : d i = 1 := by
        rw [hdi, Finsupp.degree_single] at hdNat
        omega
      have hd1 : d = Finsupp.single i 1 := by
        rw [hdi, hone]
      subst d
      simp [inVariable, linearInVariable,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.coeff_one_eq_uniformizer]
  · have hsingle : d ≠ Finsupp.single i 1 := by
      intro h
      apply hdi
      rw [h]
      simp
    simp [inVariable, linearInVariable,
      PowerSeries.coeff_subst_single, hdi,
      MvPowerSeries.coeff_X, hsingle]

omit [Fintype σ] in
theorem coeff_subst_linearInVariable_monomial
    (d : σ →₀ ℕ) (c : F.valuationSubring) :
    MvPowerSeries.coeff d
        (MvPowerSeries.subst (linearInVariable (σ := σ) π)
          (MvPowerSeries.monomial d c)) =
      π ^ d.degree * c := by
  have hlinear :
      (Function.const σ π •
          (MvPowerSeries.X :
            σ → MvPowerSeries σ F.valuationSubring)) =
        linearInVariable (σ := σ) π := by
    funext i
    simp [linearInVariable, MvPowerSeries.smul_eq_C_mul]
  rw [← hlinear, ← MvPowerSeries.rescale_eq_subst,
    MvPowerSeries.coeff_rescale,
    MvPowerSeries.coeff_monomial_same]
  simp only [Finsupp.prod, Function.const_apply,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

theorem coeff_subst_lubinTateSeries_add_monomial
    (e : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree)
    (c : F.valuationSubring) :
    MvPowerSeries.coeff d
        (PowerSeries.subst
          (H + MvPowerSeries.monomial d c)
          e.toPowerSeries) =
      MvPowerSeries.coeff d
          (PowerSeries.subst H e.toPowerSeries) +
        π * c := by
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    simp at hd
  have hMconstant :
      MvPowerSeries.constantCoeff
          (MvPowerSeries.monomial d c) = 0 :=
    constantCoeff_monomial_eq_zero hd0 c
  have hHconstant :
      MvPowerSeries.constantCoeff H = 0 :=
    hH.constantCoeff_eq_zero
  have hnewSubst :
      PowerSeries.HasSubst
        (H + MvPowerSeries.monomial d c) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      simp [hHconstant, hMconstant])
  let oldTerm : ℕ → F.valuationSubring := fun n =>
    PowerSeries.coeff n e.toPowerSeries •
      MvPowerSeries.coeff d (H ^ n)
  let deltaTerm : ℕ → F.valuationSubring := fun n =>
    PowerSeries.coeff n e.toPowerSeries •
      if n = 1 then c else 0
  have hold : Function.HasFiniteSupport oldTerm := by
    simpa only [oldTerm] using
      PowerSeries.coeff_subst_finite hH.hasSubst e.toPowerSeries d
  have hdelta : Function.HasFiniteSupport deltaTerm := by
    rw [Function.HasFiniteSupport]
    refine (Set.finite_singleton 1).subset ?_
    intro n hn
    simp only [Function.mem_support] at hn
    simp only [Set.mem_singleton_iff]
    by_contra hne
    apply hn
    simp [deltaTerm, hne]
  rw [
    PowerSeries.coeff_subst hnewSubst e.toPowerSeries d,
    PowerSeries.coeff_subst hH.hasSubst e.toPowerSeries d]
  calc
    ∑ᶠ n : ℕ,
        PowerSeries.coeff n e.toPowerSeries •
          MvPowerSeries.coeff d
            ((H + MvPowerSeries.monomial d c) ^ n) =
        ∑ᶠ n : ℕ, (oldTerm n + deltaTerm n) := by
      apply finsum_congr
      intro n
      rw [coeff_pow_add_monomial hHconstant d hd c n,
        smul_add]
    _ = (∑ᶠ n : ℕ, oldTerm n) +
        ∑ᶠ n : ℕ, deltaTerm n :=
      finsum_add_distrib hold hdelta
    _ = (∑ᶠ n : ℕ, oldTerm n) +
        PowerSeries.coeff 1 e.toPowerSeries * c := by
      congr 1
      rw [finsum_eq_single _ 1]
      · simp [deltaTerm, smul_eq_mul]
      · intro n hn
        simp [deltaTerm, hn]
    _ = (∑ᶠ n : ℕ, oldTerm n) + π * c := by
      rw [LubinTateSeries.coeff_one_eq_uniformizer]

/-- A correction in total degree at least two does not change the prescribed
linear term. -/
theorem correctedIntertwiner_hasLinearTerm
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    HasLinearTerm (correctedIntertwiner hπ e ebar hH d hd) L := by
  rw [correctedIntertwiner, HasLinearTerm]
  have hd' : (2 : ℕ∞) ≤ (d.degree : ℕ∞) := by
    exact_mod_cast hd
  have hcorrection :
      (2 : ℕ∞) ≤ (monomialCorrection hπ e ebar hH d hd).order :=
    hd'.trans
      (degree_le_order_monomial d
        (correctionCoefficient hπ e ebar hH d hd))
  rw [show
    H + monomialCorrection hπ e ebar hH d hd - linearForm L =
      (H - linearForm L) +
        monomialCorrection hπ e ebar hH d hd by ring]
  exact
    (le_min hH hcorrection).trans
      MvPowerSeries.min_order_le_add

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_RecursiveIntertwiner
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {pi : F.valuationSubring}
variable {sigma : Type w} [Fintype sigma]

/-- One step in a fixed-degree correction list, bundled with preservation of
the prescribed linear term. -/
noncomputable def correctionStep
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (H : Approximation (F := F) L)
    (d : {d : sigma →₀ ℕ // d.degree = m}) :
    Approximation (F := F) L := by
  have hd : 2 ≤ d.1.degree := by
    simpa only [d.2] using hm
  exact
    ⟨correctedIntertwiner hpi e ebar H.2 d.1 hd,
      correctedIntertwiner_hasLinearTerm hpi e ebar H.2 d.1 hd⟩

/-- Apply a list of fixed-degree monomial corrections from left to right. -/
noncomputable def correctList
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : Approximation (F := F) L) :
    Approximation (F := F) L :=
  ds.foldl (correctionStep hpi e ebar hm) H

theorem coeff_correctionStep_eq_of_degree_lt
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (H : Approximation (F := F) L)
    (d : {d : sigma →₀ ℕ // d.degree = m})
    (q : sigma →₀ ℕ) (hq : q.degree < m) :
    MvPowerSeries.coeff q (correctionStep hpi e ebar hm H d).1 =
      MvPowerSeries.coeff q H.1 := by
  have hqd : q ≠ d.1 := by
    intro h
    have hdegree : q.degree = d.1.degree :=
      congrArg (fun x : sigma →₀ ℕ => x.degree) h
    rw [d.2] at hdegree
    omega
  simp only [correctionStep, correctedIntertwiner,
    monomialCorrection, map_add,
    MvPowerSeries.coeff_monomial_ne hqd, add_zero]

theorem coeff_correctList_eq_of_degree_lt
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : Approximation (F := F) L)
    (q : sigma →₀ ℕ) (hq : q.degree < m) :
    MvPowerSeries.coeff q (correctList hpi e ebar hm ds H).1 =
      MvPowerSeries.coeff q H.1 := by
  induction ds generalizing H with
  | nil => rfl
  | cons d ds ih =>
      calc
        MvPowerSeries.coeff q
              (correctList hpi e ebar hm (d :: ds) H).1 =
            MvPowerSeries.coeff q
              (correctList hpi e ebar hm ds
                (correctionStep hpi e ebar hm H d)).1 := by
              rfl
        _ = MvPowerSeries.coeff q
              (correctionStep hpi e ebar hm H d).1 :=
          ih (correctionStep hpi e ebar hm H d)
        _ = MvPowerSeries.coeff q H.1 :=
          coeff_correctionStep_eq_of_degree_lt
            hpi e ebar hm H d q hq

/-- Correct every monomial in one fixed total degree. -/
noncomputable def correctDegree
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    (H : Approximation (F := F) L)
    (m : ℕ) (hm : 2 ≤ m) :
    Approximation (F := F) L :=
  correctList hpi e ebar hm (degreeIndexList (sigma := sigma) m) H

theorem coeff_correctDegree_eq_of_degree_lt
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    (H : Approximation (F := F) L)
    (m : ℕ) (hm : 2 ≤ m)
    (q : sigma →₀ ℕ) (hq : q.degree < m) :
    MvPowerSeries.coeff q (correctDegree hpi e ebar H m hm).1 =
      MvPowerSeries.coeff q H.1 :=
  coeff_correctList_eq_of_degree_lt
    hpi e ebar hm (degreeIndexList (sigma := sigma) m) H q hq

/-- The bundled finite-degree approximations.  Stage zero is the prescribed
linear form, and stage `n + 1` corrects total degree `n + 2`. -/
noncomputable def approximation
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) :
    ℕ → Approximation (F := F) L
  | 0 => ⟨linearForm L, linearForm_hasLinearTerm L⟩
  | n + 1 =>
      correctDegree hpi e ebar
        (approximation hpi e ebar L n) (n + 2) (by omega)

/-- The stage-`n` finite-degree approximation to the intertwiner with linear
term `L`. -/
noncomputable def intertwinerApproximation
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) (n : ℕ) :
    MvPowerSeries sigma F.valuationSubring :=
  (approximation hpi e ebar L n).1

/-- Every finite-degree approximation retains the prescribed linear term. -/
theorem intertwinerApproximation_hasLinearTerm
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) (n : ℕ) :
    HasLinearTerm (intertwinerApproximation hpi e ebar L n) L :=
  (approximation hpi e ebar L n).2

/-- Stage zero is exactly the prescribed linear form. -/
@[simp]
theorem intertwinerApproximation_zero
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) :
    intertwinerApproximation hpi e ebar L 0 = linearForm L :=
  rfl

/-- Passing from stage `n` to stage `n + 1` leaves every coefficient below
total degree `n + 2` unchanged. -/
theorem coeff_intertwinerApproximation_succ_eq_of_degree_lt
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring)
    (n : ℕ) (q : sigma →₀ ℕ) (hq : q.degree < n + 2) :
    MvPowerSeries.coeff q
        (intertwinerApproximation hpi e ebar L (n + 1)) =
      MvPowerSeries.coeff q
        (intertwinerApproximation hpi e ebar L n) := by
  exact
    coeff_correctDegree_eq_of_degree_lt
      hpi e ebar (approximation hpi e ebar L n)
        (n + 2) (by omega) q hq

/-- Once a coefficient lies below the next correction degree, it remains
unchanged at every later finite stage. -/
theorem coeff_intertwinerApproximation_eq_of_le
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring)
    (q : sigma →₀ ℕ) {m n : ℕ} (hmn : m ≤ n)
    (hq : q.degree < m + 2) :
    MvPowerSeries.coeff q
        (intertwinerApproximation hpi e ebar L n) =
      MvPowerSeries.coeff q
        (intertwinerApproximation hpi e ebar L m) := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      rw [
        coeff_intertwinerApproximation_succ_eq_of_degree_lt
          hpi e ebar L n q (by omega)]
      exact ih

/-- The full recursive series takes the coefficient of a monomial of degree
`m` from the first stage which has already corrected degree `m`. -/
noncomputable def recursiveIntertwiner
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) :
    MvPowerSeries sigma F.valuationSubring :=
  fun d =>
    MvPowerSeries.coeff d
      (intertwinerApproximation hpi e ebar L (d.degree - 1))

/-- The defining stabilized-coefficient formula. -/
@[simp]
theorem coeff_recursiveIntertwiner
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) (d : sigma →₀ ℕ) :
    MvPowerSeries.coeff d (recursiveIntertwiner hpi e ebar L) =
      MvPowerSeries.coeff d
        (intertwinerApproximation hpi e ebar L (d.degree - 1)) :=
  rfl

/-- Through degree `n + 1`, the stabilized series agrees with the stage-`n`
finite approximation. -/
theorem coeff_recursiveIntertwiner_eq_intertwinerApproximation
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring)
    (n : ℕ) (d : sigma →₀ ℕ) (hd : d.degree ≤ n + 1) :
    MvPowerSeries.coeff d (recursiveIntertwiner hpi e ebar L) =
      MvPowerSeries.coeff d
        (intertwinerApproximation hpi e ebar L n) := by
  rw [coeff_recursiveIntertwiner]
  symm
  exact
    coeff_intertwinerApproximation_eq_of_le
      hpi e ebar L d (by omega) (by omega)

/-- The stabilized recursive series retains the prescribed linear term. -/
theorem recursiveIntertwiner_hasLinearTerm
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    (L : sigma → F.valuationSubring) :
    HasLinearTerm (recursiveIntertwiner hpi e ebar L) L := by
  rw [HasLinearTerm]
  apply MvPowerSeries.nat_le_order
  intro d hd
  have hdNat : d.degree < 2 := by
    exact_mod_cast hd
  rw [map_sub,
    coeff_recursiveIntertwiner_eq_intertwinerApproximation
      hpi e ebar L 0 d (by omega),
    intertwinerApproximation_zero,
    sub_self]

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_StandardFormalGroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
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

namespace HasLinearTerm

/-- In total degree less than two, a series with prescribed linear term
agrees coefficientwise with that linear form. -/
theorem coeff_eq_linearForm
    {H : MvPowerSeries σ R} {L : σ → R}
    (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : d.degree < 2) :
    MvPowerSeries.coeff d H =
      MvPowerSeries.coeff d (linearForm L) := by
  have hd' : (d.degree : ℕ∞) < (2 : ℕ∞) := by
    exact_mod_cast hd
  have hzero :=
    MvPowerSeries.coeff_of_lt_order (hd'.trans_le hH)
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- The coefficient of `X_i` is the prescribed coefficient `L_i`. -/
theorem coeff_single
    {H : MvPowerSeries σ R} {L : σ → R}
    (hH : HasLinearTerm H L) (i : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) H = L i := by
  rw [hH.coeff_eq_linearForm (Finsupp.single i 1) (by simp)]
  classical
  simp [linearForm, MvPowerSeries.coeff_index_single_X]

end HasLinearTerm

end LinearTerms

section StandardFormalGroup

variable (hπ :
  F.toCompleteDVF.valuation.IsUniformizer (π : K))

abbrev standardSeries :
    LubinTateSeries F π :=
  standardLubinTateSeries hπ

end StandardFormalGroup

section StandardEndomorphisms

variable (hπ :
  F.toCompleteDVF.valuation.IsUniformizer (π : K))

abbrev standardSeries' :
    LubinTateSeries F π :=
  standardLubinTateSeries hπ

/-- The one-variable standard Lubin--Tate endomorphism with linear
coefficient `a`. -/
noncomputable def standardLubinTateEndomorphism
    (a : F.valuationSubring) :
    PowerSeries F.valuationSubring :=
  recursiveIntertwiner hπ (standardSeries' hπ)
    (standardSeries' hπ) (fun _ : Unit => a)

/-- The endomorphism `[a]` has linear coefficient `a`. -/
theorem standardLubinTateEndomorphism_hasLinearTerm
    (a : F.valuationSubring) :
    HasLinearTerm (standardLubinTateEndomorphism hπ a)
      (fun _ : Unit => a) :=
  recursiveIntertwiner_hasLinearTerm hπ
    (standardSeries' hπ) (standardSeries' hπ)
    (fun _ : Unit => a)

/-- The coefficient of `X` in `[a]` is `a`. -/
@[simp]
theorem standardLubinTateEndomorphism_coeff_one
    (a : F.valuationSubring) :
    PowerSeries.coeff 1
      (standardLubinTateEndomorphism hπ a) = a := by
  exact
    (standardLubinTateEndomorphism_hasLinearTerm
      hπ a).coeff_single ()

end StandardEndomorphisms

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_isCyclotomic _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup
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
    rationalCyclotomicLevelFiniteDimensional
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  IsCyclotomicExtension.finiteDimensional
    {(m : ℕ)} ℚ (KummerTheory.rationalCyclotomicLevel m)

noncomputable local instance
    rationalCyclotomicLevelIsAbelianGalois
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

/-! Named compatibility witnesses used by the ramified-prime and ray-norm
modules.  They are not installed as a duplicate module-level instance family;
the canonical instances above already provide the same data. -/

attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionRatAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseLocallyCompactSpace
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsUltrametricDist
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationCompatible
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRelIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValued
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRel
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_r76502f_1
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsNonarchimedeanLocalField
/-- Rational cyclotomic levels are finite-dimensional over `ℚ`. -/
theorem rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    (m : ℕ+) :
    FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicLevelFiniteDimensional m

abbrev rationalCyclotomicArtinLevel (m : ℕ+) :=
  KummerTheory.rationalCyclotomicLevel m

end Reciprocity
end GlobalClassFieldTheory
end
end


