-- Prove2me | Definitions.Def_OAIQ244Duke039
-- name    : OAIQ244Duke039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:47:01.020264+00:00
-- url     : https://prove2.me/theorems/1da7d101-83e4-42ea-b2c5-a598b79dac55
-- title:
--   Definitions bundle OAIQ244Duke039 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 193 declarations of OpenAI's Lean: 55 definitions, 4 inductive types or structures, 14 instances and 120 theorems. The definitions and types are `FinitePlaceSplitsCompletely`, `GlobalClassFieldTheory.ClassFieldAxiom.idelePowerLocalUnitSubgroup`, `IdeleGroup.finiteIdeleOfFinset`, `IdeleGroup.ideleOfFiniteLocalFamily`, `IdeleGroup.principalLocalQuotientMap`, `LocalClassFieldTheory.localAbsoluteValuationSubring`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.linearEquivUnderlying`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivProdiscreteLimit`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsLinearEquivProdiscreteLimit`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_zeroSubgroup_eq_unitGroup`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDomain`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueBasis`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal`, `LocalFieldTheory.DiscreteValuationField.LocalField.MixedQPadicContext`, `LocalFieldTheory.DiscreteValuationField.LocalField.laurentImageSubfield`, `LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesAlgebra`, `LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield`, `LocalFieldTheory.DiscreteValuationField.LocalField.qpadicClosureSubfield_nontriviallyNormedField`, `LocalFieldTheory.DiscreteValuationField.LocalField.qpadicClosureSubfield_normedAlgebra`, `LocalFieldTheory.DiscreteValuationField.LocalField.qpadicCompletionToQpadicClosureSubfield`, `LocalFieldTheory.DiscreteValuationField.LocalField.qpadicNumbersAlgebra`, `LocalFieldTheory.DiscreteValuationField.LocalField.qpadicNumbersEquivQpadicClosureSubfield`, `LocalFieldTheory.DiscreteValuationField.LocalField.qpadicNumbersToQpadicClosureSubfield`, `RayClass.ApproximationPlace`, `RayClass.approximationAbsoluteValue`, `RayClass.approximationCompletion`, `RayClass.approximationCompletionMap`, `RayClass.approximationEmbedding`, `RayClass.approximationTarget`, `RayClass.approximationTargetPoint`, `RayClass.primeToRayClassProjection`, `RayClass.quotientRaySubgroupEquivIdeleRayQuotient` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Adele_Coordinates`, `AlgebraicNumberTheory_Adele_FiniteRestrictedProductBaseChange`, `AlgebraicNumberTheory_Adele_InfinitePlaceTensorBlock`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_AbsoluteValue`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_FinitePlaceCompletion`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice`, `AlgebraicNumberTheory_Adele_LocalComponents`, `AlgebraicNumberTheory_Adele_RestrictedAction`, `AlgebraicNumberTheory_Adele_RestrictedProduct`, `AlgebraicNumberTheory_Idele_ClassGroup_BaseChange`, `AlgebraicNumberTheory_Idele_Cohomology_Herbrand`, `AlgebraicNumberTheory_Idele_Extension_IdealClass`, `AlgebraicNumberTheory_Idele_Principal`, `AlgebraicNumberTheory_Idele_Relative_SPlaces`, `AlgebraicNumberTheory_Ramification_Splitting_FinitePlace`, `AlgebraicNumberTheory_RayClass_Approximation`, `AlgebraicNumberTheory_RayClass_Ideal`, `AlgebraicNumberTheory_RayClass_Topology`, `GlobalClassFieldTheory_ClassFieldAxiom_CyclicIdeleClassNormIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitSubgroup`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor`, `LocalClassFieldTheory_Finite_LocalReciprocity_LocalResidueDatum`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormalization`, `LocalField_DiscreteValuationField_Basic`, `LocalField_DiscreteValuationField_EqualCharacteristicLaurent`, `LocalField_DiscreteValuationField_IwasawaPrincipalUnits`, `LocalField_DiscreteValuationField_MixedCharacteristicQp`, `LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_AdicPadicModule`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_AdicProdiscreteComparison`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_Core`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_FiniteQuotientPadicModule`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_ProdiscretePadicModule`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_WithZeroValuationTopology`, `LocalField_DiscreteValuationField_PrincipalUnits_TeichmullerDecomposition`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke025`, `OAIQ244Duke028`, `OAIQ244Duke029` and `OAIQ244Duke030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke046`, `OAIQ244Duke047`, `OAIQ244Duke048`, `OAIQ244Duke049`, `OAIQ244Duke050`, `OAIQ244Duke051` and `OAIQ244Duke052`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Hom.Basic
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
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finsupp.Fintype
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
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
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
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
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
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
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
import Mathlib.RingTheory.LocalRing.Module
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
import Definitions.Def_OAIQ244Duke025
import Definitions.Def_OAIQ244Duke028
import Definitions.Def_OAIQ244Duke029
import Definitions.Def_OAIQ244Duke030

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_Coordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed_coe _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassToFixed_coe _root_.RelativeIdeleGroup.Cohomology.ideleClassNorm_mk _root_.RelativeIdeleGroup.Cohomology.ideleClass_smul_mk _root_.RelativeIdeleGroup.Cohomology.relativeIdele_smul_def _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.RelativeIdeleGroup.smul_class_mk _root_.TowerRelativeIdeleGroup.classGroupEquiv_mk _root_.TowerRelativeIdeleGroup.classNorm_mk _root_.TowerRelativeIdeleGroup.norm_principalIdele _root_.TowerRelativeIdeleGroup.towerRelativeIdeleEquiv_principalIdele _root_.bottomAdeleToTower_apply _root_.compositeToBaseNormQuotient_mk _root_.intermediateAdeleInclusion_tmul _root_.intermediateToCompositeNormQuotient_mk _root_.pushoutNormQuotientMap_mk _root_.pushoutNormQuotientNormBack_mk _root_.pushoutTowerAdeleInclusion_tmul _root_.pushoutTowerClassInclusion_mk _root_.pushoutTowerIdeleInclusion_principalIdele _root_.scaledRelativeBasisDiscriminantInteger_coe _root_.scaledRelativeExtensionBasis_apply _root_.scaledRelativeExtensionInteger_coe _root_.topFieldToOneStep_apply _root_.topFieldToTower_apply _root_.towerRelativeAdeleFlatten_tmul _root_.towerRelativeAdeleUnflatten_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Coordinate assembly for relative adeles

The chosen finite `K`-basis of `L` identifies
`𝔸_K ⊗[K] L` with a finite family of base adeles.  The support file
constructs and controls the forward coefficients; this file supplies the
inverse assembly map.  It is the global reconstruction half needed when
local tensor components have first been chosen place by place.
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

omit [NumberField L] in
@[simp]
theorem relativeAdeleCoefficientLinearEquiv_apply
    (z : RelativeAdeleRing K L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    relativeAdeleCoefficientLinearEquiv
        (K := K) (L := L) z i =
      relativeAdeleCoefficient
        (K := K) (L := L) z i :=
  rfl

/-- Assemble a finite family of base adeles into a relative adele. -/
noncomputable def relativeAdeleOfCoefficients
    (a :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K) :
    RelativeAdeleRing K L :=
  (relativeAdeleCoefficientLinearEquiv
    (K := K) (L := L)).symm a

omit [NumberField L] in
@[simp]
theorem relativeAdeleCoefficient_ofCoefficients
    (a :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        NumberField.AdeleRing (𝓞 K) K)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    relativeAdeleCoefficient
        (K := K) (L := L)
        (relativeAdeleOfCoefficients
          (K := K) (L := L) a) i =
      a i := by
  change
    relativeAdeleCoefficientLinearEquiv
        (K := K) (L := L)
        ((relativeAdeleCoefficientLinearEquiv
          (K := K) (L := L)).symm a) i =
      a i
  rw [LinearEquiv.apply_symm_apply]

omit [NumberField L] in
@[simp]
theorem relativeAdeleOfCoefficients_coefficients
    (z : RelativeAdeleRing K L) :
    relativeAdeleOfCoefficients
        (K := K) (L := L)
        (relativeAdeleCoefficient
          (K := K) (L := L) z) =
      z := by
  change
    (relativeAdeleCoefficientLinearEquiv
      (K := K) (L := L)).symm
        (relativeAdeleCoefficientLinearEquiv
          (K := K) (L := L) z) = z
  exact
    (relativeAdeleCoefficientLinearEquiv
      (K := K) (L := L)).symm_apply_apply z
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_LocalComponents
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed_coe _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassToFixed_coe _root_.RelativeIdeleGroup.Cohomology.ideleClassNorm_mk _root_.RelativeIdeleGroup.Cohomology.ideleClass_smul_mk _root_.RelativeIdeleGroup.Cohomology.relativeIdele_smul_def _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.RelativeIdeleGroup.smul_class_mk _root_.TowerRelativeIdeleGroup.classGroupEquiv_mk _root_.TowerRelativeIdeleGroup.classNorm_mk _root_.TowerRelativeIdeleGroup.norm_principalIdele _root_.TowerRelativeIdeleGroup.towerRelativeIdeleEquiv_principalIdele _root_.bottomAdeleToTower_apply _root_.compositeToBaseNormQuotient_mk _root_.intermediateAdeleInclusion_tmul _root_.intermediateToCompositeNormQuotient_mk _root_.pushoutNormQuotientMap_mk _root_.pushoutNormQuotientNormBack_mk _root_.pushoutTowerAdeleInclusion_tmul _root_.pushoutTowerClassInclusion_mk _root_.pushoutTowerIdeleInclusion_principalIdele _root_.scaledRelativeBasisDiscriminantInteger_coe _root_.scaledRelativeExtensionBasis_apply _root_.scaledRelativeExtensionInteger_coe _root_.topFieldToOneStep_apply _root_.topFieldToTower_apply _root_.towerRelativeAdeleFlatten_tmul _root_.towerRelativeAdeleUnflatten_tmul
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

omit [NumberField L] in
/-- A local tensor component has the expected chosen-basis
coordinates at a finite place. -/
@[simp]
theorem relativeAdeleFiniteComponent_basis_repr
    (z : RelativeAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 K))
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    (Algebra.TensorProduct.basis
        (w.adicCompletion K)
        (relativeExtensionBasis
          (K := K) (L := L))).repr
        (relativeAdeleFiniteComponent
          (K := K) (L := L) w z) i =
      (relativeAdeleCoefficient
        (K := K) (L := L) z i).2 w := by
  classical
  rw [relativeAdeleFiniteComponent_eq_sum_tmul_coefficients]
  simp [relativeExtensionBasis, Finsupp.single_apply]

omit [NumberField L] in
/-- A local tensor component has the expected chosen-basis
coordinates at an infinite place. -/
@[simp]
theorem relativeAdeleInfiniteComponent_basis_repr
    (z : RelativeAdeleRing K L)
    (w : InfinitePlace K)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    (Algebra.TensorProduct.basis
        w.Completion
        (relativeExtensionBasis
          (K := K) (L := L))).repr
        (relativeAdeleInfiniteComponent
          (K := K) (L := L) w z) i =
      (relativeAdeleCoefficient
        (K := K) (L := L) z i).1 w := by
  classical
  rw [relativeAdeleInfiniteComponent_eq_sum_tmul_coefficients]
  simp [relativeExtensionBasis, Finsupp.single_apply]
  change
    (relativeAdeleCoefficient
        (K := K) (L := L) z i).1 w *
        algebraMap K w.Completion (1 : K) =
      (relativeAdeleCoefficient
        (K := K) (L := L) z i).1 w
  rw [map_one, mul_one]

omit [NumberField L] in
/-- Equality of every archimedean and finite tensor component implies
equality of relative adeles. -/
theorem relativeAdele_ext_of_components
    {x y : RelativeAdeleRing K L}
    (hinfinite :
      ∀ w : InfinitePlace K,
        relativeAdeleInfiniteComponent
            (K := K) (L := L) w x =
          relativeAdeleInfiniteComponent
            (K := K) (L := L) w y)
    (hfinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        relativeAdeleFiniteComponent
            (K := K) (L := L) w x =
          relativeAdeleFiniteComponent
            (K := K) (L := L) w y) :
    x = y := by
  apply
    (relativeAdeleCoefficientLinearEquiv
      (K := K) (L := L)).injective
  funext i
  apply Prod.ext
  · funext w
    have h :=
      congrArg
        (fun z =>
          (Algebra.TensorProduct.basis
            w.Completion
            (relativeExtensionBasis
              (K := K) (L := L))).repr z i)
        (hinfinite w)
    change (relativeAdeleCoefficient (K := K) (L := L) x i).1 w =
      (relativeAdeleCoefficient (K := K) (L := L) y i).1 w
    simpa using h
  · apply DFunLike.coe_injective
    funext w
    have h :=
      congrArg
        (fun z =>
          (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr z i)
        (hfinite w)
    change (relativeAdeleCoefficient (K := K) (L := L) x i).2 w =
      (relativeAdeleCoefficient (K := K) (L := L) y i).2 w
    simpa using h

/-- All local tensor components of a relative idele. -/
def relativeIdeleLocalComponents :
    RelativeIdeleGroup K L →*
      RelativeLocalTensorFamily (K := K) (L := L) where
  toFun z :=
    ⟨fun w =>
        RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w z,
      fun w =>
        RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z⟩
  map_one' := by
    apply Prod.ext
    · funext w
      exact map_one
        (RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w)
    · funext w
      exact map_one
        (RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w)
  map_mul' x y := by
    apply Prod.ext
    · funext w
      exact map_mul
        (RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w) x y
    · funext w
      exact map_mul
        (RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w) x y

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem relativeIdeleLocalComponents_infinite
    (z : RelativeIdeleGroup K L)
    (w : InfinitePlace K) :
    (relativeIdeleLocalComponents
      (K := K) (L := L) z).1 w =
      RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w z :=
  rfl

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem relativeIdeleLocalComponents_finite
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    (relativeIdeleLocalComponents
      (K := K) (L := L) z).2 w =
      RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z :=
  rfl

omit [NumberField L] in
/-- The complete local-component map is injective. -/
theorem relativeIdeleLocalComponents_injective :
    Function.Injective
      (relativeIdeleLocalComponents
        (K := K) (L := L)) := by
  intro x y hxy
  apply Units.ext
  apply relativeAdele_ext_of_components
  · intro w
    have h := congrArg (fun z => z.1 w) hxy
    exact congrArg Units.val h
  · intro w
    have h := congrArg (fun z => z.2 w) hxy
    exact congrArg Units.val h
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_RestrictedProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed_coe _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassToFixed_coe _root_.RelativeIdeleGroup.Cohomology.ideleClassNorm_mk _root_.RelativeIdeleGroup.Cohomology.ideleClass_smul_mk _root_.RelativeIdeleGroup.Cohomology.relativeIdele_smul_def _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.RelativeIdeleGroup.smul_class_mk _root_.TowerRelativeIdeleGroup.classGroupEquiv_mk _root_.TowerRelativeIdeleGroup.classNorm_mk _root_.TowerRelativeIdeleGroup.norm_principalIdele _root_.TowerRelativeIdeleGroup.towerRelativeIdeleEquiv_principalIdele _root_.bottomAdeleToTower_apply _root_.compositeToBaseNormQuotient_mk _root_.intermediateAdeleInclusion_tmul _root_.intermediateToCompositeNormQuotient_mk _root_.pushoutNormQuotientMap_mk _root_.pushoutNormQuotientNormBack_mk _root_.pushoutTowerAdeleInclusion_tmul _root_.pushoutTowerClassInclusion_mk _root_.pushoutTowerIdeleInclusion_principalIdele _root_.scaledRelativeBasisDiscriminantInteger_coe _root_.scaledRelativeExtensionBasis_apply _root_.scaledRelativeExtensionInteger_coe _root_.topFieldToOneStep_apply _root_.topFieldToTower_apply _root_.towerRelativeAdeleFlatten_tmul _root_.towerRelativeAdeleUnflatten_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The restricted local product of a relative adele algebra

Using the chosen finite `K`-basis of `L`, a family of local tensor
components comes from `𝔸_K ⊗[K] L` precisely when each basis coefficient
is integral at almost every finite place.  Applying the same condition to
a family of local units and to its pointwise inverse gives an exact
restricted-product model of the relative idele group.

This construction is independent of the later identification of the
chosen-basis lattice with the product of local integer rings.
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

/-- A family of local tensor elements whose chosen-basis coefficients
are integral at almost every finite place. -/
structure RelativeLocalAdeleData where
  /-- The family of archimedean local tensor components. -/
  infinite :
    ∀ w : InfinitePlace K,
      w.Completion ⊗[K] L
  /-- The family of finite local tensor components. -/
  finite :
    ∀ w : HeightOneSpectrum (𝓞 K),
      w.adicCompletion K ⊗[K] L
  /-- Every chosen-basis coefficient of the finite family is integral
  at all but finitely many places. -/
  eventually_integral :
    ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (finite w) i ∈
          w.adicCompletionIntegers K

omit [NumberField L] in
@[ext]
theorem RelativeLocalAdeleData.ext
    {a b : RelativeLocalAdeleData (K := K) (L := L)}
    (hinfinite : a.infinite = b.infinite)
    (hfinite : a.finite = b.finite) :
    a = b := by
  cases a
  cases b
  simp_all

/-- The `i`-th base-adele coefficient assembled from local tensor
coordinates. -/
noncomputable def relativeLocalAdeleCoefficient
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    NumberField.AdeleRing (𝓞 K) K :=
  ⟨fun w =>
      (Algebra.TensorProduct.basis
          w.Completion
          (relativeExtensionBasis
            (K := K) (L := L))).repr
          (a.infinite w) i,
    ⟨fun w =>
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (a.finite w) i,
      a.eventually_integral i⟩⟩

omit [NumberField L] in
@[simp]
theorem relativeLocalAdeleCoefficient_infinite
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (i : RelativeAdeleBasisIndex (K := K) (L := L))
    (w : InfinitePlace K) :
    (relativeLocalAdeleCoefficient
      (K := K) (L := L) a i).1 w =
      (Algebra.TensorProduct.basis
          w.Completion
          (relativeExtensionBasis
            (K := K) (L := L))).repr
          (a.infinite w) i :=
  rfl

omit [NumberField L] in
@[simp]
theorem relativeLocalAdeleCoefficient_finite
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (i : RelativeAdeleBasisIndex (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    (relativeLocalAdeleCoefficient
      (K := K) (L := L) a i).2 w =
      (Algebra.TensorProduct.basis
          (w.adicCompletion K)
          (relativeExtensionBasis
            (K := K) (L := L))).repr
          (a.finite w) i :=
  rfl

/-- Assemble a restricted family of local tensor elements into a
relative adele. -/
noncomputable def relativeAdeleOfLocalData
    (a : RelativeLocalAdeleData (K := K) (L := L)) :
    RelativeAdeleRing K L :=
  relativeAdeleOfCoefficients
    (K := K) (L := L)
    (relativeLocalAdeleCoefficient
      (K := K) (L := L) a)

omit [NumberField L] in
@[simp]
theorem relativeAdeleOfLocalData_infiniteComponent
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (w : InfinitePlace K) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w
        (relativeAdeleOfLocalData
          (K := K) (L := L) a) =
      a.infinite w := by
  apply
    (Algebra.TensorProduct.basis
      w.Completion
      (relativeExtensionBasis
        (K := K) (L := L))).repr.injective
  apply Finsupp.ext
  intro i
  rw [relativeAdeleInfiniteComponent_basis_repr]
  have h :=
    relativeAdeleCoefficient_ofCoefficients
      (K := K) (L := L)
      (relativeLocalAdeleCoefficient
        (K := K) (L := L) a) i
  exact congrArg
    (fun q : NumberField.AdeleRing (𝓞 K) K =>
      q.1 w) h

omit [NumberField L] in
@[simp]
theorem relativeAdeleOfLocalData_finiteComponent
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeAdeleFiniteComponent
        (K := K) (L := L) w
        (relativeAdeleOfLocalData
          (K := K) (L := L) a) =
      a.finite w := by
  apply
    (Algebra.TensorProduct.basis
      (w.adicCompletion K)
      (relativeExtensionBasis
        (K := K) (L := L))).repr.injective
  apply Finsupp.ext
  intro i
  rw [relativeAdeleFiniteComponent_basis_repr]
  have h :=
    relativeAdeleCoefficient_ofCoefficients
      (K := K) (L := L)
      (relativeLocalAdeleCoefficient
        (K := K) (L := L) a) i
  exact congrArg
    (fun q : NumberField.AdeleRing (𝓞 K) K =>
      q.2.1 w) h

/-- A restricted family of local tensor units.  Restrictedness is
required both for the family and for its pointwise inverse. -/
structure RelativeLocalIdeleData where
  /-- The family of archimedean local tensor units. -/
  infinite :
    ∀ w : InfinitePlace K,
      (w.Completion ⊗[K] L)ˣ
  /-- The family of finite local tensor units. -/
  finite :
    ∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ
  /-- Every chosen-basis coefficient of the finite family is integral
  at all but finitely many places. -/
  eventually_integral :
    ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (finite w : w.adicCompletion K ⊗[K] L) i ∈
          w.adicCompletionIntegers K
  /-- Every chosen-basis coefficient of the pointwise inverse finite
  family is integral at all but finitely many places. -/
  eventually_inverse_integral :
    ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (↑((finite w)⁻¹) :
              w.adicCompletion K ⊗[K] L) i ∈
          w.adicCompletionIntegers K

omit [NumberField L] in
@[ext]
theorem RelativeLocalIdeleData.ext
    {a b : RelativeLocalIdeleData (K := K) (L := L)}
    (hinfinite : a.infinite = b.infinite)
    (hfinite : a.finite = b.finite) :
    a = b := by
  cases a
  cases b
  simp_all

/-- Forget local invertibility while retaining the value family. -/
noncomputable def RelativeLocalIdeleData.value
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    RelativeLocalAdeleData (K := K) (L := L) where
  infinite w := a.infinite w
  finite w := a.finite w
  eventually_integral := a.eventually_integral

/-- The pointwise inverse family as restricted local adele data. -/
noncomputable def RelativeLocalIdeleData.inverse
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    RelativeLocalAdeleData (K := K) (L := L) where
  infinite w :=
    (↑((a.infinite w)⁻¹) :
      w.Completion ⊗[K] L)
  finite w :=
    (↑((a.finite w)⁻¹) :
      w.adicCompletion K ⊗[K] L)
  eventually_integral := a.eventually_inverse_integral

/-- Extract the complete restricted local-unit family of a relative
idele. -/
noncomputable def relativeIdeleToLocalData
    (z : RelativeIdeleGroup K L) :
    RelativeLocalIdeleData (K := K) (L := L) where
  infinite w :=
    RelativeIdeleGroup.infiniteComponent
      (K := K) (L := L) w z
  finite w :=
    RelativeIdeleGroup.finiteComponent
      (K := K) (L := L) w z
  eventually_integral i := by
    filter_upwards [
      (relativeAdeleCoefficient
        (K := K) (L := L)
      (z : RelativeAdeleRing K L) i).2.2] with w hw
    rw [RelativeIdeleGroup.finiteComponent_coe,
      relativeAdeleFiniteComponent_basis_repr]
    change
      (relativeAdeleCoefficient
        (K := K) (L := L)
        (z : RelativeAdeleRing K L) i).2.1 w ∈
          w.adicCompletionIntegers K at hw ⊢
    exact hw
  eventually_inverse_integral i := by
    filter_upwards [
      (relativeAdeleCoefficient
        (K := K) (L := L)
      ((z⁻¹ : RelativeIdeleGroup K L) :
          RelativeAdeleRing K L) i).2.2] with w hw
    rw [← map_inv
      (RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w) z,
      RelativeIdeleGroup.finiteComponent_coe,
      relativeAdeleFiniteComponent_basis_repr]
    change
      (relativeAdeleCoefficient
        (K := K) (L := L)
        ((z⁻¹ : RelativeIdeleGroup K L) :
          RelativeAdeleRing K L) i).2.1 w ∈
          w.adicCompletionIntegers K at hw ⊢
    exact hw

/-- Assemble a restricted local-unit family into a relative idele. -/
noncomputable def relativeIdeleOfLocalData
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    RelativeIdeleGroup K L := by
  let x :=
    relativeAdeleOfLocalData
      (K := K) (L := L) a.value
  let y :=
    relativeAdeleOfLocalData
      (K := K) (L := L) a.inverse
  have hxy : x * y = 1 := by
    apply relativeAdele_ext_of_components
    · intro w
      rw [map_mul,
        relativeAdeleOfLocalData_infiniteComponent,
        relativeAdeleOfLocalData_infiniteComponent,
        map_one]
      change
        (((a.infinite w) * (a.infinite w)⁻¹ :
          (w.Completion ⊗[K] L)ˣ) :
            w.Completion ⊗[K] L) = 1
      simp
    · intro w
      rw [map_mul,
        relativeAdeleOfLocalData_finiteComponent,
        relativeAdeleOfLocalData_finiteComponent,
        map_one]
      change
        (((a.finite w) * (a.finite w)⁻¹ :
          (w.adicCompletion K ⊗[K] L)ˣ) :
            w.adicCompletion K ⊗[K] L) = 1
      simp
  exact Units.mkOfMulEqOne x y hxy

omit [NumberField L] in
@[simp]
theorem relativeIdeleOfLocalData_infiniteComponent
    (a : RelativeLocalIdeleData (K := K) (L := L))
    (w : InfinitePlace K) :
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w
        (relativeIdeleOfLocalData
          (K := K) (L := L) a) =
      a.infinite w := by
  apply Units.ext
  change
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w
        (relativeAdeleOfLocalData
          (K := K) (L := L) a.value) =
      (a.infinite w :
        w.Completion ⊗[K] L)
  rw [relativeAdeleOfLocalData_infiniteComponent]
  change
    (↑(a.infinite w) :
      w.Completion ⊗[K] L) =
      (↑(a.infinite w) :
        w.Completion ⊗[K] L)
  rfl

omit [NumberField L] in
@[simp]
theorem relativeIdeleOfLocalData_finiteComponent
    (a : RelativeLocalIdeleData (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w
        (relativeIdeleOfLocalData
          (K := K) (L := L) a) =
      a.finite w := by
  apply Units.ext
  change
    relativeAdeleFiniteComponent
        (K := K) (L := L) w
        (relativeAdeleOfLocalData
          (K := K) (L := L) a.value) =
      (a.finite w :
        w.adicCompletion K ⊗[K] L)
  rw [relativeAdeleOfLocalData_finiteComponent]
  change
    (↑(a.finite w) :
      w.adicCompletion K ⊗[K] L) =
      (↑(a.finite w) :
        w.adicCompletion K ⊗[K] L)
  rfl

omit [NumberField L] in
@[simp]
theorem relativeIdeleOfLocalData_toLocalData
    (z : RelativeIdeleGroup K L) :
    relativeIdeleOfLocalData
        (K := K) (L := L)
        (relativeIdeleToLocalData
          (K := K) (L := L) z) =
      z := by
  apply relativeIdeleLocalComponents_injective
  apply Prod.ext
  · funext w
    change
      RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w
          (relativeIdeleOfLocalData
            (K := K) (L := L)
            (relativeIdeleToLocalData
              (K := K) (L := L) z)) =
        RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w z
    rw [relativeIdeleOfLocalData_infiniteComponent
      (K := K) (L := L)]
    rfl
  · funext w
    change
      RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w
          (relativeIdeleOfLocalData
            (K := K) (L := L)
            (relativeIdeleToLocalData
              (K := K) (L := L) z)) =
        RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z
    rw [relativeIdeleOfLocalData_finiteComponent
      (K := K) (L := L)]
    rfl

omit [NumberField L] in
@[simp]
theorem relativeIdeleToLocalData_ofLocalData
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    relativeIdeleToLocalData
        (K := K) (L := L)
        (relativeIdeleOfLocalData
          (K := K) (L := L) a) =
      a := by
  apply RelativeLocalIdeleData.ext
  · funext w
    change
      RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w
          (relativeIdeleOfLocalData
            (K := K) (L := L) a) =
        a.infinite w
    rw [relativeIdeleOfLocalData_infiniteComponent
      (K := K) (L := L)]
  · funext w
    change
      RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w
          (relativeIdeleOfLocalData
            (K := K) (L := L) a) =
        a.finite w
    rw [relativeIdeleOfLocalData_finiteComponent
      (K := K) (L := L)]

/-- The relative idele group is exactly the coordinate-restricted
product of all local tensor unit groups. -/
noncomputable def relativeIdeleEquivLocalData :
    RelativeIdeleGroup K L ≃
      RelativeLocalIdeleData (K := K) (L := L) where
  toFun :=
    relativeIdeleToLocalData (K := K) (L := L)
  invFun :=
    relativeIdeleOfLocalData (K := K) (L := L)
  left_inv :=
    relativeIdeleOfLocalData_toLocalData
      (K := K) (L := L)
  right_inv :=
    relativeIdeleToLocalData_ofLocalData
      (K := K) (L := L)

/-- The group structure on the restricted local product, transported
through its proved equivalence with the relative idele group. -/
noncomputable instance relativeLocalIdeleDataGroup :
    Group
      (RelativeLocalIdeleData
        (K := K) (L := L)) :=
  (relativeIdeleEquivLocalData
    (K := K) (L := L)).symm.group

/-- The restricted local-product equivalence as a multiplicative
equivalence. -/
noncomputable def relativeIdeleMulEquivLocalData :
    RelativeIdeleGroup K L ≃*
      RelativeLocalIdeleData (K := K) (L := L) :=
  ((relativeIdeleEquivLocalData
    (K := K) (L := L)).symm.mulEquiv).symm

omit [NumberField L] in
@[simp]
theorem relativeIdeleMulEquivLocalData_apply
    (z : RelativeIdeleGroup K L) :
    relativeIdeleMulEquivLocalData
        (K := K) (L := L) z =
      relativeIdeleToLocalData
        (K := K) (L := L) z :=
  rfl

omit [NumberField L] in
@[simp]
theorem RelativeLocalIdeleData.infinite_mul
    (a b : RelativeLocalIdeleData (K := K) (L := L))
    (w : InfinitePlace K) :
    (a * b).infinite w =
      a.infinite w * b.infinite w := by
  change
    (relativeIdeleToLocalData
      (K := K) (L := L)
      (relativeIdeleOfLocalData
          (K := K) (L := L) a *
        relativeIdeleOfLocalData
          (K := K) (L := L) b)).infinite w =
      a.infinite w * b.infinite w
  change
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w
        (relativeIdeleOfLocalData
            (K := K) (L := L) a *
          relativeIdeleOfLocalData
            (K := K) (L := L) b) =
      a.infinite w * b.infinite w
  rw [map_mul,
    relativeIdeleOfLocalData_infiniteComponent,
    relativeIdeleOfLocalData_infiniteComponent]

omit [NumberField L] in
@[simp]
theorem RelativeLocalIdeleData.finite_mul
    (a b : RelativeLocalIdeleData (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    (a * b).finite w =
      a.finite w * b.finite w := by
  change
    (relativeIdeleToLocalData
      (K := K) (L := L)
      (relativeIdeleOfLocalData
          (K := K) (L := L) a *
        relativeIdeleOfLocalData
          (K := K) (L := L) b)).finite w =
      a.finite w * b.finite w
  change
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w
        (relativeIdeleOfLocalData
            (K := K) (L := L) a *
          relativeIdeleOfLocalData
            (K := K) (L := L) b) =
      a.finite w * b.finite w
  rw [map_mul,
    relativeIdeleOfLocalData_finiteComponent,
    relativeIdeleOfLocalData_finiteComponent]
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_BaseChange
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Base change of idele-class norms along a pushout square

For a pushout square of finite extensions

```
K  ─→  M
│       │
↓       ↓
L  ─→  N
```

this file constructs the maps on relative ideles and idele classes
that occur after adjoining roots of unity.
Keeping the bottom adele ring fixed makes the norm square an actual
determinant-norm base-change identity.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

universe u

variable
    (K M L N : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K L]
    [Algebra M N] [Algebra L N] [Algebra K N]
    [IsScalarTower K M N] [IsScalarTower K L N]
    [Algebra.IsPushout K M L N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N]

attribute [local instance] instIsMulCommutativeTowerRelativeIdeleGroup_1
attribute [local instance] instIsMulCommutativeClassGroup_1
attribute [local instance] instIsMulCommutativeIdeleClassGroup_1
omit [NumberField M] in
/-- Norm followed by class inclusion is the extension-degree power on
the base idele class group. -/
theorem ideleClassNorm_classInclusion
    (c : IdeleClassGroup K) :
    RelativeIdeleGroup.classNorm K M
        (RelativeIdeleGroup.classInclusion K M c) =
      c ^ Module.finrank K M := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)
        (RelativeIdeleGroup.norm K M
          (RelativeIdeleGroup.inclusion K M a)) =
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K) a) ^
          Module.finrank K M
  rw [RelativeIdeleGroup.norm_inclusion, map_pow]

omit [NumberField M] [NumberField L] in
/-- The norm-back composite is the `[M:K]`-power map on the original
class-norm quotient. -/
theorem pushoutNormQuotientNormBack_comp_map
    (q : RelativeIdeleGroup.ClassNormQuotient K L) :
    pushoutNormQuotientNormBack K M L N
        (pushoutNormQuotientMap K M L N q) =
      q ^ Module.finrank K M := by
  refine QuotientGroup.induction_on q ?_
  intro c
  change
    QuotientGroup.mk' (RelativeIdeleGroup.classNorm K L).range
        (RelativeIdeleGroup.classNorm K M
          (RelativeIdeleGroup.classInclusion K M c)) =
      (QuotientGroup.mk' (RelativeIdeleGroup.classNorm K L).range c) ^
        Module.finrank K M
  rw [ideleClassNorm_classInclusion, map_pow]

omit [NumberField M] [NumberField L] in
/-- If the `[M:K]`-power map on the original norm quotient is
injective, then so is the map induced by the pushout inclusion. -/
theorem pushoutNormQuotientMap_injective_of_pow_injective
    (hpow :
      Function.Injective
        (fun q : RelativeIdeleGroup.ClassNormQuotient K L =>
          q ^ Module.finrank K M)) :
    Function.Injective (pushoutNormQuotientMap K M L N) := by
  intro x y hxy
  apply hpow
  change
    x ^ Module.finrank K M =
      y ^ Module.finrank K M
  rw [← pushoutNormQuotientNormBack_comp_map K M L N x,
    ← pushoutNormQuotientNormBack_comp_map K M L N y,
    hxy]
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_Herbrand
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Herbrand cohomology of the relative idele class group

This file realizes the low-degree exact sequence on the actual relative
idele group

`1 → Lˣ → I_L → C_L → 1`.

The Galois actions are the concrete conjugation actions from the
tensor-product model of relative adeles.  The class norm is descended from
the determinant norm on relative ideles, and its relation with the Tate
norm is proved from the Galois product formula.
-/

open scoped BigOperators NumberField
open NumberField

noncomputable section


open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

namespace RelativeIdeleGroup
namespace Cohomology

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section Actions

local instance instMulDistribMulActionAlgEquiv_rfe3bea_1 :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup K L) :=
  relativeIdeleMulDistribMulAction K L
attribute [local instance] RelativeIdeleGroup.Cohomology.instMulDistribMulActionAlgEquivClassGroup
local instance instMulDistribMulActionAlgEquivSubtypeMemSubgroupPrincipalSubgroup_rfe3bea_1 :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L) :=
  principalIdeleMulDistribMulAction K L
omit [NumberField L] in
/-- Under Galois descent, the image of the class norm is exactly the
Tate-norm subgroup of the fixed idele classes. -/
theorem ideleClassNorm_range_map_equivFixed :
    (ideleClassNorm K L).range.map
        (baseIdeleClassEquivFixed K L).toMonoidHom =
      (tateNormSubgroup (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L)).subgroupOf
          (fixedSubgroup (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)) := by
  ext x
  constructor
  · rintro ⟨c, ⟨d, rfl⟩, rfl⟩
    change
      RelativeIdeleGroup.classInclusion K L
          (ideleClassNorm K L d) ∈
        tateNormSubgroup (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)
    exact
      ⟨d,
        (classInclusion_ideleClassNorm_eq_tateNorm
          K L d).symm⟩
  · intro hx
    change
      (x : RelativeIdeleGroup.ClassGroup K L) ∈
        tateNormSubgroup (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) at hx
    rcases hx with ⟨d, hd⟩
    refine
      ⟨ideleClassNorm K L d, ⟨d, rfl⟩, ?_⟩
    apply Subtype.ext
    exact
      (classInclusion_ideleClassNorm_eq_tateNorm
        K L d).trans hd

section NormQuotientIdentification

local instance ideleClassNormQuotient_baseIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance instMulDistribMulActionAlgEquiv_rfe3bea_2 :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup K L) :=
  relativeIdeleMulDistribMulAction K L
attribute [local instance] RelativeIdeleGroup.Cohomology.instMulDistribMulActionAlgEquivClassGroup
local instance instMulDistribMulActionAlgEquivSubtypeMemSubgroupPrincipalSubgroup_rfe3bea_2 :
    MulDistribMulAction (L ≃ₐ[K] L)
      (RelativeIdeleGroup.principalSubgroup K L) :=
  principalIdeleMulDistribMulAction K L
/-- The degree-zero Tate group of the actual idele class group is the
class-norm quotient `C_K / N_{L/K} C_L`. -/
noncomputable def ideleClassHerbrandH0EquivNormQuotient :
    HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) ≃*
      IdeleClassNormQuotient K L :=
  (HerbrandH0.equiv
    (G := L ≃ₐ[K] L)
    (A := RelativeIdeleGroup.ClassGroup K L)).trans
      (QuotientGroup.congr
        (ideleClassNorm K L).range
        ((tateNormSubgroup (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)).subgroupOf
            (fixedSubgroup (L ≃ₐ[K] L)
              (RelativeIdeleGroup.ClassGroup K L)))
        (baseIdeleClassEquivFixed K L)
        (ideleClassNorm_range_map_equivFixed K L)).symm

end NormQuotientIdentification

end Actions

end Cohomology
end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Principal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RelativeIdeleGroup.finiteComponent_coe _root_.RelativeIdeleGroup.finiteComponent_inclusion _root_.RelativeIdeleGroup.finiteComponent_norm _root_.RelativeIdeleGroup.finiteComponent_principalIdele _root_.RelativeIdeleGroup.infiniteComponent_coe _root_.RelativeIdeleGroup.infiniteComponent_inclusion _root_.RelativeIdeleGroup.infiniteComponent_norm _root_.RelativeIdeleGroup.infiniteComponent_principalIdele _root_.TowerRelativeIdeleGroup.classGroupEquiv_mk _root_.TowerRelativeIdeleGroup.classNorm_mk _root_.TowerRelativeIdeleGroup.norm_principalIdele _root_.TowerRelativeIdeleGroup.towerRelativeIdeleEquiv_principalIdele _root_.bottomAdeleToTower_apply _root_.compositeToBaseNormQuotient_mk _root_.intermediateAdeleInclusion_tmul _root_.intermediateToCompositeNormQuotient_mk _root_.mem_relativeAdeleCoefficientSupport_iff _root_.mem_relativeIdeleCoefficientSupport_iff _root_.pushoutNormQuotientMap_mk _root_.pushoutNormQuotientNormBack_mk _root_.pushoutTowerAdeleInclusion_tmul _root_.pushoutTowerClassInclusion_mk _root_.pushoutTowerIdeleInclusion_principalIdele _root_.relativeAdeleCoefficientLinearEquiv_apply _root_.relativeAdeleFiniteComponent_basis_repr _root_.relativeAdeleFiniteComponent_tmul _root_.relativeAdeleInfiniteComponent_basis_repr _root_.relativeAdeleInfiniteComponent_tmul _root_.relativeAdeleOfCoefficients_coefficients _root_.relativeAdeleOfLocalData_finiteComponent _root_.relativeAdeleOfLocalData_infiniteComponent _root_.relativeIdeleLocalComponents_finite _root_.relativeIdeleLocalComponents_infinite _root_.relativeIdeleMulEquivLocalData_apply _root_.relativeIdeleOfLocalData_finiteComponent _root_.relativeIdeleOfLocalData_infiniteComponent _root_.relativeIdeleOfLocalData_toLocalData _root_.topFieldToOneStep_apply _root_.topFieldToTower_apply _root_.towerRelativeAdeleFlatten_tmul _root_.towerRelativeAdeleUnflatten_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Principal ideles and their Galois module structure

This module exposes the diagonal embedding and idele class group, identifies
field units with principal relative ideles, and transports low-degree Tate
cohomology across that identification.
-/

noncomputable section

open RelativeIdeleGroup.Cohomology


open LocalClassFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The field-unit group is multiplicatively equivalent to the actual
subgroup of principal relative ideles. -/
noncomputable def fieldUnitsEquivPrincipalIdeles :
    Lˣ ≃*
      RelativeIdeleGroup.principalSubgroup K L :=
  MulEquiv.ofBijective
    (RelativeIdeleGroup.principalIdele K L).rangeRestrict
    ⟨fun _ _ h ↦
        RelativeIdeleGroup.principalIdele_injective K L
          (congrArg Subtype.val h),
      (RelativeIdeleGroup.principalIdele K L).rangeRestrict_surjective⟩

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem fieldUnitsEquivPrincipalIdeles_coe
    (x : Lˣ) :
    ((fieldUnitsEquivPrincipalIdeles K L x :
        RelativeIdeleGroup.principalSubgroup K L) :
      RelativeIdeleGroup K L) =
        RelativeIdeleGroup.principalIdele K L x :=
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Topology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceBaseIsUltrametricDist _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

/-- Every local higher-unit group is open in the multiplicative group of the
finite completion. -/
theorem isOpen_localHigherUnitGroup
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    IsOpen
      ((localHigherUnitGroup v n :
        Subgroup (v.adicCompletion K)ˣ) :
          Set (v.adicCompletion K)ˣ) := by
  let D : Subgroup (v.adicCompletion K)ˣ :=
    (v.adicCompletionIntegers K).units
  let I : Ideal (v.adicCompletionIntegers K) :=
    (IsLocalRing.maximalIdeal
      (v.adicCompletionIntegers K)) ^ n
  let toInteger : D → v.adicCompletionIntegers K :=
    fun y ↦ localIntegralValue v y
  have htoInteger : Continuous toInteger := by
    apply continuous_induced_rng.mpr
    exact Units.continuous_val.comp continuous_subtype_val
  let W : Set D := {y | toInteger y - 1 ∈ I}
  have : CompactSpace (v.adicCompletionIntegers K) :=
    Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance
  have hIOpen : IsOpen (I : Set (v.adicCompletionIntegers K)) := by
    exact IsLocalRing.isOpen_maximalIdeal_pow
      (v.adicCompletionIntegers K) n
  have hWOpen : IsOpen W := by
    exact hIOpen.preimage (htoInteger.sub continuous_const)
  have hDOpen : IsOpen (D : Set (v.adicCompletion K)ˣ) := by
    exact isOpen_finiteLocalUnits K v
  have himageOpen :
      IsOpen (Subtype.val '' W : Set (v.adicCompletion K)ˣ) :=
    hDOpen.isOpenEmbedding_subtypeVal.isOpenMap W hWOpen
  have heq :
      (localHigherUnitGroup v n :
          Set (v.adicCompletion K)ˣ) =
        Subtype.val '' W := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, rfl, hy⟩ :=
        (mem_localHigherUnitGroup_iff v n x).1 hx
      refine ⟨y, ?_, rfl⟩
      exact (localHigherUnitMap_eq_one_iff v n y).1 hy
    · rintro ⟨y, hyW, rfl⟩
      let y' : (v.adicCompletionIntegers K).units := y
      apply (mem_localHigherUnitGroup_iff v n y).2
      refine ⟨y', rfl, ?_⟩
      exact (localHigherUnitMap_eq_one_iff v n y').2 hyW
  rw [heq]
  exact himageOpen

omit [NumberField K] in
/-- At a real place the positivity subgroup is open; at a complex place it
is the whole local multiplicative group. -/
theorem isOpen_infinitePositiveSubgroup (v : InfinitePlace K) :
    IsOpen
      ((infinitePositiveSubgroup v : Subgroup v.Completionˣ) :
        Set v.Completionˣ) := by
  by_cases hv : v.IsReal
  · rw [show
      (infinitePositiveSubgroup v : Set v.Completionˣ) =
        {x : v.Completionˣ |
          0 <
            InfinitePlace.Completion.extensionEmbeddingOfIsReal
              hv (x : v.Completion)} by
        ext x
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro h
          exact h hv
        · intro h hv'
          simpa only [Subsingleton.elim hv' hv] using h]
    exact isOpen_Ioi.preimage
      ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).continuous.comp
        Units.continuous_val)
  · have htop :
        infinitePositiveSubgroup v = ⊤ := by
      ext x
      simp [mem_infinitePositiveSubgroup_iff, hv]
    rw [htop]
    exact isOpen_univ

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Ideal
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe
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

theorem ideleCongruenceSubgroup_le_primeTo
    (m : Modulus K) :
    m.ideleCongruenceSubgroup ≤
      idelePrimeToModulusSubgroup m := by
  intro a ha
  exact ⟨ha.1, fun v _ => ha.2 v⟩

/-! ### Simultaneous approximation at the places in a modulus -/

/-- The finite primes in `m`, together with all infinite places. -/
abbrev ApproximationPlace (m : Modulus K) :=
  (↥m.finitePart.support) ⊕ InfinitePlace K

/-- The absolute value represented by an approximation place. -/
abbrev approximationAbsoluteValue (m : Modulus K) :
    ApproximationPlace m → AbsoluteValue K ℝ
  | Sum.inl v => NumberField.HeightOneSpectrum.adicAbv K v.1
  | Sum.inr w => w.1

theorem adicAbv_not_isEquiv_infinitePlace
    (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv w.1 := by
  intro h
  have hle :
      w.1 ((2 : ℕ) : K) ≤ 1 :=
    h.le_one_iff.mp
      (NumberField.HeightOneSpectrum.adicAbv_natCast_le_one K v 2)
  have hw :
      w.1 ((2 : ℕ) : K) = (2 : ℝ) :=
    NumberField.InfinitePlace.map_natCast w 2
  have hfalse : (2 : ℝ) ≤ 1 := hw ▸ hle
  norm_num at hfalse

theorem approximationAbsoluteValue_isNontrivial
    (m : Modulus K) :
    ∀ i, (approximationAbsoluteValue m i).IsNontrivial
  | Sum.inl v => by
      change
        (NumberField.HeightOneSpectrum.adicAbv K v.1).IsNontrivial
      exact adicAbv_isNontrivial v.1
  | Sum.inr w => by
      change w.1.IsNontrivial
      exact w.isNontrivial

theorem approximationAbsoluteValue_pairwise
    (m : Modulus K) :
    Pairwise fun i j =>
      ¬ (approximationAbsoluteValue m i).IsEquiv
        (approximationAbsoluteValue m j) := by
  intro i j hij
  cases i with
  | inl v =>
      cases j with
      | inl w =>
          apply adicAbv_not_isEquiv_of_ne
          intro hvw
          apply hij
          exact congrArg Sum.inl (Subtype.ext hvw)
      | inr w =>
          exact adicAbv_not_isEquiv_infinitePlace v.1 w
  | inr v =>
      cases j with
      | inl w =>
          exact fun h =>
            adicAbv_not_isEquiv_infinitePlace w.1 v h.symm
      | inr w =>
          intro h
          apply hij
          congr
          change v.1.IsEquiv w.1 at h
          exact
            (InfinitePlace.eq_iff_isEquiv (K := K)).mpr h

/-- The corresponding product of local completions. -/
abbrev approximationCompletion (m : Modulus K) :
    ApproximationPlace m → Type _
  | Sum.inl v => v.1.adicCompletion K
  | Sum.inr w => w.Completion

noncomputable instance approximationCompletionTopologicalSpace
    (m : Modulus K) (i : ApproximationPlace m) :
    TopologicalSpace (approximationCompletion m i) := by
  cases i <;> simp only [approximationCompletion] <;> infer_instance

/-- Coordinatewise completion of the valued copies of `K`. -/
def approximationCompletionMap (m : Modulus K) :
    ∀ i : ApproximationPlace m,
      WithAbs (approximationAbsoluteValue m i) →
        approximationCompletion m i
  | Sum.inl v =>
      fun x =>
        FinitePlace.embedding v.1
          (WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v.1) x)
  | Sum.inr w => fun x => (x : w.Completion)

theorem denseRange_approximationCompletionMap
    (m : Modulus K) :
    ∀ i, DenseRange (approximationCompletionMap m i)
  | Sum.inl v => denseRange_finiteApproximationCompletionMap v.1
  | Sum.inr w =>
      NumberField.InfinitePlace.Completion.denseRange_coe w

theorem continuous_approximationCompletionMap
    (m : Modulus K) :
    ∀ i, Continuous (approximationCompletionMap m i)
  | Sum.inl v => continuous_finiteApproximationCompletionMap v.1
  | Sum.inr w =>
      NumberField.InfinitePlace.Completion.continuous_coe w

/-- The diagonal embedding into the finite product of the relevant
completions. -/
def approximationEmbedding (m : Modulus K) :
    K → (i : ApproximationPlace m) → approximationCompletion m i :=
  (Pi.map (approximationCompletionMap m)) ∘
    algebraMap K
      ((i : ApproximationPlace m) →
        WithAbs (approximationAbsoluteValue m i))

@[simp]
theorem approximationEmbedding_finite
    (m : Modulus K) (x : K) (v : ↥m.finitePart.support) :
    approximationEmbedding m x (Sum.inl v) =
      FinitePlace.embedding v.1 x :=
  rfl

@[simp]
theorem approximationEmbedding_infinite
    (m : Modulus K) (x : K) (w : InfinitePlace K) :
    approximationEmbedding m x (Sum.inr w) =
      (x : w.Completion) :=
  rfl

theorem denseRange_approximationEmbedding (m : Modulus K) :
    DenseRange (approximationEmbedding m) := by
  exact
    (DenseRange.piMap
      (denseRange_approximationCompletionMap m)).comp
      (AbsoluteValue.denseRange_algebraMap_pi
        (approximationAbsoluteValue_isNontrivial m)
        (approximationAbsoluteValue_pairwise m))
      (.piMap (continuous_approximationCompletionMap m))

/-- The value of the distinguished unit belongs to its unit-ratio set. -/
theorem val_mem_unitRatioSet
    {F : Type*} [Field F] (a : Fˣ) (U : Subgroup Fˣ) :
    (a : F) ∈ unitRatioSet a U := by
  exact ⟨a, by simp, rfl⟩

/-- The open local conditions that make `a / x` prime to `m`. -/
def approximationTarget (m : Modulus K) (a : IdeleGroup K) :
    ∀ i : ApproximationPlace m, Set (approximationCompletion m i)
  | Sum.inl v =>
      unitRatioSet (a.2 v.1)
        (localHigherUnitGroup v.1 (m.finitePart v.1))
  | Sum.inr w =>
      unitRatioSet
        (ContinuousMulEquiv.piUnits a.1 w)
        (m.localInfiniteCongruenceSubgroup w)

theorem isOpen_approximationTarget
    (m : Modulus K) (a : IdeleGroup K) :
    ∀ i, IsOpen (approximationTarget m a i)
  | Sum.inl v => by
      change IsOpen
        (unitRatioSet (a.2 v.1)
          (localHigherUnitGroup v.1 (m.finitePart v.1)))
      exact isOpen_unitRatioSet _ _
        (isOpen_localHigherUnitGroup v.1 (m.finitePart v.1))
  | Sum.inr w => by
      change IsOpen
        (unitRatioSet
          (ContinuousMulEquiv.piUnits a.1 w)
          (m.localInfiniteCongruenceSubgroup w))
      apply isOpen_unitRatioSet _ _
      classical
      by_cases hw : w.IsReal
      · by_cases hmem : (⟨w, hw⟩ : RealPlace K) ∈ m.infinitePart
        · rw [Modulus.localInfiniteCongruenceSubgroup,
            dite_eq_left hw, dite_eq_left hmem]
          exact isOpen_infinitePositiveSubgroup w
        · rw [Modulus.localInfiniteCongruenceSubgroup,
            dite_eq_left hw, dite_eq_right hmem]
          exact isOpen_univ
      · rw [Modulus.localInfiniteCongruenceSubgroup, dite_eq_right hw]
        exact isOpen_univ

/-- The given idele itself lies in the product of its approximation
neighborhoods. -/
def approximationTargetPoint
    (m : Modulus K) (a : IdeleGroup K) :
    (i : ApproximationPlace m) → approximationCompletion m i
  | Sum.inl v => (a.2 v.1 : v.1.adicCompletion K)
  | Sum.inr w =>
      (ContinuousMulEquiv.piUnits a.1 w : w.Completion)

theorem approximationTargetPoint_mem
    (m : Modulus K) (a : IdeleGroup K) :
    approximationTargetPoint m a ∈
      Set.univ.pi (approximationTarget m a) := by
  intro i _hi
  cases i with
  | inl v =>
      exact val_mem_unitRatioSet _ _
  | inr w =>
      exact val_mem_unitRatioSet _ _

/-- Weak approximation in the precise open local cosets required by the
modulus. -/
theorem exists_principal_quotient_mem_primeTo
    (m : Modulus K) (a : IdeleGroup K) :
    ∃ x : Kˣ,
      a * (IdeleGroup.principalIdele K x)⁻¹ ∈
        idelePrimeToModulusSubgroup m := by
  let U : Set
      ((i : ApproximationPlace m) → approximationCompletion m i) :=
    Set.univ.pi (approximationTarget m a)
  have hUOpen : IsOpen U := by
    exact isOpen_set_pi Set.finite_univ fun i _hi =>
      isOpen_approximationTarget m a i
  have hUNonempty : U.Nonempty :=
    ⟨approximationTargetPoint m a,
      approximationTargetPoint_mem m a⟩
  obtain ⟨x, hx⟩ :=
    (denseRange_approximationEmbedding m).exists_mem_open
      hUOpen hUNonempty
  let w₀ : InfinitePlace K := Classical.choice inferInstance
  have hxw₀ :=
    hx (Sum.inr w₀) (Set.mem_univ (Sum.inr w₀))
  change
    (x : w₀.Completion) ∈
      unitRatioSet
        (ContinuousMulEquiv.piUnits a.1 w₀)
        (m.localInfiniteCongruenceSubgroup w₀) at hxw₀
  obtain ⟨y₀, _hy₀, hy₀x⟩ := hxw₀
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply Units.ne_zero y₀
    rw [hy₀x, hxzero,
      NumberField.InfinitePlace.Completion.coe_zero]
  let xu : Kˣ := Units.mk0 x hx0
  refine ⟨xu, ?_⟩
  constructor
  · apply
      (Modulus.mem_infiniteCongruenceSubgroup_iff_local m
        (a * (IdeleGroup.principalIdele K xu)⁻¹).1).2
    intro w
    have hw :=
      hx (Sum.inr w) (Set.mem_univ (Sum.inr w))
    change
      (x : w.Completion) ∈
        unitRatioSet
          (ContinuousMulEquiv.piUnits a.1 w)
          (m.localInfiniteCongruenceSubgroup w) at hw
    obtain ⟨y, hy, hyx⟩ := hw
    have hprincipal :
        ContinuousMulEquiv.piUnits
            (IdeleGroup.principalIdele K xu).1 w =
          y := by
      apply Units.ext
      calc
        ((ContinuousMulEquiv.piUnits
            (IdeleGroup.principalIdele K xu).1 w :
              w.Completionˣ) : w.Completion) =
            (xu : K) :=
          IdeleGroup.infiniteComponent_principalIdele xu w
        _ = (x : K) := rfl
        _ = (y : w.Completion) := hyx.symm
    change
      ContinuousMulEquiv.piUnits a.1 w *
          (ContinuousMulEquiv.piUnits
            (IdeleGroup.principalIdele K xu).1 w)⁻¹ ∈
        m.localInfiniteCongruenceSubgroup w
    rw [hprincipal]
    exact hy
  · intro v hv
    let vm : ↥m.finitePart.support := ⟨v, hv⟩
    have hvx :=
      hx (Sum.inl vm) (Set.mem_univ (Sum.inl vm))
    change
      FinitePlace.embedding v x ∈
        unitRatioSet (a.2 v)
          (localHigherUnitGroup v (m.finitePart v)) at hvx
    obtain ⟨y, hy, hyx⟩ := hvx
    have hprincipal :
        (IdeleGroup.principalIdele K xu).2 v = y := by
      apply Units.ext
      calc
        (((IdeleGroup.principalIdele K xu).2 v :
            (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            (xu : K) :=
          IdeleGroup.finiteComponent_principalIdele xu v
        _ = (x : K) := rfl
        _ = (y : v.adicCompletion K) := hyx.symm
    change
      a.2 v *
          ((IdeleGroup.principalIdele K xu).2 v)⁻¹ ∈
        localHigherUnitGroup v (m.finitePart v)
    rw [hprincipal]
    exact hy

/-- Approximation identifies the idele group as
`I_K = I_K^(m) Kˣ`. -/
theorem idelePrimeToModulusSubgroup_sup_principalSubgroup
    (m : Modulus K) :
    idelePrimeToModulusSubgroup m ⊔
        IdeleGroup.principalSubgroup K =
      ⊤ := by
  apply top_unique
  intro a _ha
  obtain ⟨x, hx⟩ :=
    exists_principal_quotient_mem_primeTo m a
  rw [Subgroup.mem_sup]
  refine
    ⟨a * (IdeleGroup.principalIdele K x)⁻¹, hx,
      IdeleGroup.principalIdele K x, ⟨x, rfl⟩, ?_⟩
  group

/-- The natural map from the prime-to-`m` ideles to the full idelic
ray-class quotient. -/
def primeToRayClassProjection (m : Modulus K) :
    idelePrimeToModulusSubgroup m →*
      IdeleGroup K ⧸
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) :=
  (QuotientGroup.mk'
    (m.ideleCongruenceSubgroup ⊔
      IdeleGroup.principalSubgroup K)).comp
    (idelePrimeToModulusSubgroup m).subtype

theorem primeToRayClassProjection_ker (m : Modulus K) :
    (primeToRayClassProjection m).ker =
      raySubgroupInPrimeTo m := by
  ext a
  constructor
  · intro ha
    have hN :
        (a : IdeleGroup K) ∈
          m.ideleCongruenceSubgroup ⊔
            IdeleGroup.principalSubgroup K := by
      rw [← QuotientGroup.eq_one_iff]
      exact MonoidHom.mem_ker.mp ha
    rw [Subgroup.mem_sup] at hN
    obtain ⟨c, hc, p, hp, hcp⟩ := hN
    have hcA :
        c ∈ idelePrimeToModulusSubgroup m :=
      ideleCongruenceSubgroup_le_primeTo m hc
    have hpA :
        p ∈ idelePrimeToModulusSubgroup m := by
      have haA :
          (a : IdeleGroup K) ∈
            idelePrimeToModulusSubgroup m :=
        a.property
      have hmul :
          c⁻¹ * (a : IdeleGroup K) ∈
            idelePrimeToModulusSubgroup m :=
        (idelePrimeToModulusSubgroup m).mul_mem
          ((idelePrimeToModulusSubgroup m).inv_mem hcA) haA
      rw [← hcp] at hmul
      simpa using hmul
    rw [raySubgroupInPrimeTo, Subgroup.mem_sup]
    refine
      ⟨⟨c, hcA⟩, ?_, ⟨p, hpA⟩, ?_, ?_⟩
    · exact hc
    · exact hp
    · apply Subtype.ext
      exact hcp
  · intro ha
    apply MonoidHom.mem_ker.mpr
    change
      QuotientGroup.mk'
          (m.ideleCongruenceSubgroup ⊔
            IdeleGroup.principalSubgroup K)
          (a : IdeleGroup K) =
        1
    rw [QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    rw [raySubgroupInPrimeTo, Subgroup.mem_sup] at ha
    obtain ⟨c, hc, p, hp, rfl⟩ := ha
    apply
      (m.ideleCongruenceSubgroup ⊔
        IdeleGroup.principalSubgroup K).mul_mem
    · exact
        (show m.ideleCongruenceSubgroup ≤
            m.ideleCongruenceSubgroup ⊔
              IdeleGroup.principalSubgroup K from le_sup_left) hc
    · exact
      (show IdeleGroup.principalSubgroup K ≤
            m.ideleCongruenceSubgroup ⊔
              IdeleGroup.principalSubgroup K from le_sup_right) hp

theorem primeToRayClassProjection_surjective (m : Modulus K) :
    Function.Surjective (primeToRayClassProjection m) := by
  intro q
  refine q.inductionOn' ?_
  intro g
  have hg :
      g ∈ idelePrimeToModulusSubgroup m ⊔
        IdeleGroup.principalSubgroup K := by
    rw [idelePrimeToModulusSubgroup_sup_principalSubgroup m]
    exact Subgroup.mem_top g
  rw [Subgroup.mem_sup] at hg
  obtain ⟨a, ha, p, hp, hap⟩ := hg
  refine ⟨⟨a, ha⟩, ?_⟩
  change
    QuotientGroup.mk'
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) a =
      QuotientGroup.mk'
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) g
  rw [← hap, map_mul]
  have hpN :
      p ∈ m.ideleCongruenceSubgroup ⊔
        IdeleGroup.principalSubgroup K :=
    (show IdeleGroup.principalSubgroup K ≤
        m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K from le_sup_right) hp
  have hmkp :
      QuotientGroup.mk'
          (m.ideleCongruenceSubgroup ⊔
            IdeleGroup.principalSubgroup K) p =
        1 := by
    rw [QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hpN
  rw [hmkp]
  exact
    (mul_one
      (QuotientGroup.mk'
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) a)).symm

/-- Restricting the full idelic ray-class quotient to prime-to-`m`
ideles is an equivalence. -/
def quotientRaySubgroupEquivIdeleRayQuotient
    (m : Modulus K) :
    idelePrimeToModulusSubgroup m ⧸
        raySubgroupInPrimeTo m ≃*
      IdeleGroup K ⧸
        (m.ideleCongruenceSubgroup ⊔
          IdeleGroup.principalSubgroup K) :=
  (QuotientGroup.quotientMulEquivOfEq
      (primeToRayClassProjection_ker m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (primeToRayClassProjection m)
      (primeToRayClassProjection_surjective m))

/-- The quotient equivalence induced by the idelic ray projection evaluates
on a prime-to-modulus idele class as the original projection. -/
@[simp]
theorem quotientRaySubgroupEquivIdeleRayQuotient_mk
    (m : Modulus K) (a : idelePrimeToModulusSubgroup m) :
    quotientRaySubgroupEquivIdeleRayQuotient m
        (QuotientGroup.mk' (raySubgroupInPrimeTo m) a) =
      primeToRayClassProjection m a := by
  rw [quotientRaySubgroupEquivIdeleRayQuotient,
    MulEquiv.trans_apply, QuotientGroup.mk'_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk (primeToRayClassProjection m) a

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Approximation
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Multiplicative weak approximation for ideles

This file extracts the simultaneous approximation statement needed for ray
class groups. At finitely many
finite places one may prescribe an arbitrary open multiplicative coset and
move a given idele into all of those cosets by a single principal idele.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

/-- A finite local family, extended by `1`, is a finite idele. -/
def finiteIdeleOfFinset
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ) :
    FiniteIdeleGroup K := by
  let f : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K)ˣ :=
    fun v => if hv : v ∈ S then a ⟨v, hv⟩ else 1
  refine ⟨f, ?_⟩
  have haway :
      ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        v ∉ S := by
    rw [Filter.eventually_cofinite]
    convert S.finite_toSet using 1
    all_goals try with_reducible_and_instances rfl
    ext v
    simp
  filter_upwards [haway] with v hv
  change f v ∈ (v.adicCompletionIntegers K).units
  simp [f, hv]

@[simp]
theorem finiteIdeleOfFinset_apply_mem
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ)
    (v : ↥S) :
    finiteIdeleOfFinset S a v.1 = a v := by
  classical
  change (if hv : v.1 ∈ S then a ⟨v.1, hv⟩ else 1) = a v
  exact dite_eq_left v.2

@[simp]
theorem finiteIdeleOfFinset_apply_notMem
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    finiteIdeleOfFinset S a v = 1 := by
  classical
  change (if hmem : v ∈ S then a ⟨v, hmem⟩ else 1) =
    (1 : (v.adicCompletion K)ˣ)
  exact dite_eq_right hv

/-- The idele whose prescribed finite components are `a` and whose other
finite and all infinite components are `1`. -/
def ideleOfFiniteLocalFamily
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ) :
    IdeleGroup K :=
  (1, finiteIdeleOfFinset S a)

@[simp]
theorem ideleOfFiniteLocalFamily_finiteComponent
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ∀ v : ↥S, (v.1.adicCompletion K)ˣ)
    (v : ↥S) :
    (ideleOfFiniteLocalFamily S a).2 v.1 = a v :=
  finiteIdeleOfFinset_apply_mem S a v

/-- The diagonal map from `Kˣ` to a finite product of local multiplicative
quotients. -/
def principalLocalQuotientMap
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (U : ∀ v : ↥S, Subgroup (v.1.adicCompletion K)ˣ) :
    Kˣ →* (∀ v : ↥S, (v.1.adicCompletion K)ˣ ⧸ U v) :=
  MonoidHom.pi fun v =>
    (QuotientGroup.mk' (U v)).comp
      ((finiteComponent v.1).comp (principalIdele K))

@[simp]
theorem principalLocalQuotientMap_apply
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (U : ∀ v : ↥S, Subgroup (v.1.adicCompletion K)ˣ)
    (x : Kˣ) (v : ↥S) :
    principalLocalQuotientMap S U x v =
      QuotientGroup.mk' (U v) ((principalIdele K x).2 v.1) :=
  rfl

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnits_TeichmullerDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.normSubgroupClassInZeroQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.residueDegreeClassSubgroup_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.ofWithZeroValuation_val _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientZeroSubgroupEquivValueSubgroup_norm_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.toAdd_quotientZeroSubgroupEquivValueSubgroup_norm_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.toAdd_valuationHom_apply_norm _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valuationHom_apply_norm _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valuationHom_apply_norm_div _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valuation_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valuation_apply_div _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valuation_apply_uniformizer_pow _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valuation_apply_uniformizer_zpow _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valueModResidueDegreeHom_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_uniformizerClass_zpow _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.zeroQuotientModuloResidueDegreeClassEquivNormClass_uniformizerClass_zpow _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

/-!
# Teichmuller and principal-unit decompositions

Decomposes valuation-ring units and field units into residue roots, first principal units,
and a uniformizer factor.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- If the zero-valuation subgroup of a field-unit valuation is the usual
unit group of the valuation subring, then it is exactly the image of
valuation-ring units under `valuationSubringUnitFieldUnitHom`. -/
theorem mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup)
    (y : Kˣ) :
    y ∈ V.zeroSubgroup ↔
      ∃ u : F.valuationSubringˣ,
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y := by
  rw [hzero]
  constructor
  · intro hy
    let a : F.valuation.valuationSubring.unitGroup := ⟨y, hy⟩
    refine ⟨F.valuation.valuationSubring.unitGroupMulEquiv a, ?_⟩
    apply Units.ext
    simp [higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom, a]
  · rintro ⟨u, hu⟩
    rw [← hu]
    simp [higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom]

/-- Group-isomorphism form under the standard subgroup equality hypothesis
`V.zeroSubgroup = O^*`. -/
noncomputable def fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_zeroSubgroup_eq_unitGroup
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ) :
    higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ :=
  higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer
    (F := F) V
    (fun y =>
      higherPrincipalUnitGroup.mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
        (F := F) V hzero y)
    hϖ
end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_LocalResidueDatum
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open ClassFormation

open ValuationTheory RamificationTheory LocalFieldTheory

/-!
# Finite local reciprocity: the local residue degree datum

For a nonarchimedean local field `K`, this file makes the choices implicit in
the construction explicit.  The canonical local valuation is packaged as a complete
DVF, Chevalley's theorem chooses an extension to `AlgebraicClosure K`, and
that valuation is pulled back to `SeparableClosure K`.  Finite-separable
uniqueness shows that its decomposition subgroup is the whole Galois group.
The residue field of the decomposition field is then identified with the
finite residue field of `K`.

The remaining step is topological: the reduction action is shown continuous
for the two Krull topologies and is composed with the intrinsic finite-field
degree map from `ResidueAlgebraicClosureDegree`.  The selected residue field
is algebraically closed because its extension to the residue of
`AlgebraicClosure K` is purely inseparable and the selected residue field is
perfect over the finite base residue field.
-/

noncomputable section

open scoped Pointwise ValuativeRel
open _root_.RamificationTheory.HilbertRamification.ValuationSubring
open Field.absoluteGaloisGroup

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ## The canonical complete discrete valuation and its absolute extension -/

attribute [local instance] LocalClassFieldTheory.localSeparableClosureAlgebra
local instance localSeparableClosureScalarTower_rfe3bea_1 :
    IsScalarTower K (SeparableClosure K) (AlgebraicClosure K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
/-- A Chevalley extension of the local valuation to the chosen algebraic
closure.  This is the valuation choice `w | v` made in the finite local reciprocity construction. -/
noncomputable def localAbsoluteValuationSubring :
    ValuationSubring (AlgebraicClosure K) :=
  Classical.choose
    (ValuationTheory.DiscreteValuationField.Valuation.exists_extension_valuationSubring
      (L := AlgebraicClosure K) (localCompleteDVF K).valuation)

/-! ## Identification of the finite base residue field -/

/-! ## Continuity of reduction and the local degree map -/

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.decompositionField_decompositionField_integerMap_isLocalHom _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.HilbertRamification.decompositionField_decompositionField_integerMap_apply _root_.HilbertRamification.decompositionField_decompositionField_residueFieldEquiv_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.mem_decompositionRightCosetsFinset _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The tensor-product realization of a local induced block

This file connects the induced module in `LocalBlock` with the actual local
factor of the scalar-extended adele algebra.  The natural Galois action on
`K_v ⊗[K] L` is conjugation on the second tensor factor. The completion tensor-product theorem
identifies this algebra with the product of the completions above `v`.

The first part records the natural tensor action and the canonical
identifications between completions at conjugate absolute values.  These
identifications are the concrete source of the induced-module covariance in
the induced local-block calculation.
-/

open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Conjugation fixes the embedded completed base field. -/
theorem conjugateCompletionRingEquiv_completionMap
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) (b : vK.Completion) :
    conjugateCompletionRingEquiv w.1 σ
        (AbsoluteValue.completionMap vK
          (absoluteValueConjugate w.1 σ)
          (absoluteValueConjugate_extends vK w σ) b) =
      AbsoluteValue.completionMap vK w.1 w.2 b := by
  refine UniformSpace.Completion.ext'
    (UniformSpace.Completion.continuous_map.comp
      (AbsoluteValue.completionMap_isometry
        vK
        (absoluteValueConjugate w.1 σ)
        (absoluteValueConjugate_extends vK w σ)).continuous)
    (AbsoluteValue.completionMap_isometry
      vK w.1 w.2).continuous ?_ b
  intro x
  have hx : (x : vK.Completion) =
      algebraMap K vK.Completion (WithAbs.equiv vK x) := by
    rw [← AbsoluteValue.toCompletion_eq_algebraMap]
    simp
  rw [hx]
  simp only [Function.comp_apply]
  rw [AbsoluteValue.completionMap_coe,
    AbsoluteValue.completionMap_coe]
  change
    conjugateCompletionRingEquiv w.1 σ
        (AbsoluteValue.toCompletion
          (absoluteValueConjugate w.1 σ)
          (algebraMap K L (WithAbs.equiv vK x))) =
      AbsoluteValue.toCompletion w.1
        (algebraMap K L (WithAbs.equiv vK x))
  rw [conjugateCompletionRingEquiv_toCompletion, σ.commutes]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem conjugateCompletionRingEquiv_algebraMap
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) (b : vK.Completion) :
    letI :
        Algebra vK.Completion
          (absoluteValueConjugate w.1 σ).Completion :=
      AbsoluteValue.completionAlgebra vK
        (absoluteValueConjugate w.1 σ)
        (absoluteValueConjugate_extends vK w σ)
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    conjugateCompletionRingEquiv w.1 σ
        (algebraMap vK.Completion
          (absoluteValueConjugate w.1 σ).Completion b) =
      algebraMap vK.Completion w.1.Completion b :=
  conjugateCompletionRingEquiv_completionMap vK w σ b

omit [FiniteDimensional K L] [IsGalois K L] in
theorem conjugateExtensionCompletionRingEquiv_algebraMap
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L) (b : vK.Completion) :
    letI :
        Algebra vK.Completion
          (absoluteValueExtensionConjugate vK w σ).1.Completion :=
      AbsoluteValue.completionAlgebra vK
        (absoluteValueExtensionConjugate vK w σ).1
        (absoluteValueExtensionConjugate vK w σ).2
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    conjugateExtensionCompletionRingEquiv vK w σ
        (algebraMap vK.Completion
          (absoluteValueExtensionConjugate vK w σ).1.Completion b) =
      algebraMap vK.Completion w.1.Completion b := by
  let _ :
      Algebra vK.Completion
        (absoluteValueConjugate w.1 σ).Completion :=
    AbsoluteValue.completionAlgebra vK
      (absoluteValueConjugate w.1 σ)
      (absoluteValueConjugate_extends vK w σ)
  let _ : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  change
    conjugateCompletionRingEquiv w.1 σ
        (algebraMap vK.Completion
          (absoluteValueConjugate w.1 σ).Completion b) =
      algebraMap vK.Completion w.1.Completion b
  exact conjugateCompletionRingEquiv_algebraMap vK w σ b

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_AbsoluteValue
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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

omit [NumberField K] [NumberField L] in
/-- An element of an extension-completion valuation ring is integral
over the valuation ring in the base completion.  This is the
integral-closure characterization for complete henselian valued
fields, expressed in the absolute-value completion model used by
the canonical local tensor decomposition. -/
theorem isIntegral_over_baseCompletionIntegers_of_mem
    [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ))
    (hvK0 : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    {x : w.1.Completion}
    (hx : x ∈ absoluteValueCompletionIntegers w.1
      (absoluteValueExtension_isNonarchimedean vK hvK w)) :
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    IsIntegral (absoluteValueCompletionIntegers vK hvK) x := by
  let hw : IsNonarchimedean (w.1 : L → ℝ) :=
    absoluteValueExtension_isNonarchimedean vK hvK w
  let aC := AbsoluteValue.completionAbsoluteValue vK
  let bC := AbsoluteValue.completionAbsoluteValue w.1
  let haC : LubinTate.Valuations.NonarchimedeanAbsoluteValue aC :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat aC).1
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean vK hvK)
  let hbC : LubinTate.Valuations.NonarchimedeanAbsoluteValue bC :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat bC).1
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean w.1 hw)
  let va :=
    absoluteValueExponentialValuation aC haC
  let vb :=
    absoluteValueExponentialValuation bC hbC
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Module.Finite vK.Completion w.1.Completion :=
    completionModuleFinite vK hvK0 w
  let : Algebra.IsAlgebraic vK.Completion w.1.Completion :=
    Algebra.IsAlgebraic.of_finite vK.Completion w.1.Completion
  have hVaAbs :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring va =
        absoluteValueValuationSubring aC haC :=
    associatedAbsoluteValue_valuationSubring_eq
      va (Real.exp 1) aC haC
        (absoluteValueExponentialValuation_associated aC haC)
  have hVbAbs :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vb =
        absoluteValueValuationSubring bC hbC :=
    associatedAbsoluteValue_valuationSubring_eq
      vb (Real.exp 1) bC hbC
        (absoluteValueExponentialValuation_associated bC hbC)
  have hVa :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring va =
        absoluteValueCompletionIntegers vK hvK := by
    rw [hVaAbs]
    ext y
    rw [mem_absoluteValueValuationSubring_iff,
      mem_absoluteValueCompletionIntegers_iff]
    rfl
  have hVb :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vb =
        absoluteValueCompletionIntegers w.1 hw := by
    rw [hVbAbs]
    ext y
    rw [mem_absoluteValueValuationSubring_iff,
      mem_absoluteValueCompletionIntegers_iff]
    rfl
  have hhensAbs :
      ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (absoluteValueValuationSubring aC haC).valuation :=
    henselianValuation_of_complete aC
      ((absoluteValueCompleteness_completeSpace_withAbs_iff_complete aC).1
        (AbsoluteValue.completionAbsoluteValue_complete vK))
      haC
  have hhens :
      ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
          va).valuation := by
    rw [hVaAbs]
    exact hhensAbs
  have hExt :
      ∀ y : vK.Completion,
        bC (algebraMap vK.Completion w.1.Completion y) = aC y :=
    AbsoluteValue.completionAbsoluteValue_extends vK w.1 w.2
  have hclosure :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      va vb
      (absoluteValueExponentialValuation_extends
        aC bC haC hbC hExt)
      hhens
  rw [hVa, hVb] at hclosure
  rw [← mem_integralClosure_iff]
  change x ∈
    (integralClosure
      (absoluteValueCompletionIntegers vK hvK) w.1.Completion).toSubring
  rw [← hclosure]
  exact hx
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Every scaled basis vector belongs to the valuation ring of every
nonarchimedean extension of an absolute value of `K`. -/
theorem scaledRelativeExtensionBasis_absoluteValue_le_one
    (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ))
    (wL : AbsoluteValueExtension vK L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    wL.1
      (scaledRelativeExtensionBasis
        (K := K) (L := L) i) ≤ 1 :=
  absoluteValue_le_one_of_isIntegral
    wL.1
    (absoluteValueExtension_isNonarchimedean
      vK hvK wL)
    (scaledRelativeExtensionBasis_isIntegral
      (K := K) (L := L) i)

/-- The integral scale remains nonzero in the ring of integers. -/
theorem relativeBasisIntegralScaleInRingOfIntegers_ne_zero :
    relativeBasisIntegralScaleInRingOfIntegers
      (K := K) (L := L) ≠ 0 := by
  intro h
  have hc :
      (chosenRelativeBasisIntegralScale
        (K := K) (L := L) : 𝓞 K) =
        ((0 : ℤ) : 𝓞 K) := by
    simpa [relativeBasisIntegralScaleInRingOfIntegers] using h
  exact
    chosenRelativeBasisIntegralScale_ne_zero
      (K := K) (L := L)
      (Int.cast_injective hc)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_FinitePlaceCompletion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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

omit [NumberField K] [NumberField L] in
/-- Trace in the canonical local tensor algebra preserves integrality
when all completed-field components are integral. -/
theorem isIntegral_trace_tensor_of_components
    [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ))
    (hvK0 : vK.IsNontrivial)
    (x : vK.Completion ⊗[K] L)
    (hx : ∀ w : AbsoluteValueExtension vK L,
      completionTensorDecomposition_left
          (K := K) (L := L) vK hvK0 x w ∈
        absoluteValueCompletionIntegers w.1
          (absoluteValueExtension_isNonarchimedean vK hvK w)) :
    IsIntegral (absoluteValueCompletionIntegers vK hvK)
      (Algebra.trace vK.Completion
        (vK.Completion ⊗[K] L) x) := by
  classical
  let : Fintype (AbsoluteValueExtension vK L) :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK0
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w => AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w => completionModuleFinite vK hvK0 w
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Free vK.Completion w.1.Completion :=
    fun w => Module.Free.of_divisionRing
      vK.Completion w.1.Completion
  let y :
      ∀ w : AbsoluteValueExtension vK L, w.1.Completion :=
    completionTensorDecomposition_left
      (K := K) (L := L) vK hvK0 x
  have hy :
      ∀ w : AbsoluteValueExtension vK L,
        IsIntegral (absoluteValueCompletionIntegers vK hvK) (y w) := by
    intro w
    exact isIntegral_over_baseCompletionIntegers_of_mem
      (K := K) (L := L) vK hvK hvK0 w (hx w)
  have hsum :
      IsIntegral (absoluteValueCompletionIntegers vK hvK)
        (∑ w : AbsoluteValueExtension vK L,
          Algebra.trace vK.Completion w.1.Completion (y w)) := by
    apply IsIntegral.sum
    intro w _
    exact Algebra.isIntegral_trace (hy w)
  rw [← ValuationTheory.Completion.algebra_trace_pi_apply
    (fun w : AbsoluteValueExtension vK L => w.1.Completion) y] at hsum
  rw [Algebra.trace_eq_of_algEquiv
    (completionTensorDecomposition_left
      (K := K) (L := L) vK hvK0) x] at hsum
  exact hsum
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_RestrictedAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassEquivFixed_coe _root_.RelativeIdeleGroup.Cohomology.baseIdeleClassToFixed_coe _root_.RelativeIdeleGroup.Cohomology.ideleClassNorm_mk _root_.RelativeIdeleGroup.Cohomology.ideleClass_smul_mk _root_.RelativeIdeleGroup.Cohomology.relativeIdele_smul_def _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.RelativeIdeleGroup.smul_class_mk _root_.TowerRelativeIdeleGroup.classGroupEquiv_mk _root_.TowerRelativeIdeleGroup.classNorm_mk _root_.TowerRelativeIdeleGroup.norm_principalIdele _root_.TowerRelativeIdeleGroup.towerRelativeIdeleEquiv_principalIdele _root_.bottomAdeleToTower_apply _root_.compositeToBaseNormQuotient_mk _root_.fieldUnitsEquivPrincipalIdeles_coe _root_.intermediateAdeleInclusion_tmul _root_.intermediateToCompositeNormQuotient_mk _root_.pushoutNormQuotientMap_mk _root_.pushoutNormQuotientNormBack_mk _root_.pushoutTowerAdeleInclusion_tmul _root_.pushoutTowerClassInclusion_mk _root_.pushoutTowerIdeleInclusion_principalIdele _root_.topFieldToOneStep_apply _root_.topFieldToTower_apply _root_.towerRelativeAdeleFlatten_tmul _root_.towerRelativeAdeleUnflatten_tmul
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

/-- The natural action on relative ideles, upgraded to an action by
group automorphisms for the restricted-product comparison. -/
@[reducible]
noncomputable def relativeIdeleRestrictedMulDistribMulAction :
    MulDistribMulAction
      (L ≃ₐ[K] L) (RelativeIdeleGroup K L) where
  __ := RelativeIdeleGroup.relativeIdeleMulAction K L
  smul_one σ :=
    map_one
      (RelativeIdeleGroup.conjugationIdele K L σ)
  smul_mul σ a b :=
    map_mul
      (RelativeIdeleGroup.conjugationIdele K L σ) a b

omit [NumberField L] [FiniteDimensional K L] in
/-- Finite-place evaluation commutes with Galois conjugation. -/
theorem relativeAdeleFiniteComponent_conjugation
    (w : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (z : RelativeAdeleRing K L) :
    relativeAdeleFiniteComponent
        (K := K) (L := L) w
        (RelativeIdeleGroup.conjugation K L σ z) =
      scalarTensorConjugation
        (K := K) (L := L)
        (A := w.adicCompletion K) σ
        (relativeAdeleFiniteComponent
          (K := K) (L := L) w z) := by
  induction z using OAI.tensorInductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp [hx, hy]

omit [NumberField L] [FiniteDimensional K L] in
/-- The finite local unit component map is equivariant. -/
theorem RelativeIdeleGroup.finiteComponent_smul
    (w : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (z : RelativeIdeleGroup K L) :
    letI := scalarTensorUnitsAction
      (K := K) (L := L)
      (A := w.adicCompletion K)
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w (σ • z) =
      σ • RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z := by
  let _ := scalarTensorUnitsAction
    (K := K) (L := L)
    (A := w.adicCompletion K)
  apply Units.ext
  exact relativeAdeleFiniteComponent_conjugation
    (K := K) (L := L) w σ
      (z : RelativeAdeleRing K L)

/-- The Galois action on the restricted local product transported
through the exact relative-idele equivalence. -/
@[reducible]
noncomputable def relativeLocalIdeleDataMulDistribMulAction :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (RelativeLocalIdeleData
        (K := K) (L := L)) := by
  letI : MulDistribMulAction
      (L ≃ₐ[K] L) (RelativeIdeleGroup K L) :=
    relativeIdeleRestrictedMulDistribMulAction
      (K := K) (L := L)
  let e :=
    relativeIdeleMulEquivLocalData
      (K := K) (L := L)
  exact
    { smul := fun σ a => e (σ • e.symm a)
      one_smul := by
        intro a
        change e (1 • e.symm a) = a
        rw [one_smul, e.apply_symm_apply]
      mul_smul := by
        intro σ τ a
        change
          e ((σ * τ) • e.symm a) =
            e (σ • e.symm (e (τ • e.symm a)))
        rw [e.symm_apply_apply, mul_smul]
      smul_one := by
        intro σ
        change e (σ • e.symm 1) = 1
        rw [e.symm.map_one, smul_one, e.map_one]
      smul_mul := by
        intro σ a b
        change
          e (σ • e.symm (a * b)) =
            e (σ • e.symm a) *
              e (σ • e.symm b)
        rw [e.symm.map_mul,
          MulDistribMulAction.smul_mul, e.map_mul] }
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_SPlaces
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place support for relative ideles

This file packages a restricted-product assertion for relative ideles. At
every finite place outside a finite
set, a relative idele belongs to the actual product of valuation-ring
unit groups supplied by the completion decomposition. The resulting supported
subgroups are stable under the Galois action and exhaust the full
relative idele group.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open CyclicCohomology


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] [IsGalois K L] in
/-- Membership in the chosen basis lattice is exactly the coefficient
integrality needed by the restricted local-product model. -/
theorem relativeBasisIntegralAt_repr_mem
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L)
    (hx : RelativeBasisIntegralAt
      (K := K) (L := L) w x)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    (Algebra.TensorProduct.basis
        (w.adicCompletion K)
        (relativeExtensionBasis
          (K := K) (L := L))).repr x i ∈
      w.adicCompletionIntegers K := by
  classical
  rcases hx with ⟨c, rfl⟩
  simp
  rw [Finset.sum_eq_single i]
  · simpa only [Finsupp.single_eq_same] using (c i).property
  · intro j _ hji
    simp [hji]
  · simp
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_FiniteRestrictedProductBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- The finite part of the relative restricted local product.  This is
the source model whose flattening is the ordinary finite idele group of
`L`. -/
structure RelativeFiniteIdeleData where
  /-- The unit in each finite local tensor factor. -/
  finite :
    ∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ
  /-- Every basis coordinate of the finite component is integral at
  all but finitely many places. -/
  eventually_integral :
    ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (finite w : w.adicCompletion K ⊗[K] L) i ∈
          w.adicCompletionIntegers K
  /-- Every basis coordinate of the inverse finite component is integral
  at all but finitely many places. -/
  eventually_inverse_integral :
    ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (↑((finite w)⁻¹) :
              w.adicCompletion K ⊗[K] L) i ∈
          w.adicCompletionIntegers K
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_InfinitePlaceTensorBlock
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

/-- Base change of the first tensor factor from the concrete
archimedean completion to the absolute-value completion. -/
noncomputable def infinitePlaceLocalTensorAlgEquiv
    (w : InfinitePlace K) :
    w.Completion ⊗[K] L ≃ₐ[K]
      LocalTensorAlgebra (L := L) w.1 :=
  Algebra.TensorProduct.congr
    (infinitePlaceCompletionAlgEquiv w)
    (AlgEquiv.refl : L ≃ₐ[K] L)

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- The concrete-to-absolute completion comparison acts componentwise
on a pure tensor. -/
@[simp]
theorem infinitePlaceLocalTensorAlgEquiv_tmul
    (w : InfinitePlace K) (a : w.Completion) (x : L) :
    infinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) w (a ⊗ₜ[K] x) =
      infinitePlaceCompletionAlgEquiv w a ⊗ₜ[K] x := by
  rfl

/-- The induced multiplicative equivalence on local tensor units. -/
noncomputable def infinitePlaceLocalTensorUnitsEquiv
    (w : InfinitePlace K) :
    (w.Completion ⊗[K] L)ˣ ≃*
      (LocalTensorAlgebra (L := L) w.1)ˣ :=
  Units.mapEquiv
    (infinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w).toMulEquiv
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_IdealClass
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Extension of ideles and ideal classes

For a finite Galois extension of number fields, scalar extension of the
relative adele algebra followed by the relative-to-ordinary comparison
gives the usual extension map on ideles.  This file descends that map to
idele classes and compares it with extension of fractional ideals and
ideal classes.
-/

open scoped NumberField TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v w

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

namespace FractionalIdealGroup

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Extension of a prime fractional ideal commutes with passage to the
ideal class group. -/
@[simp]
theorem classGroup_mk_extension_prime
    (w : HeightOneSpectrum (𝓞 K)) :
    ClassGroup.mk L (extension K L (prime w)) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (ClassGroup.mk K (prime w)) := by
  let w₀ : (Ideal (𝓞 K))⁰ :=
    ⟨w.asIdeal,
      mem_nonZeroDivisors_iff_ne_zero.mpr w.ne_bot⟩
  have hw :
      prime w = FractionalIdeal.mk0 K w₀ := by
    apply Units.ext
    rfl
  rw [hw, ClassGroup.mk_mk0,
    ClassGroup.extendedHom_mk0]
  rw [← ClassGroup.mk_mk0 L
    (ClassGroup.extendedIdeal (𝓞 K) (𝓞 L) w₀)]
  apply congrArg (ClassGroup.mk L)
  apply Units.ext
  exact extension_prime_val K L w

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Extension of arbitrary fractional ideals commutes with passage to
the ideal class group. -/
@[simp]
theorem classGroup_mk_extension
    (I : FractionalIdealGroup K) :
    ClassGroup.mk L (extension K L I) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (ClassGroup.mk K I) := by
  obtain ⟨exps, rfl⟩ :=
    factorization_surjective (K := K) I
  change
    ((ClassGroup.mk L).comp (extension K L))
        (factorization exps) =
      ((ClassGroup.extendedHom (𝓞 K) (𝓞 L)).comp
        (ClassGroup.mk K)) (factorization exps)
  rw [factorization, MonoidHom.mk'_apply, Finsupp.prod]
  simp only [map_prod, primePowerHom, MonoidHom.mk'_apply,
    toAdd_ofAdd, MonoidHom.comp_apply, map_zpow,
    classGroup_mk_extension_prime]

end FractionalIdealGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_FinitePlace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition groups and complete splitting at finite places

For a finite Galois extension of number fields `L / K`, this file
attaches an actual decomposition subgroup to every finite place of
`K`.  The extension of the adic absolute value is the one constructed
in `LocalNormApproximation`; no place above `v` is supplied as an
additional hypothesis.

The stabilizer is identified with the automorphism group of the algebraic
localization. The finite-localization theorem supplies finite dimensionality,
so the order of
the decomposition group is exactly the local degree.  Consequently
complete splitting is equivalent both to cardinality one and to local
degree one.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- A finite place splits completely when its chosen decomposition
subgroup is trivial.  Conjugacy of extensions makes this independent
of the chosen extension, but the chosen representative gives a
concrete subgroup for subsequent constructions. -/
def FinitePlaceSplitsCompletely
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  finitePlaceDecompositionGroup
    (K := K) (L := L) v = ⊥
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitSubgroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Power-local-unit subgroups of the idele group

This module defines the subgroup of ideles that are local powers at selected
places and integral units elsewhere, together with its intersection with
principal ideles and the corresponding subgroup of S-unit powers.
-/

open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type*} [Field K] [NumberField K]

/-- Ideles that are local `n`-th powers at the prescribed places and
integral units away from `S ∪ T`. -/
def idelePowerLocalUnitSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (IdeleGroup K) :=
  (⨅ w : InfinitePlace K,
      ((powMonoidHom (n : ℕ) :
        w.Completionˣ →* w.Completionˣ).range).comap
        (IdeleGroup.infiniteComponent w)) ⊓
    (⨅ v : HeightOneSpectrum (𝓞 K),
      ⨅ (_ : v ∈ S),
        (powMonoidHom (n : ℕ) :
          (v.adicCompletion K)ˣ →*
            (v.adicCompletion K)ˣ).range.comap
          (IdeleGroup.finiteComponent v)) ⊓
    (⨅ v : HeightOneSpectrum (𝓞 K),
      ⨅ (_ : v ∉ S ∪ T),
        (v.adicCompletionIntegers K).units.comap
          (IdeleGroup.finiteComponent v))

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply
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

namespace LocalField

variable {K : Type u} [Field K]

/-- The residue characteristic belongs to the maximal ideal of the valuation
ring. -/
theorem residueCharacteristic_natCast_mem_maximalIdeal
    (F : LocalField.{u, v} K) :
    (F.residueCharacteristic : F.valuationSubring) ∈ F.maximalIdeal :=
  (F.toCompleteDVF.residue_eq_zero_iff
    (F.residueCharacteristic : F.valuationSubring)).1
    F.residueCharacteristic_natCast_residue_eq_zero

/-- Valuatively, the residue characteristic lies in the open unit ball. -/
theorem valuation_residueCharacteristic_natCast_lt_one
    (F : LocalField.{u, v} K) :
    F.toCompleteDVF.valuation
      ((F.residueCharacteristic : F.valuationSubring) : K) < 1 :=
  (F.toCompleteDVF.mem_maximalIdeal_iff
    (F.residueCharacteristic : F.valuationSubring)).1
    F.residueCharacteristic_natCast_mem_maximalIdeal

/-- Field-level form of the previous valuation estimate. -/
theorem valuation_natCast_residueCharacteristic_lt_one
    (F : LocalField.{u, v} K) :
    F.toCompleteDVF.valuation (F.residueCharacteristic : K) < 1 := by
  have hcast :
      ((F.residueCharacteristic : F.valuationSubring) : K) =
        (F.residueCharacteristic : K) := by
    exact map_natCast F.toCompleteDVF.valuation.valuationSubring.subtype
      F.residueCharacteristic
  rw [← hcast]
  exact F.valuation_residueCharacteristic_natCast_lt_one

/-- For an arbitrary integer, membership in the maximal ideal is exactly
divisibility by the residue characteristic. -/
theorem intCast_mem_maximalIdeal_iff_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (z : ℤ) :
    (z : F.valuationSubring) ∈ F.maximalIdeal ↔
      (F.residueCharacteristic : ℤ) ∣ z := by
  rw [← F.toCompleteDVF.residue_eq_zero_iff (z : F.valuationSubring)]
  rw [map_intCast]
  exact
    CharP.intCast_eq_zero_iff
      (R := F.residueField) F.residueCharacteristic z

/-- Natural-number version of
`intCast_mem_maximalIdeal_iff_residueCharacteristic_dvd`. -/
theorem natCast_mem_maximalIdeal_iff_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (n : ℕ) :
    (n : F.valuationSubring) ∈ F.maximalIdeal ↔
      F.residueCharacteristic ∣ n := by
  rw [← F.toCompleteDVF.residue_eq_zero_iff (n : F.valuationSubring)]
  rw [map_natCast]
  exact ringChar.spec (R := F.residueField) n

/-- Integer-valued maximal-ideal membership as a valuation inequality. -/
theorem valuationSubring_intCast_lt_one_iff_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (z : ℤ) :
    F.toCompleteDVF.valuation ((z : F.valuationSubring) : K) < 1 ↔
      (F.residueCharacteristic : ℤ) ∣ z :=
  (F.toCompleteDVF.mem_maximalIdeal_iff
    (z : F.valuationSubring)).symm.trans
    (F.intCast_mem_maximalIdeal_iff_residueCharacteristic_dvd z)

/-- Natural-number-valued maximal-ideal membership as a valuation inequality. -/
theorem valuationSubring_natCast_lt_one_iff_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (n : ℕ) :
    F.toCompleteDVF.valuation ((n : F.valuationSubring) : K) < 1 ↔
      F.residueCharacteristic ∣ n :=
  (F.toCompleteDVF.mem_maximalIdeal_iff
    (n : F.valuationSubring)).symm.trans
    (F.natCast_mem_maximalIdeal_iff_residueCharacteristic_dvd n)

/-- An integer prime to the residue characteristic has valuation one. -/
theorem valuationSubring_intCast_eq_one_of_not_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) {z : ℤ}
    (hz : ¬ (F.residueCharacteristic : ℤ) ∣ z) :
    F.toCompleteDVF.valuation ((z : F.valuationSubring) : K) = 1 := by
  have hle :
      F.toCompleteDVF.valuation ((z : F.valuationSubring) : K) ≤ 1 :=
    (F.toCompleteDVF.mem_valuationSubring_iff
      ((z : F.valuationSubring) : K)).1
      (z : F.valuationSubring).property
  have hnlt :
      ¬ F.toCompleteDVF.valuation ((z : F.valuationSubring) : K) < 1 := by
    intro hlt
    exact hz
      ((F.valuationSubring_intCast_lt_one_iff_residueCharacteristic_dvd z).1 hlt)
  exact le_antisymm hle (le_of_not_gt hnlt)

/-- A natural number prime to the residue characteristic has valuation one. -/
theorem valuationSubring_natCast_eq_one_of_not_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) {n : ℕ}
    (hn : ¬ F.residueCharacteristic ∣ n) :
    F.toCompleteDVF.valuation ((n : F.valuationSubring) : K) = 1 := by
  have hle :
      F.toCompleteDVF.valuation ((n : F.valuationSubring) : K) ≤ 1 :=
    (F.toCompleteDVF.mem_valuationSubring_iff
      ((n : F.valuationSubring) : K)).1
      (n : F.valuationSubring).property
  have hnlt :
      ¬ F.toCompleteDVF.valuation ((n : F.valuationSubring) : K) < 1 := by
    intro hlt
    exact hn
      ((F.valuationSubring_natCast_lt_one_iff_residueCharacteristic_dvd n).1 hlt)
  exact le_antisymm hle (le_of_not_gt hnlt)

/-- Field-level natural-number valuation criterion for the residue
characteristic. -/
theorem valuation_natCast_lt_one_iff_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) (n : ℕ) :
    F.toCompleteDVF.valuation (n : K) < 1 ↔
      F.residueCharacteristic ∣ n := by
  have hcast :
      ((n : F.valuationSubring) : K) = (n : K) := by
    exact map_natCast F.toCompleteDVF.valuation.valuationSubring.subtype n
  rw [← hcast]
  exact F.valuationSubring_natCast_lt_one_iff_residueCharacteristic_dvd n

/-- Field-level integer valuation-one criterion away from the residue
characteristic. -/
theorem valuation_intCast_eq_one_of_not_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) {z : ℤ}
    (hz : ¬ (F.residueCharacteristic : ℤ) ∣ z) :
    F.toCompleteDVF.valuation (z : K) = 1 := by
  have hcast :
      ((z : F.valuationSubring) : K) = (z : K) := by
    exact map_intCast F.toCompleteDVF.valuation.valuationSubring.subtype z
  rw [← hcast]
  exact F.valuationSubring_intCast_eq_one_of_not_residueCharacteristic_dvd hz

/-- Field-level natural-number valuation-one criterion away from the residue
characteristic. -/
theorem valuation_natCast_eq_one_of_not_residueCharacteristic_dvd
    (F : LocalField.{u, v} K) {n : ℕ}
    (hn : ¬ F.residueCharacteristic ∣ n) :
    F.toCompleteDVF.valuation (n : K) = 1 := by
  have hcast :
      ((n : F.valuationSubring) : K) = (n : K) := by
    exact map_natCast F.toCompleteDVF.valuation.valuationSubring.subtype n
  rw [← hcast]
  exact F.valuationSubring_natCast_eq_one_of_not_residueCharacteristic_dvd hn

/-- If the denominator of a rational number is prime to the residue
characteristic, then its valuation is the valuation of its numerator. -/
theorem valuation_ratCast_eq_intCast_of_not_residueCharacteristic_dvd_den
    (F : LocalField.{u, v} K) (q : ℚ)
    (hden : ¬ F.residueCharacteristic ∣ q.den) :
    F.toCompleteDVF.valuation (q : K) =
      F.toCompleteDVF.valuation (q.num : K) := by
  calc
    F.toCompleteDVF.valuation (q : K)
        = F.toCompleteDVF.valuation ((q.num : K) / (q.den : K)) := by
          rw [Rat.cast_def]
    _ = F.toCompleteDVF.valuation (q.num : K) /
        F.toCompleteDVF.valuation (q.den : K) := by
          exact F.toCompleteDVF.valuation.map_div (q.num : K) (q.den : K)
    _ = F.toCompleteDVF.valuation (q.num : K) / 1 := by
          rw [F.valuation_natCast_eq_one_of_not_residueCharacteristic_dvd hden]
    _ = F.toCompleteDVF.valuation (q.num : K) := by
          simp

/-- A rational number with denominator prime to the residue characteristic lies
in the valuation subring.  This is the local `ℤ_(p)` input for the converse
classification in the local-field structure theory, the local-field structure classification. -/
theorem valuation_ratCast_le_one_of_not_residueCharacteristic_dvd_den
    (F : LocalField.{u, v} K) (q : ℚ)
    (hden : ¬ F.residueCharacteristic ∣ q.den) :
    F.toCompleteDVF.valuation (q : K) ≤ 1 := by
  rw [F.valuation_ratCast_eq_intCast_of_not_residueCharacteristic_dvd_den q hden]
  exact F.valuation_intCast_le_one q.num

/-- For mixed-characteristic local fields, the rational numbers lying in the
valuation subring are exactly those whose denominator is prime to the residue
characteristic. -/
theorem valuation_ratCast_le_one_iff_not_residueCharacteristic_dvd_den
    (F : LocalField.{u, v} K) [CharZero K] (q : ℚ) :
    F.toCompleteDVF.valuation (q : K) ≤ 1 ↔
      ¬ F.residueCharacteristic ∣ q.den := by
  constructor
  · intro hle hden
    have hnumNot :
        ¬ (F.residueCharacteristic : ℤ) ∣ q.num :=
      F.not_residueCharacteristic_dvd_rat_num_of_dvd_den q hden
    have hnumVal :
        F.toCompleteDVF.valuation (q.num : K) = 1 :=
      F.valuation_intCast_eq_one_of_not_residueCharacteristic_dvd hnumNot
    have hdenValLt :
        F.toCompleteDVF.valuation (q.den : K) < 1 :=
      (F.valuation_natCast_lt_one_iff_residueCharacteristic_dvd q.den).2 hden
    have hdenNe : (q.den : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr q.den_ne_zero
    have hdenValPos :
        0 < F.toCompleteDVF.valuation (q.den : K) :=
      F.toCompleteDVF.valuation.pos_iff.2 hdenNe
    have hqVal :
        F.toCompleteDVF.valuation (q : K) =
          F.toCompleteDVF.valuation (q.num : K) /
            F.toCompleteDVF.valuation (q.den : K) := by
      calc
        F.toCompleteDVF.valuation (q : K)
            = F.toCompleteDVF.valuation ((q.num : K) / (q.den : K)) := by
              rw [Rat.cast_def]
        _ = F.toCompleteDVF.valuation (q.num : K) /
            F.toCompleteDVF.valuation (q.den : K) := by
              exact F.toCompleteDVF.valuation.map_div (q.num : K) (q.den : K)
    have hgt : 1 < F.toCompleteDVF.valuation (q : K) := by
      rw [hqVal, hnumVal]
      simpa [one_div] using (one_lt_inv₀ hdenValPos).2 hdenValLt
    exact (not_lt_of_ge hle) hgt
  · exact F.valuation_ratCast_le_one_of_not_residueCharacteristic_dvd_den q

/-- The restriction of the local-field valuation to `ℚ` has the same valuation
subring as the `p`-adic valuation, where `p` is the residue characteristic. -/
theorem valuation_ratCast_le_one_iff_padicValuation_le_one
    (F : LocalField.{u, v} K) [CharZero K] (q : ℚ) :
    F.toCompleteDVF.valuation (q : K) ≤ 1 ↔
      Rat.padicValuation F.residueCharacteristic q ≤ 1 :=
  (F.valuation_ratCast_le_one_iff_not_residueCharacteristic_dvd_den q).trans
    (Rat.padicValuation_le_one_iff
      (p := F.residueCharacteristic) (x := q)).symm

end LocalField
end LocalFieldTheory.DiscreteValuationField
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_EqualCharacteristicLaurent
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Equal-characteristic Laurent-series input for the local-field structure classification

This file starts the equal-characteristic branch of the local-field structure classification, the local-field structure classification.  Given the Teichmuller coefficient-field section
`κ -> O_K -> K` and a uniformizer `π`, it constructs the induced evaluation
map `κ((X)) -> K` by first evaluating `κ⟦X⟧` at `X = π`, then using the
localization description `κ((X)) = κ⟦X⟧[X⁻¹]`.
-/

noncomputable section

universe u v

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF

open scoped PowerSeries LaurentSeries Filter Topology BigOperators
open Filter

variable {K : Type u} [Field K]
variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

namespace EqualCharacteristicLaurent

/-- The maximal-ideal adic topology on the valuation ring is linear. -/
theorem valuationSubring_isLinearTopology_adic :
    letI : TopologicalSpace F.valuationSubring := F.maximalIdeal.adicTopology
    IsLinearTopology F.valuationSubring F.valuationSubring := by
  let : TopologicalSpace F.valuationSubring := F.maximalIdeal.adicTopology
  exact
    IsLinearTopology.mk_of_hasBasis F.valuationSubring
      (Ideal.hasBasis_nhds_zero_adic F.maximalIdeal)

/-- The `WithIdeal` adic topology on the valuation ring is linear. -/
theorem valuationSubring_isLinearTopology_withIdeal :
    letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
    IsLinearTopology F.valuationSubring F.valuationSubring := by
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  exact valuationSubring_isLinearTopology_adic (F := F)

/-- The valuation ring is complete for its maximal-ideal adic topology. -/
theorem valuationSubring_completeSpace_withIdeal :
    letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
    CompleteSpace F.valuationSubring := by
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  have hadic : IsAdic F.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp F.isAdicComplete).1

/-- The valuation ring is Hausdorff for its maximal-ideal adic topology. -/
theorem valuationSubring_t2Space_withIdeal :
    letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
    T2Space F.valuationSubring := by
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  have hadic : IsAdic F.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp F.isAdicComplete).2

/-- The adic Laurent-series evaluation with all topology instances supplied
from the complete-DVF structure. -/
noncomputable def adicLaurentSeriesEvalHom
    [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K)) :
    F.residueField⸨X⸩ →+* K := by
  letI : UniformSpace F.residueField := ⊥
  haveI : DiscreteUniformity F.residueField := inferInstance
  haveI : IsUniformAddGroup F.residueField :=
    inferInstance
  letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  haveI : IsLinearTopology F.valuationSubring F.valuationSubring :=
    valuationSubring_isLinearTopology_withIdeal (F := F)
  haveI : CompleteSpace F.valuationSubring :=
    valuationSubring_completeSpace_withIdeal (F := F)
  haveI : T2Space F.valuationSubring :=
    valuationSubring_t2Space_withIdeal (F := F)
  exact
    laurentSeriesEvalHom (F := F) p hcard π hπ
      (continuous_coeffSubringHom_of_discrete (F := F) p hcard)
      (uniformizer_hasEval_valuationSubring_withIdeal (F := F) hπ)

end EqualCharacteristicLaurent
end CompleteDVF

namespace LocalField

open scoped PowerSeries LaurentSeries Filter Topology BigOperators

variable {K : Type u} [Field K]
variable (F : LocalField.{u, v} K)

/-- The image in `K` of the equal-characteristic Laurent-series evaluation.
This is the candidate base field for the converse direction of the local-field structure classification. -/
noncomputable def laurentImageSubfield
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    Subfield K :=
  (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom
    (F := F.toCompleteDVF) p hcard π hπ).fieldRange

/-- The Laurent-series field is identified with its image in `K`. -/
noncomputable def laurentSeriesEquivLaurentImageSubfield
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    F.residueField⸨X⸩ ≃+*
      F.laurentImageSubfield p hcard π hπ :=
  RingHom.rangeRestrictFieldEquiv
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom
      (F := F.toCompleteDVF) p hcard π hπ)

/--
Establishes the identity `((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ x :
F.laurentImageSubfield p hcard π hπ) : K) =
CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom (F := F.toCompleteDVF) p hcard π
hπ x`.
-/
@[simp] theorem laurentSeriesEquivLaurentImageSubfield_apply_coe
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (x : F.residueField⸨X⸩) :
    ((F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ x :
        F.laurentImageSubfield p hcard π hπ) : K) =
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom
        (F := F.toCompleteDVF) p hcard π hπ x := by
  rfl

/-- The actual Laurent-series base acts on `K` through the image subfield. -/
@[reducible] noncomputable def laurentSeriesAlgebra
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    Algebra F.residueField⸨X⸩ K :=
  RingHom.toAlgebra
    ((F.laurentImageSubfield p hcard π hπ).subtype.comp
      (F.laurentSeriesEquivLaurentImageSubfield p hcard π hπ :
        F.residueField⸨X⸩ →+*
          F.laurentImageSubfield p hcard π hπ))

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_AdicProdiscreteComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Adic and prodiscrete principal-unit models

The adic topology on first principal units agrees with the prodiscrete topology carried
by the inverse limit of finite quotient coordinates.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-- Additive topological form of
`adicPrincipalUnitsHomeomorphProdiscreteLimit`. -/
noncomputable def adicPrincipalUnitsContinuousAddEquivProdiscreteLimit
    (F : CompleteDVF.{u, v} K) :
    AdicPrincipalUnits F ≃ₜ+ PrincipalUnitProdiscreteLimit F :=
  ContinuousAddEquiv.mk'
    (adicPrincipalUnitsHomeomorphProdiscreteLimit F)
    (fun x y => by
      simpa only [adicPrincipalUnitsHomeomorphProdiscreteLimit_apply] using
        (adicPrincipalUnitsAddEquivProdiscreteLimit F).map_add x y)

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_FiniteQuotientPadicModule
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# P-adic modules on finite principal-unit quotients

Finite principal-unit quotients have the expected residue-characteristic exponent.
Reduction of p-adic integers therefore supplies canonical module structures, compatible with
the transition maps.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-! ## The finite-coordinate p-adic actions -/

/-- The type in `Finite (DiscretePrincipalUnitQuotient F.toCompleteDVF n)` is finite. -/
instance discretePrincipalUnitQuotientFinite
    (F : LocalField.{u, v} K) (n : ℕ) :
    Finite (DiscretePrincipalUnitQuotient F.toCompleteDVF n) :=
  Finite.of_injective
    (fun x : DiscretePrincipalUnitQuotient F.toCompleteDVF n => x.val)
    (DiscretePrincipalUnitQuotient.equiv F.toCompleteDVF n).injective

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_ProdiscretePadicModule
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The p-adic module on the prodiscrete principal-unit limit

Coordinatewise scalar multiplication makes the prodiscrete inverse limit a topological
module over the p-adic integers.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-! ## The inverse-limit module and transport to `U^1` -/

/--
Equips the target in `Module ℤ_[F.residueCharacteristic] (Additive
(Internal.principalUnitInverseLimitCarrier F.toCompleteDVF))` with the indicated module structure.
-/
noncomputable instance Internal.principalUnitInverseLimitCarrierPadicModule
    (F : LocalField.{u, v} K) :
    Module ℤ_[F.residueCharacteristic]
      (Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF)) :=
  Module.ofMinimalAxioms
    (fun (a : ℤ_[F.residueCharacteristic])
        (x y : Additive
          (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF)) => by
      apply Additive.toMul.injective
      apply Subtype.ext
      funext n
      let : Module ℤ_[F.residueCharacteristic]
          (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :=
        principalUnitQuotientCarrierPadicModule F n
      apply Additive.ofMul.injective
      change
        a • (Additive.ofMul ((Additive.toMul x).1 n) +
          Additive.ofMul ((Additive.toMul y).1 n)) =
        a • Additive.ofMul ((Additive.toMul x).1 n) +
          a • Additive.ofMul ((Additive.toMul y).1 n)
      exact (principalUnitQuotientCarrierPadicModule F n).smul_add a
        (Additive.ofMul ((Additive.toMul x).1 n))
        (Additive.ofMul ((Additive.toMul y).1 n)))
    (fun (a b : ℤ_[F.residueCharacteristic])
        (x : Additive
          (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF)) => by
      apply Additive.toMul.injective
      apply Subtype.ext
      funext n
      let : Module ℤ_[F.residueCharacteristic]
          (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :=
        principalUnitQuotientCarrierPadicModule F n
      apply Additive.ofMul.injective
      change
        (a + b) • Additive.ofMul ((Additive.toMul x).1 n) =
          a • Additive.ofMul ((Additive.toMul x).1 n) +
            b • Additive.ofMul ((Additive.toMul x).1 n)
      exact (principalUnitQuotientCarrierPadicModule F n).add_smul a b
        (Additive.ofMul ((Additive.toMul x).1 n)))
    (fun (a b : ℤ_[F.residueCharacteristic])
        (x : Additive
          (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF)) => by
      apply Additive.toMul.injective
      apply Subtype.ext
      funext n
      let : Module ℤ_[F.residueCharacteristic]
          (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :=
        principalUnitQuotientCarrierPadicModule F n
      apply Additive.ofMul.injective
      change
        (a * b) • Additive.ofMul ((Additive.toMul x).1 n) =
          a • b • Additive.ofMul ((Additive.toMul x).1 n)
      exact (principalUnitQuotientCarrierPadicModule F n).mul_smul a b
        (Additive.ofMul ((Additive.toMul x).1 n)))
    (fun (x : Additive
        (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF)) => by
      apply Additive.toMul.injective
      apply Subtype.ext
      funext n
      let : Module ℤ_[F.residueCharacteristic]
          (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :=
        principalUnitQuotientCarrierPadicModule F n
      apply Additive.ofMul.injective
      change
        (1 : ℤ_[F.residueCharacteristic]) •
            Additive.ofMul ((Additive.toMul x).1 n) =
          Additive.ofMul ((Additive.toMul x).1 n)
      exact (principalUnitQuotientCarrierPadicModule F n).one_smul
        (Additive.ofMul ((Additive.toMul x).1 n)))

/--
Equips the target in `Module ℤ_[F.residueCharacteristic] (PrincipalUnitProdiscreteLimit
F.toCompleteDVF)` with the indicated module structure.
-/
noncomputable instance principalUnitProdiscreteLimitPadicModule
    (F : LocalField.{u, v} K) :
    Module ℤ_[F.residueCharacteristic]
      (PrincipalUnitProdiscreteLimit F.toCompleteDVF) :=
  AddEquiv.module
    (β := Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF))
    ℤ_[F.residueCharacteristic]
    (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF)

/--
Establishes the identity `PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF (a • x) = a •
PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF x`.
-/
@[simp]
theorem PrincipalUnitProdiscreteLimit.addEquiv_map_smul
    (F : LocalField.{u, v} K) (a : ℤ_[F.residueCharacteristic])
    (x : PrincipalUnitProdiscreteLimit F.toCompleteDVF) :
    PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF (a • x) =
      a • PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF x :=
  rfl

/--
Establishes the identity `PrincipalUnitProdiscreteLimit.coordinate F.toCompleteDVF n (a • x) = a •
PrincipalUnitProdiscreteLimit.coordinate F.toCompleteDVF n x`.
-/
@[simp] theorem PrincipalUnitProdiscreteLimit.coordinate_smul
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : ℤ_[F.residueCharacteristic])
    (x : PrincipalUnitProdiscreteLimit F.toCompleteDVF) :
    PrincipalUnitProdiscreteLimit.coordinate F.toCompleteDVF n (a • x) =
      a • PrincipalUnitProdiscreteLimit.coordinate F.toCompleteDVF n x := by
  apply (DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n).injective
  rw [DiscretePrincipalUnitQuotient.addEquiv_map_smul,
    PrincipalUnitProdiscreteLimit.coordinate_apply,
    PrincipalUnitProdiscreteLimit.coordinate_apply,
    DiscretePrincipalUnitQuotient.addEquiv_of,
    DiscretePrincipalUnitQuotient.addEquiv_of,
    PrincipalUnitProdiscreteLimit.addEquiv_map_smul]
  exact Internal.principalUnitInverseLimitCarrierPadic_smul_apply F a
    (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF x) n

/-- Addition on the type-level prodiscrete principal-unit limit is
continuous. -/
noncomputable instance principalUnitProdiscreteLimitContinuousAdd
    (F : LocalField.{u, v} K) :
    ContinuousAdd (PrincipalUnitProdiscreteLimit F.toCompleteDVF) := by
  let : (n : ℕ) → TopologicalSpace
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⊥
  let : (n : ℕ) → DiscreteTopology
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⟨rfl⟩
  let e := (PrincipalUnitProdiscreteLimit.homeomorph F.toCompleteDVF).trans
    (WithTopology.homeomorph
      (α := Additive
        (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF))
      (topology := principalUnitProdiscreteTopology F.toCompleteDVF))
  refine ⟨?_⟩
  have hlim : Continuous fun z :
      Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) ×
        Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
      z.1 + z.2 := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro n
    have hx : Continuous fun z :
        Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) ×
          Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
        (Additive.toMul z.1).1 n :=
      (continuous_apply n).comp
        (continuous_subtype_val.comp continuous_fst)
    have hy : Continuous fun z :
        Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) ×
          Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
        (Additive.toMul z.2).1 n :=
      (continuous_apply n).comp
        (continuous_subtype_val.comp continuous_snd)
    exact (continuous_of_discreteTopology : Continuous fun z :
      Internal.principalUnitQuotientCarrier F.toCompleteDVF n ×
        Internal.principalUnitQuotientCarrier F.toCompleteDVF n => z.1 * z.2).comp
      (hx.prodMk hy)
  have hpair : Continuous fun z :
      PrincipalUnitProdiscreteLimit F.toCompleteDVF ×
        PrincipalUnitProdiscreteLimit F.toCompleteDVF =>
      (e z.1, e z.2) :=
    (e.continuous.comp continuous_fst).prodMk
      (e.continuous.comp continuous_snd)
  have htransport := e.continuous_symm.comp (hlim.comp hpair)
  exact htransport

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_AdicPadicModule
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The p-adic module on adic principal units

The coordinatewise p-adic action is transported across the canonical adic/prodiscrete
comparison, producing its linear and topological forms on first principal units.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-- Transport the coordinatewise p-adic scalar multiplication from the
inverse limit to `U^1`. -/
noncomputable instance principalUnitPadicSMul
    (F : LocalField.{u, v} K) :
    SMul ℤ_[F.residueCharacteristic]
      (Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) where
  smul a x :=
    (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).symm
      (a • principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x)

/--
Establishes the identity `a • x = (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).symm
(a • principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x)`.
-/
@[simp] theorem principalUnitPadic_smul_def
    (F : LocalField.{u, v} K)
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) :
    a • x =
      (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).symm
        (a • principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x) :=
  rfl

/-- The standard `Z_p`-module structure on the first principal units of a
local field. -/
noncomputable instance principalUnitPadicModule
    (F : LocalField.{u, v} K) :
    Module ℤ_[F.residueCharacteristic]
      (Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) :=
  Module.ofMinimalAxioms
    (fun (a : ℤ_[F.residueCharacteristic])
        (x y : Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) => by
      apply (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).injective
      simp only [principalUnitPadic_smul_def, AddEquiv.apply_symm_apply,
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).map_add]
      exact (principalUnitInverseLimitCarrierPadicModule F).smul_add a
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x)
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF y))
    (fun (a b : ℤ_[F.residueCharacteristic])
        (x : Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) => by
      apply (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).injective
      simp only [principalUnitPadic_smul_def, AddEquiv.apply_symm_apply,
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).map_add]
      exact (principalUnitInverseLimitCarrierPadicModule F).add_smul a b
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x))
    (fun (a b : ℤ_[F.residueCharacteristic])
        (x : Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) => by
      apply (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).injective
      simp only [principalUnitPadic_smul_def, AddEquiv.apply_symm_apply]
      exact (principalUnitInverseLimitCarrierPadicModule F).mul_smul a b
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x))
    (fun (x : Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) => by
      apply (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).injective
      simp only [principalUnitPadic_smul_def, AddEquiv.apply_symm_apply]
      exact (principalUnitInverseLimitCarrierPadicModule F).one_smul
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x))

/--
Equips the target in `Module ℤ_[F.residueCharacteristic] (AdicPrincipalUnits F.toCompleteDVF)`
with the indicated module structure.
-/
noncomputable instance adicPrincipalUnitsPadicModule
    (F : LocalField.{u, v} K) :
    Module ℤ_[F.residueCharacteristic]
      (AdicPrincipalUnits F.toCompleteDVF) :=
  AddEquiv.module
    (β := Additive
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        F.toCompleteDVF) 1))
    ℤ_[F.residueCharacteristic]
    (AdicPrincipalUnits.addEquiv F.toCompleteDVF)

/--
Establishes the identity `AdicPrincipalUnits.addEquiv F.toCompleteDVF (a • x) = a •
AdicPrincipalUnits.addEquiv F.toCompleteDVF x`.
-/
@[simp]
theorem AdicPrincipalUnits.addEquiv_map_smul
    (F : LocalField.{u, v} K) (a : ℤ_[F.residueCharacteristic])
    (x : AdicPrincipalUnits F.toCompleteDVF) :
    AdicPrincipalUnits.addEquiv F.toCompleteDVF (a • x) =
      a • AdicPrincipalUnits.addEquiv F.toCompleteDVF x :=
  rfl

/-- The adic wrapper and its underlying principal-unit module are canonically
`Z_p`-linearly equivalent. -/
noncomputable def AdicPrincipalUnits.linearEquivUnderlying
    (F : LocalField.{u, v} K) :
    AdicPrincipalUnits F.toCompleteDVF ≃ₗ[ℤ_[F.residueCharacteristic]]
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF) 1) :=
  { AdicPrincipalUnits.addEquiv F.toCompleteDVF with
    map_smul' := AdicPrincipalUnits.addEquiv_map_smul F }

/--
Establishes the identity `principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF (a • x) = a •
principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x`.
-/
@[simp] theorem Internal.principalUnitAddEquivInverseLimitCarrier_map_smul
    (F : LocalField.{u, v} K)
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) :
    principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF (a • x) =
      a • principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x := by
  change
    principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF
        ((principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).symm
          (a • principalUnitAddEquivInverseLimitCarrier
            F.toCompleteDVF x)) =
      a • principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x
  exact (principalUnitAddEquivInverseLimitCarrier
    F.toCompleteDVF).apply_symm_apply _

/-- Coordinate formula for the canonical action: the class of `a • x` at
level `n` is obtained by reducing `a` modulo `p^(f*n)` and acting on the class
of `x`. -/
@[simp] theorem Internal.principalUnitPadic_smul_carrier_coordinate
    (F : LocalField.{u, v} K)
    (a : ℤ_[F.residueCharacteristic])
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1) (n : ℕ) :
    Additive.ofMul
        ((principalUnitMulEquivInverseLimitCarrier F.toCompleteDVF
          (Additive.toMul (a • Additive.ofMul x))).1 n) =
      principalUnitQuotientCarrierPadicScalar F n a
        (Additive.ofMul
          ((principalUnitMulEquivInverseLimitCarrier F.toCompleteDVF x).1 n)) := by
  rw [principalUnitQuotientCarrierPadicScalar_eq_smul]
  have h := congrArg
    (fun z : Additive
        (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
      Additive.ofMul ((Additive.toMul z).1 n))
      (principalUnitAddEquivInverseLimitCarrier_map_smul
      F a (Additive.ofMul x))
  exact h

/--
Establishes the identity `adicPrincipalUnitsAddEquivProdiscreteLimit F.toCompleteDVF (a • x) = a •
adicPrincipalUnitsAddEquivProdiscreteLimit F.toCompleteDVF x`.
-/
@[simp]
theorem adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul
    (F : LocalField.{u, v} K)
    (a : ℤ_[F.residueCharacteristic])
    (x : AdicPrincipalUnits F.toCompleteDVF) :
    adicPrincipalUnitsAddEquivProdiscreteLimit F.toCompleteDVF (a • x) =
      a • adicPrincipalUnitsAddEquivProdiscreteLimit F.toCompleteDVF x := by
  apply (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).injective
  change
    PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF
        ((PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).symm
          (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF
            (AdicPrincipalUnits.addEquiv F.toCompleteDVF (a • x)))) =
      PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF
        (a •
          (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).symm
            (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF
              (AdicPrincipalUnits.addEquiv F.toCompleteDVF x)))
  rw [(PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).apply_symm_apply,
    PrincipalUnitProdiscreteLimit.addEquiv_map_smul,
    (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).apply_symm_apply,
    AdicPrincipalUnits.addEquiv_map_smul,
    Internal.principalUnitAddEquivInverseLimitCarrier_map_smul]

/-- `Z_p`-linear form of the canonical adic/prodiscrete comparison. -/
noncomputable def adicPrincipalUnitsLinearEquivProdiscreteLimit
    (F : LocalField.{u, v} K) :
    AdicPrincipalUnits F.toCompleteDVF ≃ₗ[ℤ_[F.residueCharacteristic]]
      PrincipalUnitProdiscreteLimit F.toCompleteDVF :=
  { adicPrincipalUnitsAddEquivProdiscreteLimit F.toCompleteDVF with
    map_smul' := adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul F }

/-- Addition on the adic principal-unit model is continuous. -/
noncomputable instance adicPrincipalUnitsContinuousAdd
    (F : LocalField.{u, v} K) :
    ContinuousAdd (AdicPrincipalUnits F.toCompleteDVF) := by
  let e := adicPrincipalUnitsContinuousAddEquivProdiscreteLimit F.toCompleteDVF
  refine ⟨?_⟩
  have hpair : Continuous fun z :
      AdicPrincipalUnits F.toCompleteDVF ×
        AdicPrincipalUnits F.toCompleteDVF =>
      (e z.1, e z.2) :=
    (e.continuous.comp continuous_fst).prodMk
      (e.continuous.comp continuous_snd)
  have h := e.continuous_symm.comp
    (continuous_add.comp hpair)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  change z.1 + z.2 = e.symm (e z.1 + e z.2)
  apply e.injective
  rw [e.apply_symm_apply]
  exact e.map_add z.1 z.2

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_WithZeroValuationTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Principal-unit topology from a normalized valuation

For a complete discrete valuation with value group `WithZero (Multiplicative ℤ)`, the
inherited topology agrees with the canonical adic model, so the p-adic action and addition are
continuous on the original principal-unit carrier.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-- Compare the type-level adic model with the principal-unit carrier under
the canonical topology of a normalized complete discrete valuation. -/
noncomputable def adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    AdicPrincipalUnits F.toCompleteDVF ≃ₜ+
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1) := by
  let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  letI : ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
      (Valued.v : _root_.Valuation K
        (WithZero (Multiplicative ℤ))) := by
    change ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v
    infer_instance
  let π := chosenPrincipalUnitPadicUniformizer F.toCompleteDVF
  have hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K) :=
    chosenPrincipalUnitPadicUniformizer_isUniformizer F.toCompleteDVF
  have hadic :
      (inferInstance : TopologicalSpace F.toCompleteDVF.valuationSubring) =
        (LubinTate.Valuations.uniformizerPowerIdeal π 1).adicTopology := by
    have hmax :
        (inferInstance : TopologicalSpace F.toCompleteDVF.valuationSubring) =
          F.toCompleteDVF.maximalIdeal.adicTopology := by
      exact ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdic
        (K := K) (Gamma := WithZero (Multiplicative ℤ))
    have hideal : LubinTate.Valuations.uniformizerPowerIdeal π 1 =
        F.toCompleteDVF.maximalIdeal := by
      rw [LubinTate.Valuations.uniformizerPowerIdeal, pow_one,
        ← F.toCompleteDVF.maximalIdeal_eq_span_uniformizer hπ]
    simpa only [hideal] using hmax
  let carrierTopology
      (t : TopologicalSpace F.toCompleteDVF.valuationSubring) :
      TopologicalSpace
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF) 1)) :=
    letI : TopologicalSpace F.toCompleteDVF.valuationSubring := t
    inferInstance
  have hcarrier :
      (inferInstance : TopologicalSpace
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF) 1))) =
        principalUnitAdicTopology F.toCompleteDVF := by
    change carrierTopology
        (inferInstance : TopologicalSpace F.toCompleteDVF.valuationSubring) =
      carrierTopology
        ((LubinTate.Valuations.uniformizerPowerIdeal π 1).adicTopology)
    exact congrArg carrierTopology hadic
  have hcontinuousAdic :
      @Continuous
        (AdicPrincipalUnits F.toCompleteDVF)
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF) 1))
        inferInstance
        (principalUnitAdicTopology F.toCompleteDVF)
        (AdicPrincipalUnits.equiv F.toCompleteDVF) :=
    continuous_induced_dom
  have hcontinuousAdic_symm :
      @Continuous
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF) 1))
        (AdicPrincipalUnits F.toCompleteDVF)
        (principalUnitAdicTopology F.toCompleteDVF)
        inferInstance
        (AdicPrincipalUnits.equiv F.toCompleteDVF).symm :=
    continuous_induced_rng.2 (continuous_id_of_le le_rfl)
  have hcontinuous : Continuous
      (AdicPrincipalUnits.equiv F.toCompleteDVF) := by
    exact Eq.mpr
      (congrArg
        (fun t : TopologicalSpace
            (Additive
              ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
                F.toCompleteDVF) 1)) =>
          @Continuous
            (AdicPrincipalUnits F.toCompleteDVF)
            (Additive
              ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
                F.toCompleteDVF) 1))
            inferInstance t
            (AdicPrincipalUnits.equiv F.toCompleteDVF))
        hcarrier)
      hcontinuousAdic
  have hcontinuous_symm : Continuous
      (AdicPrincipalUnits.equiv F.toCompleteDVF).symm := by
    exact Eq.mpr
      (congrArg
        (fun t : TopologicalSpace
            (Additive
              ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
                F.toCompleteDVF) 1)) =>
          @Continuous
            (Additive
              ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
                F.toCompleteDVF) 1))
            (AdicPrincipalUnits F.toCompleteDVF)
            t inferInstance
            (AdicPrincipalUnits.equiv F.toCompleteDVF).symm)
        hcarrier)
      hcontinuousAdic_symm
  exact ContinuousAddEquiv.mk'
    { toEquiv := AdicPrincipalUnits.equiv F.toCompleteDVF
      continuous_toFun := hcontinuous
      continuous_invFun := hcontinuous_symm }
    (fun _ _ => rfl)

/--
The continuous additive comparison from adic principal units to the underlying local-field model
preserves `ℤ_p`-scalar multiplication.
-/
@[simp] theorem adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] :
    let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    ∀ (a : ℤ_[F.residueCharacteristic])
      (x : AdicPrincipalUnits F.toCompleteDVF),
      adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation v
          (a • x) =
        a • adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation
          v x := by
  let F : LocalField.{u, 0} K := LocalField.ofWithZeroValuation v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  dsimp only
  intro a x
  exact (AdicPrincipalUnits.linearEquivUnderlying F).map_smul a x

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_Core
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Assembles the inverse-limit and topological models used to define the `ℤ_[p]`-module structure on
principal units.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-- Natural p-adic scalars act by the ordinary group powers. -/
@[simp] theorem principalUnitPadic_natCast_smul
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1) :
    (n : ℤ_[F.residueCharacteristic]) • Additive.ofMul x =
      Additive.ofMul (x ^ n) := by
  calc
    (n : ℤ_[F.residueCharacteristic]) • Additive.ofMul x =
        n • Additive.ofMul x :=
      Nat.cast_smul_eq_nsmul ℤ_[F.residueCharacteristic] n (Additive.ofMul x)
    _ = Additive.ofMul (x ^ n) := rfl

/-- Equivalent multiplicative reading of
`principalUnitPadic_natCast_smul`. -/
@[simp] theorem principalUnitPadic_nsmul_eq_pow
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1) :
    Additive.toMul
        ((n : ℤ_[F.residueCharacteristic]) • Additive.ofMul x) = x ^ n := by
  exact congrArg Additive.toMul
    (principalUnitPadic_natCast_smul F n x)

/-- Every `U^r`, for `r >= 1`, is stable under the canonical p-adic action
on `U^1`. -/
theorem principalUnitPadic_smul_mem_higher
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r)
    (a : ℤ_[F.residueCharacteristic])
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)
    (hx : (x : F.valuationSubringˣ) ∈
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) r) :
    ((Additive.toMul (a • Additive.ofMul x) :
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1) :
      F.valuationSubringˣ) ∈
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) r := by
  let n := r - 1
  have hn : n + 1 = r := Nat.sub_add_cancel hr
  let y : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1 :=
    Additive.toMul (a • Additive.ofMul x)
  have hxq :
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F.toCompleteDVF).principalUnitSubquotientMk
        1 (n + 1) x = 1 := by
    exact ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
      F.toCompleteDVF).principalUnitSubquotient_mk_eq_one_iff x).2
      (by
        change (x : F.valuationSubringˣ) ∈
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF) (n + 1)
        rw [hn]
        exact hx)
  have hcoord :
      Additive.ofMul
          (principalUnitInverseLimitCarrierEval F.toCompleteDVF n
            (principalUnitMulEquivInverseLimitCarrier F.toCompleteDVF y)) =
        a • Additive.ofMul
          (principalUnitInverseLimitCarrierEval F.toCompleteDVF n
            (principalUnitMulEquivInverseLimitCarrier F.toCompleteDVF x)) := by
    have h := congrArg
      (fun z : Additive
          (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
        Additive.ofMul
          (principalUnitInverseLimitCarrierEval F.toCompleteDVF n
            (Additive.toMul z)))
      (principalUnitAddEquivInverseLimitCarrier_map_smul
        F a (Additive.ofMul x))
    exact h
  have hyq :
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F.toCompleteDVF).principalUnitSubquotientMk
        1 (n + 1) y = 1 := by
    apply Additive.ofMul.injective
    calc
      Additive.ofMul
          ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F.toCompleteDVF).principalUnitSubquotientMk
            1 (n + 1) y) =
          a • Additive.ofMul
            ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F.toCompleteDVF).principalUnitSubquotientMk
              1 (n + 1) x) := by
        simpa only [principalUnitMulEquivInverseLimitCarrier_apply] using hcoord
      _ = a • Additive.ofMul (1 :
          Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := by rw [hxq]
      _ = 0 := by
        rw [show Additive.ofMul
          (1 : Internal.principalUnitQuotientCarrier F.toCompleteDVF n) = 0 from rfl]
        exact (principalUnitQuotientCarrierPadicModule F n).smul_zero a
      _ = Additive.ofMul (1 :
          Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := rfl
  change (y : F.valuationSubringˣ) ∈
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) r
  rw [← hn]
  exact ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
    F.toCompleteDVF).principalUnitSubquotient_mk_eq_one_iff y).1 hyq

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_IwasawaPrincipalUnits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The convergent Iwasawa product for principal units

This module assembles the finite-level Iwasawa factors into a compatible
family in the principal-unit inverse limit, proves continuity and bijectivity,
and packages the resulting topological additive equivalence.
-/

/-!
# Finite-level Iwasawa generators for principal units

This file develops an explicit topological product decomposition of principal units.  In equal characteristic, choose
a residue-field basis `omega_i` over `F_p`.  For a positive degree `n`, the
prime-to-`p` Iwasawa map is

`g_n(a_i) = product_i (1 + [omega_i] pi^n) ^ a_i`.

The powers by p-adic integers are the canonical powers constructed from the
finite principal-unit quotients in `PrincipalUnitPadicAction`.  This module
constructs each finite-level factor `g_n`, proves its filtration properties,
and establishes its algebraic injectivity.  The convergent global product is
assembled in `IwasawaPrincipalUnits`.
-/

noncomputable section

open scoped BigOperators

universe u v

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

open LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
open Internal

variable {K : Type u} [Field K]

noncomputable instance residueFieldZModAlgebra
    (F : LocalField.{u, v} K) :
    Algebra (ZMod F.residueCharacteristic) F.residueField :=
  ZMod.algebra F.residueField F.residueCharacteristic

/-- The number of vectors in a basis of the residue field over its prime
field.  This is the `f` in `q = p^f` in the field-unit structure theorem. -/
abbrev iwasawaResidueRank (F : LocalField.{u, v} K) : ℕ :=
  Module.finrank (ZMod F.residueCharacteristic) F.residueField

/-- A fixed `F_p`-basis of the residue field, denoted `omega_1,...,omega_f`
in this construction. -/
noncomputable def iwasawaResidueBasis (F : LocalField.{u, v} K) :
    Module.Basis (Fin (iwasawaResidueRank F))
      (ZMod F.residueCharacteristic) F.residueField :=
  Module.finBasis (ZMod F.residueCharacteristic) F.residueField

/-- The element `[omega_i] pi^n` of the `n`-th maximal-ideal power. -/
noncomputable def iwasawaSeedIdeal
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (i : Fin (iwasawaResidueRank F)) :
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) :=
  DVF.maximalIdealPowMulUniformizerPowMap F.toDVF hpi n
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift F.toCompleteDVF
      (iwasawaResidueBasis F i))

/--
Establishes the identity `(iwasawaSeedIdeal F hpi n i : F.valuationSubring) =
CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift F.toCompleteDVF (iwasawaResidueBasis F
i) * pi ^ n`.
-/
@[simp] theorem iwasawaSeedIdeal_val
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (i : Fin (iwasawaResidueRank F)) :
    (iwasawaSeedIdeal F hpi n i : F.valuationSubring) =
      LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift F.toCompleteDVF
          (iwasawaResidueBasis F i) * pi ^ n :=
  rfl

/-- The generator `1 + [omega_i] pi^n`, first as an element of `U^n`. -/
noncomputable def iwasawaSeedAtLevel
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (i : Fin (iwasawaResidueRank F)) :
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) n :=
  LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup
    F.toCompleteDVF hn (iwasawaSeedIdeal F hpi n i)
      (iwasawaSeedIdeal F hpi n i).property

/--
Establishes the identity `(((iwasawaSeedAtLevel F hpi n hn i :
((CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) n) : F.valuationSubringˣ) :
F.valuationSubring) = 1 + CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift
F.toCompleteDVF (iwasawaResidueBasis F i) * pi ^ n`.
-/
@[simp] theorem iwasawaSeedAtLevel_val
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (i : Fin (iwasawaResidueRank F)) :
    (((iwasawaSeedAtLevel F hpi n hn i :
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) n) : F.valuationSubringˣ) :
      F.valuationSubring) =
      1 + LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift F.toCompleteDVF
          (iwasawaResidueBasis F i) * pi ^ n := by
  rw [iwasawaSeedAtLevel,
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val,
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val]
  rfl

/-- The same generator regarded as a first principal unit, so that the
canonical p-adic scalar action is available. -/
noncomputable def iwasawaSeed
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (i : Fin (iwasawaResidueRank F)) :
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) 1 :=
  ⟨(iwasawaSeedAtLevel F hpi n hn i : F.valuationSubringˣ),
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.antitone F.toCompleteDVF hn
      (iwasawaSeedAtLevel F hpi n hn i).property⟩

/--
Establishes the identity `(((iwasawaSeed F hpi n hn i : ((CompleteDVF.higherPrincipalUnitGroup
F.toCompleteDVF)) 1) : F.valuationSubringˣ) : F.valuationSubring) = 1 +
CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift F.toCompleteDVF (iwasawaResidueBasis F
i) * pi ^ n`.
-/
@[simp] theorem iwasawaSeed_val
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (i : Fin (iwasawaResidueRank F)) :
    (((iwasawaSeed F hpi n hn i : ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) 1) :
        F.valuationSubringˣ) : F.valuationSubring) =
      1 + LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift F.toCompleteDVF
          (iwasawaResidueBasis F i) * pi ^ n := by
  exact iwasawaSeedAtLevel_val F hpi n hn i

/-- The leading coefficient of `1 + [omega_i] pi^n` in
`U^n/U^(n+1)` is exactly the basis vector `omega_i`. -/
@[simp] theorem principalUnitSuccQuotAddEquivResidue_iwasawaSeed
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (i : Fin (iwasawaResidueRank F)) :
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer
        F.toCompleteDVF hpi n hn
      (Additive.ofMul
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotMk F.toCompleteDVF n
          (iwasawaSeedAtLevel F hpi n hn i))) =
      iwasawaResidueBasis F i := by
  let r : F.valuationSubring :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift F.toCompleteDVF
      (iwasawaResidueBasis F i)
  let e :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer
      F.toCompleteDVF hpi n hn
  have hs :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue
      F.toCompleteDVF hpi n hn r
  have he := congrArg e hs
  simpa [e, r, iwasawaSeedAtLevel, iwasawaSeedIdeal,
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply,
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueMap_residueTeichmullerLift] using he.symm

/-! ## Reduction of p-adic exponents on one graded layer -/

/-- The Iwasawa homomorphism `g_n : Z_p^f -> U^1`.  Its range is shown
below to lie in `U^n`.  In additive notation the Iwasawa product is a
finite sum of p-adic scalar multiples of the seed units. -/
noncomputable def iwasawaGn
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) :
    (Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) →ₗ[ℤ_[F.residueCharacteristic]]
      Additive (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) 1) :=
  Fintype.linearCombination ℤ_[F.residueCharacteristic]
    (fun i => Additive.ofMul (iwasawaSeed F hpi n hn i))

/--
The defining evaluation formula for `iwasawaGn` is `iwasawaGn F hpi n hn a = ∑ i, a i •
Additive.ofMul (iwasawaSeed F hpi n hn i)`.
-/
@[simp] theorem iwasawaGn_apply
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n)
    (a : Fin (iwasawaResidueRank F) → ℤ_[F.residueCharacteristic]) :
    iwasawaGn F hpi n hn a =
      ∑ i, a i • Additive.ofMul (iwasawaSeed F hpi n hn i) :=
  Fintype.linearCombination_apply
    ℤ_[F.residueCharacteristic]
    (fun i => Additive.ofMul (iwasawaSeed F hpi n hn i)) a

/-! ## Algebraic injectivity of each Iwasawa factor -/

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

noncomputable section

open scoped BigOperators

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

open LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
open Internal

variable {K : Type u} [Field K]

/-! ## The convergent product, constructed through finite quotients -/

/-- The product of one copy of `Z_p^f` for every positive prime-to-`p`
degree. -/
abbrev iwasawaDomain (F : LocalField.{u, v} K) :=
  IwasawaIndex F.residueCharacteristic (iwasawaResidueRank F) →
    ℤ_[F.residueCharacteristic]

/-- The `n`-th factor in Iwasawa's infinite product.  It is `1` when `n`
is zero or is divisible by `p`; this lets finite partial products be indexed
by ordinary ranges without making any choice of an enumeration. -/
noncomputable def iwasawaDegreeTerm
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (n : ℕ) :
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) 1 :=
  if hn : 1 ≤ n ∧ Nat.Coprime n F.residueCharacteristic then
    Additive.toMul
      (iwasawaGn F hpi n hn.1
        (fun i => a (⟨n, hn⟩, i)))
  else 1

/-- Establishes the identity `iwasawaDegreeTerm F hpi (0 : iwasawaDomain F) n = 1`. -/
@[simp] theorem iwasawaDegreeTerm_zero
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (n : ℕ) :
    iwasawaDegreeTerm F hpi (0 : iwasawaDomain F) n = 1 := by
  classical
  rw [iwasawaDegreeTerm]
  split_ifs with hn
  · change Additive.toMul
        (iwasawaGn F hpi n hn.1 (0 : Fin (iwasawaResidueRank F) →
          ℤ_[F.residueCharacteristic])) = 1
    rw [map_zero]
    rfl
  · rfl

/-- The product of the Iwasawa factors of degree at most `r`. -/
noncomputable def iwasawaPartialProduct
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : iwasawaDomain F) (r : ℕ) :
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF)) 1 :=
  ∏ n ∈ Finset.range (r + 1), iwasawaDegreeTerm F hpi a n

/-- Establishes the identity `iwasawaPartialProduct F hpi (0 : iwasawaDomain F) r = 1`. -/
@[simp] theorem iwasawaPartialProduct_zero_input
    (F : LocalField.{u, v} K)
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (r : ℕ) :
    iwasawaPartialProduct F hpi (0 : iwasawaDomain F) r = 1 := by
  classical
  simp [iwasawaPartialProduct]

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicQp
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

/-- The range-restricted local-field valuation has the same `ℚ`-subring of
elements of value at most one as the `p`-adic valuation. -/
theorem mrangeRestrict_valuation_ratCast_le_one_iff_padicValuation_le_one
    (F : LocalField.{u, v} K) [CharZero K] (q : ℚ) :
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF (q : K) ≤ 1 ↔
      Rat.padicValuation F.residueCharacteristic q ≤ 1 := by
  rw [← Subtype.coe_le_coe]
  simpa [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply] using
    F.valuation_ratCast_le_one_iff_padicValuation_le_one q

/-- The range-restricted local-field valuation, restricted along `ℚ → K`, is
equivalent to the usual `p`-adic valuation. -/
theorem ratCast_mrangeRestrict_valuation_isEquiv_padicValuation
    (F : LocalField.{u, v} K) [CharZero K] :
    ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF).comap (Rat.castHom K)).IsEquiv
      (Rat.padicValuation F.residueCharacteristic) := by
  refine (Valuation.isEquiv_iff_valuationSubring
    (v₁ := (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF).comap (Rat.castHom K))
    (v₂ := Rat.padicValuation F.residueCharacteristic)).2 ?_
  ext q
  change _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF ((Rat.castHom K) q) ≤ 1 ↔
    Rat.padicValuation F.residueCharacteristic q ≤ 1
  simpa using
    F.mrangeRestrict_valuation_ratCast_le_one_iff_padicValuation_le_one q

/-- In mixed characteristic, powers of the residue characteristic are cofinal
among neighborhoods of zero for the range-restricted valuation topology. -/
theorem mrangeRestrict_exists_residueCharacteristic_pow_lt_unit
    (F : LocalField.{u, v} K) [CharZero K]
    (gamma : F.mrangeValueGroupˣ) :
    ∃ N : ℕ,
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF
        (((F.residueCharacteristic ^ N : ℕ) : K)) < gamma := by
  have hp_pos :
      0 < _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF (F.residueCharacteristic : K) := by
    rw [← Subtype.coe_lt_coe]
    simpa [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply] using
      (F.toCompleteDVF.valuation.pos_iff).2
        F.natCast_residueCharacteristic_ne_zero_of_charZero
  let delta : F.mrangeValueGroupˣ :=
    Units.mk0
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF (F.residueCharacteristic : K))
      hp_pos.ne'
  have hdelta_lt_one : delta < (1 : F.mrangeValueGroupˣ) := by
    rw [← Units.val_lt_val]
    change
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF (F.residueCharacteristic : K) <
        (1 : F.mrangeValueGroup)
    rw [← Subtype.coe_lt_coe]
    simpa [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply] using
      F.valuation_natCast_residueCharacteristic_lt_one
  have : IsCyclic F.mrangeValueGroupˣ :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_units_isCyclic F.toCompleteDVF
  have : MulArchimedean F.mrangeValueGroupˣ :=
    WithZeroValuation.isCyclic_mulArchimedean F.mrangeValueGroupˣ
  have hdelta_inv : (1 : F.mrangeValueGroupˣ) < delta⁻¹ :=
    one_lt_inv'.2 hdelta_lt_one
  obtain ⟨N, hN⟩ := exists_lt_pow hdelta_inv gamma⁻¹
  refine ⟨N, ?_⟩
  have hpow_lt_units : delta ^ N < gamma := by
    have hinv : (delta⁻¹ ^ N)⁻¹ < (gamma⁻¹)⁻¹ := inv_lt_inv' hN
    simpa [inv_pow] using hinv
  have hpow_lt :
      ((delta ^ N : F.mrangeValueGroupˣ) : F.mrangeValueGroup) <
        (gamma : F.mrangeValueGroup) := by
    exact Units.val_lt_val.2 hpow_lt_units
  simpa [delta, _root_.Valuation.map_pow, Nat.cast_pow] using
    hpow_lt

/-- The rational embedding from `ℚ` with its `p`-adic valuation topology to
`K` with the range-restricted local-field topology is uniformly continuous. -/
theorem ratCastWithValToK_uniformContinuous
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    UniformContinuous
      ((Rat.castHom K).comp
        (WithVal.equiv
          (Rat.padicValuation F.residueCharacteristic)).toRingHom) := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let f : WithVal (Rat.padicValuation F.residueCharacteristic) → K :=
    ((Rat.castHom K).comp
      (WithVal.equiv
        (Rat.padicValuation F.residueCharacteristic)).toRingHom)
  let vq := Rat.padicValuation F.residueCharacteristic
  let vWith : _root_.Valuation (WithVal vq) ℤᵐ⁰ := Valued.v
  let w : _root_.Valuation K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
      F.toCompleteDVF
  change UniformContinuous f
  refine
    ((Valued.hasBasis_uniformity
        (WithVal (Rat.padicValuation F.residueCharacteristic))
        ℤᵐ⁰).uniformContinuous_iff
        (Valued.hasBasis_uniformity K F.mrangeValueGroup)).2 ?_
  intro gamma _
  let gamma' : F.mrangeValueGroupˣ :=
    Units.map
      MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom gamma
  obtain ⟨N, hN⟩ :=
    F.mrangeRestrict_exists_residueCharacteristic_pow_lt_unit gamma'
  let pNQ : ℚ := ((F.residueCharacteristic ^ N : ℕ) : ℚ)
  have hpN_nat_ne : F.residueCharacteristic ^ N ≠ 0 :=
    pow_ne_zero N F.residueCharacteristic_ne_zero
  have hpNQ_ne : pNQ ≠ 0 := by
    simpa [pNQ] using
      (Nat.cast_ne_zero.mpr hpN_nat_ne :
        ((F.residueCharacteristic ^ N : ℕ) : ℚ) ≠ 0)
  let pNW : WithVal vq := (WithVal.equiv vq).symm pNQ
  have hpNW_ne : vWith pNW ≠ 0 := by
    change vq pNQ ≠ 0
    exact (vq.pos_iff.2 hpNQ_ne).ne'
  have hpNW_restrict_ne : vWith.restrict pNW ≠ 0 := by
    simpa using hpNW_ne
  let delta :
      (MonoidWithZeroHom.ValueGroup₀ (.ofClass vWith))ˣ :=
    Units.mk0 (vWith.restrict pNW) hpNW_restrict_ne
  refine ⟨delta, trivial, ?_⟩
  intro x y hxy
  let xq : ℚ :=
    WithVal.equiv (Rat.padicValuation F.residueCharacteristic) x
  let yq : ℚ :=
    WithVal.equiv (Rat.padicValuation F.residueCharacteristic) y
  have hpadic :
      Rat.padicValuation F.residueCharacteristic (yq - xq) <
        Rat.padicValuation F.residueCharacteristic pNQ := by
    change vq (yq - xq) < vq pNQ
    change vWith.restrict (y - x) < vWith.restrict pNW at hxy
    have hvWith : vWith (y - x) < vWith pNW :=
      (_root_.Valuation.restrict_lt_iff vWith).1 hxy
    change vq (yq - xq) < vq pNQ at hvWith
    exact hvWith
  have hcomap :
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF ((yq - xq : ℚ) : K) <
        _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF ((pNQ : ℚ) : K) := by
    have hEquiv :=
      F.ratCast_mrangeRestrict_valuation_isEquiv_padicValuation
    have hlt :=
      (hEquiv.lt_iff_lt (x := yq - xq) (y := pNQ)).2 hpadic
    simpa [pNQ] using hlt
  have hfsub :
      f y - f x = ((yq - xq : ℚ) : K) := by
    simp [f, xq, yq]
  change (Valued.v : _root_.Valuation K F.mrangeValueGroup).restrict (f y - f x) < gamma
  rw [_root_.Valuation.restrict_lt_iff_lt_embedding]
  change w (f y - f x) < (gamma' : F.mrangeValueGroup)
  calc
    w (f y - f x) = w ((yq - xq : ℚ) : K) := by
          rw [hfsub]
    _ < w ((pNQ : ℚ) : K) := hcomap
    _ = w (((F.residueCharacteristic ^ N : ℕ) : K)) := by
          congr 1
          simp [pNQ]
    _ < gamma' := hN

/-- The topology induced on the rational prime field from the range-restricted
local-field topology is exactly the usual `p`-adic topology. -/
theorem ratCastWithValToK_isUniformInducing
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    IsUniformInducing
      ((Rat.castHom K).comp
        (WithVal.equiv
          (Rat.padicValuation F.residueCharacteristic)).toRingHom) := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let f : WithVal (Rat.padicValuation F.residueCharacteristic) → K :=
    ((Rat.castHom K).comp
      (WithVal.equiv
        (Rat.padicValuation F.residueCharacteristic)).toRingHom)
  let vq := Rat.padicValuation F.residueCharacteristic
  let vWith : _root_.Valuation (WithVal vq) ℤᵐ⁰ := Valued.v
  let w : _root_.Valuation K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
      F.toCompleteDVF
  change IsUniformInducing f
  refine
    ((Valued.hasBasis_uniformity
        (WithVal (Rat.padicValuation F.residueCharacteristic))
        ℤᵐ⁰).isUniformInducing_iff
        (Valued.hasBasis_uniformity K F.mrangeValueGroup)).2 ?_
  constructor
  · exact
      ((Valued.hasBasis_uniformity
          (WithVal (Rat.padicValuation F.residueCharacteristic))
          ℤᵐ⁰).uniformContinuous_iff
          (Valued.hasBasis_uniformity K F.mrangeValueGroup)).1
        F.ratCastWithValToK_uniformContinuous
  · intro delta _
    obtain ⟨q, hq⟩ :=
      Rat.surjective_padicValuation F.residueCharacteristic
        (MonoidWithZeroHom.ValueGroup₀.embedding
          (delta :
            MonoidWithZeroHom.ValueGroup₀ (.ofClass vWith)))
    have hq_ne : q ≠ 0 := by
      intro hzero
      have hdelta_zero :
          MonoidWithZeroHom.ValueGroup₀.embedding
              (delta :
                MonoidWithZeroHom.ValueGroup₀ (.ofClass vWith)) = 0 := by
        simpa [hzero] using hq.symm
      exact
        (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero delta)
          hdelta_zero
    have hqK_ne : ((q : ℚ) : K) ≠ 0 := by
      exact Rat.cast_ne_zero.mpr hq_ne
    have hvalue_ne :
        _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF ((q : ℚ) : K) ≠ 0 := by
      rw [← Subtype.coe_ne_coe]
      simpa [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply] using
        ((F.toCompleteDVF.valuation.pos_iff).2 hqK_ne).ne'
    have hrestrict_ne : w.restrict ((q : ℚ) : K) ≠ 0 := by
      simpa using hvalue_ne
    let gamma :
        (MonoidWithZeroHom.ValueGroup₀ (.ofClass w))ˣ :=
      Units.mk0 (w.restrict ((q : ℚ) : K)) hrestrict_ne
    refine ⟨gamma, trivial, ?_⟩
    intro x y hxy
    let xq : ℚ :=
      WithVal.equiv (Rat.padicValuation F.residueCharacteristic) x
    let yq : ℚ :=
      WithVal.equiv (Rat.padicValuation F.residueCharacteristic) y
    have hfsub :
        f y - f x = ((yq - xq : ℚ) : K) := by
      simp [f, xq, yq]
    have hcomap :
        _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF ((yq - xq : ℚ) : K) <
          _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF ((q : ℚ) : K) := by
      change w.restrict (f y - f x) < w.restrict ((q : ℚ) : K) at hxy
      rw [hfsub] at hxy
      exact (_root_.Valuation.restrict_lt_iff w).1 hxy
    have hpadic :
        Rat.padicValuation F.residueCharacteristic (yq - xq) <
          Rat.padicValuation F.residueCharacteristic q := by
      have hEquiv :=
        F.ratCast_mrangeRestrict_valuation_isEquiv_padicValuation
      exact (hEquiv.lt_iff_lt (x := yq - xq) (y := q)).1 hcomap
    change vWith.restrict (y - x) < delta
    rw [_root_.Valuation.restrict_lt_iff_lt_embedding]
    change
      vq (yq - xq) <
        MonoidWithZeroHom.ValueGroup₀.embedding
          (delta :
            MonoidWithZeroHom.ValueGroup₀ (.ofClass vWith))
    simpa [hq] using hpadic

/-- The rational embedding from p-adically valued `ℚ` to the closed `Qp`
candidate is uniformly continuous. -/
theorem ratCastWithValToQpadicClosureSubfield_uniformContinuous
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    UniformContinuous F.ratCastWithValToQpadicClosureSubfield := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  exact
    F.ratCastWithValToK_uniformContinuous.subtype_mk
      (fun q => F.ratCast_mem_qpadicClosureSubfield
        ((WithVal.equiv
          (Rat.padicValuation F.residueCharacteristic) q : ℚ)))

/-- The closed `Qp` candidate carries exactly the subspace topology induced
from the p-adic topology on the rational prime field. -/
theorem ratCastWithValToQpadicClosureSubfield_isUniformInducing
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    IsUniformInducing F.ratCastWithValToQpadicClosureSubfield := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  have hK :
      IsUniformInducing
        (((↑) : F.qpadicClosureSubfield → K) ∘
          F.ratCastWithValToQpadicClosureSubfield) := by
    simpa [Function.comp_def, ratCastWithValToQpadicClosureSubfield,
      ratCastToQpadicClosureSubfield] using
      F.ratCastWithValToK_isUniformInducing
  exact
    (isUniformInducing_val
      (F.qpadicClosureSubfield : Set K)).of_comp_iff.1 hK

/-- The extension of the rational embedding to the `p`-adic completion,
landing in the closed `Qp` candidate inside `K`. -/
noncomputable def qpadicCompletionToQpadicClosureSubfield
    (F : LocalField.{u, v} K) [CharZero K] :
    (Rat.padicValuation F.residueCharacteristic).Completion →+*
      F.qpadicClosureSubfield := by
  letI : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  letI : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  haveI : CompleteSpace F.qpadicClosureSubfield :=
    F.qpadicClosureSubfield_completeSpace
  exact
    UniformSpace.Completion.extensionHom
      F.ratCastWithValToQpadicClosureSubfield
      F.ratCastWithValToQpadicClosureSubfield_uniformContinuous.continuous

/--
Establishes the identity `F.qpadicCompletionToQpadicClosureSubfield q =
F.ratCastWithValToQpadicClosureSubfield q`.
-/
theorem qpadicCompletionToQpadicClosureSubfield_coe
    (F : LocalField.{u, v} K) [CharZero K]
    (q : WithVal (Rat.padicValuation F.residueCharacteristic)) :
    F.qpadicCompletionToQpadicClosureSubfield q =
      F.ratCastWithValToQpadicClosureSubfield q := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  have : CompleteSpace F.qpadicClosureSubfield :=
    F.qpadicClosureSubfield_completeSpace
  exact
    UniformSpace.Completion.extensionHom_coe
      F.ratCastWithValToQpadicClosureSubfield
      F.ratCastWithValToQpadicClosureSubfield_uniformContinuous.continuous q

/-- The completion map from the `p`-adically valued rationals to the closed
`Qp` candidate is a uniform inducing map. -/
theorem qpadicCompletionToQpadicClosureSubfield_isUniformInducing
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    letI : NontriviallyNormedField K :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
    IsUniformInducing F.qpadicCompletionToQpadicClosureSubfield := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  have : CompleteSpace F.qpadicClosureSubfield :=
    F.qpadicClosureSubfield_completeSpace
  simpa [qpadicCompletionToQpadicClosureSubfield,
    UniformSpace.Completion.extensionHom] using
    UniformSpace.Completion.isUniformInducing_extension
      (f := F.ratCastWithValToQpadicClosureSubfield)
      F.ratCastWithValToQpadicClosureSubfield_isUniformInducing

/-- The induced map from the actual `p`-adic number field to the closed `Qp`
candidate inside `K`. -/
noncomputable def qpadicNumbersToQpadicClosureSubfield
    (F : LocalField.{u, v} K) [CharZero K] :
    ℚ_[F.residueCharacteristic] →+* F.qpadicClosureSubfield :=
  F.qpadicCompletionToQpadicClosureSubfield.comp
    (Padic.withValRingEquiv
      (p := F.residueCharacteristic)).symm.toRingHom

/--
Establishes the identity `F.qpadicNumbersToQpadicClosureSubfield (q : ℚ_[F.residueCharacteristic])
= F.ratCastToQpadicClosureSubfield q`.
-/
theorem qpadicNumbersToQpadicClosureSubfield_ratCast
    (F : LocalField.{u, v} K) [CharZero K] (q : ℚ) :
    F.qpadicNumbersToQpadicClosureSubfield
        (q : ℚ_[F.residueCharacteristic]) =
      F.ratCastToQpadicClosureSubfield q := by
  let vq := Rat.padicValuation F.residueCharacteristic
  let e := Padic.withValRingEquiv (p := F.residueCharacteristic)
  have hcast :
      e (((WithVal.equiv vq).symm q : WithVal vq) :
          vq.Completion) =
        (q : ℚ_[F.residueCharacteristic]) := by
    rw [Padic.coe_withValRingEquiv]
    simpa [vq, Function.comp_def] using
      (UniformSpace.Completion.extension_coe
        (f := ((Rat.castHom ℚ_[F.residueCharacteristic]).comp
          (WithVal.equiv (Rat.padicValuation F.residueCharacteristic)).toRingHom :
            WithVal (Rat.padicValuation F.residueCharacteristic) →
              ℚ_[F.residueCharacteristic]))
        (Padic.isUniformInducing_cast_withVal
          (p := F.residueCharacteristic)).uniformContinuous
        ((WithVal.equiv (Rat.padicValuation F.residueCharacteristic)).symm q))
  have hsymm :
      e.symm (q : ℚ_[F.residueCharacteristic]) =
        (((WithVal.equiv vq).symm q : WithVal vq) :
          vq.Completion) := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact hcast.symm
  calc
    F.qpadicNumbersToQpadicClosureSubfield
        (q : ℚ_[F.residueCharacteristic])
        = F.qpadicCompletionToQpadicClosureSubfield
            (e.symm (q : ℚ_[F.residueCharacteristic])) := rfl
    _ = F.qpadicCompletionToQpadicClosureSubfield
          (((WithVal.equiv vq).symm q : WithVal vq) :
            vq.Completion) := by
          rw [hsymm]
    _ = F.ratCastWithValToQpadicClosureSubfield
          ((WithVal.equiv vq).symm q) := by
          simpa [vq] using
            F.qpadicCompletionToQpadicClosureSubfield_coe
              ((WithVal.equiv vq).symm q)
    _ = F.ratCastToQpadicClosureSubfield q := by
          ext
          simp [ratCastWithValToQpadicClosureSubfield, vq]

/-- The actual `ℚ_[p]` map to the closed `Qp` candidate is a uniform inducing
map. -/
theorem qpadicNumbersToQpadicClosureSubfield_isUniformInducing
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    letI : NontriviallyNormedField K :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
    IsUniformInducing F.qpadicNumbersToQpadicClosureSubfield := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  have hcomp :
      IsUniformInducing
        (F.qpadicCompletionToQpadicClosureSubfield ∘
          (Padic.withValUniformEquiv
            (p := F.residueCharacteristic)).symm) :=
    F.qpadicCompletionToQpadicClosureSubfield_isUniformInducing.comp
      (Padic.withValUniformEquiv
        (p := F.residueCharacteristic)).symm.isUniformInducing
  have hinv :
      ⇑(Padic.withValUniformEquiv
          (p := F.residueCharacteristic)).symm =
        ⇑(Padic.withValRingEquiv
          (p := F.residueCharacteristic)).symm := by
    funext x
    exact congrArg
      (fun e :
          (Rat.padicValuation F.residueCharacteristic).Completion ≃
            ℚ_[F.residueCharacteristic] => e.symm x)
      Padic.toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv
  change
    IsUniformInducing
      (F.qpadicCompletionToQpadicClosureSubfield ∘
        ⇑(Padic.withValRingEquiv
          (p := F.residueCharacteristic)).symm)
  rw [← hinv]
  exact hcomp

/-- The image of the `ℚ_[p]` map is closed in the closed `Qp` candidate. -/
theorem qpadicNumbersToQpadicClosureSubfield_isClosed_range
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    letI : NontriviallyNormedField K :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
    IsClosed (Set.range F.qpadicNumbersToQpadicClosureSubfield) := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  have hEmbedding :
      IsUniformEmbedding F.qpadicNumbersToQpadicClosureSubfield :=
    ⟨F.qpadicNumbersToQpadicClosureSubfield_isUniformInducing,
      RingHom.injective _⟩
  exact hEmbedding.isClosedEmbedding.isClosed_range

/-- The map from `ℚ_[p]` to the closed `Qp` candidate has dense range. -/
theorem qpadicNumbersToQpadicClosureSubfield_denseRange
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    letI : NontriviallyNormedField K :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
    DenseRange F.qpadicNumbersToQpadicClosureSubfield := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  apply DenseRange.of_comp
    (g := ((↑) : ℚ → ℚ_[F.residueCharacteristic]))
  have hfun :
      F.qpadicNumbersToQpadicClosureSubfield ∘
          ((↑) : ℚ → ℚ_[F.residueCharacteristic]) =
        F.ratCastToQpadicClosureSubfield := by
    funext q
    exact F.qpadicNumbersToQpadicClosureSubfield_ratCast q
  rw [hfun]
  exact F.ratCastToQpadicClosureSubfield_denseRange

/-- The dense closed embedding from `ℚ_[p]` onto the closed `Qp` candidate is
surjective. -/
theorem qpadicNumbersToQpadicClosureSubfield_surjective
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    letI : NontriviallyNormedField K :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
    Function.Surjective F.qpadicNumbersToQpadicClosureSubfield := by
  let : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  let : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  rw [← Set.range_eq_univ]
  have hdense := F.qpadicNumbersToQpadicClosureSubfield_denseRange
  have hclosed := F.qpadicNumbersToQpadicClosureSubfield_isClosed_range
  exact hclosed.closure_eq.symm.trans hdense.closure_range

/-- The closed subfield generated by `ℚ` inside a mixed-characteristic local
field is canonically isomorphic to the actual `p`-adic number field. -/
noncomputable def qpadicNumbersEquivQpadicClosureSubfield
    (F : LocalField.{u, v} K) [CharZero K] :
    ℚ_[F.residueCharacteristic] ≃+* F.qpadicClosureSubfield :=
  RingEquiv.ofBijective F.qpadicNumbersToQpadicClosureSubfield
    ⟨RingHom.injective _,
      F.qpadicNumbersToQpadicClosureSubfield_surjective⟩

/-- The closed `Qp` candidate has the induced nontrivial normed-field
structure.  The residue characteristic itself has norm different from one. -/
@[implicit_reducible]
noncomputable def qpadicClosureSubfield_nontriviallyNormedField
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    letI : NontriviallyNormedField K :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
    NontriviallyNormedField F.qpadicClosureSubfield := by
  letI : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  haveI :
      (Valued.v : _root_.Valuation K F.mrangeValueGroup).RankOne := by
    change
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict
        F.toCompleteDVF).RankOne
    exact
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_rankOne
        F.toCompleteDVF
  letI : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  let pSub : F.qpadicClosureSubfield :=
    F.ratCastToQpadicClosureSubfield (F.residueCharacteristic : ℚ)
  have hpSub_coe :
      (pSub : K) = (F.residueCharacteristic : K) := by
    simp [pSub]
  refine NontriviallyNormedField.ofNormNeOne ?_
  refine ⟨pSub, ?_, ?_⟩
  · intro hp
    have hpK : (pSub : K) = 0 := by
      simpa using congrArg Subtype.val hp
    rw [hpSub_coe] at hpK
    exact F.natCast_residueCharacteristic_ne_zero_of_charZero hpK
  · have hpVal_lt_one :
        _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F.toCompleteDVF
          (F.residueCharacteristic : K) < 1 := by
      rw [← Subtype.coe_lt_coe]
      simpa [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply] using
        F.valuation_natCast_residueCharacteristic_lt_one
    have hpNorm_lt_one_K :
        ‖(F.residueCharacteristic : K)‖ < 1 := by
      simpa [_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued] using
        (Valued.toNormedField.norm_lt_one_iff
          (x := (F.residueCharacteristic : K))).2 hpVal_lt_one
    have hpNorm_lt_one : ‖pSub‖ < 1 := by
      change ‖(pSub : K)‖ < 1
      simpa [hpSub_coe] using hpNorm_lt_one_K
    exact ne_of_lt hpNorm_lt_one

/-- The ambient local field is a normed algebra over the closed `Qp`
candidate, using the induced subfield norm. -/
@[implicit_reducible]
noncomputable def qpadicClosureSubfield_normedAlgebra
    (F : LocalField.{u, v} K) [CharZero K] :
    letI : Valued K F.mrangeValueGroup :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
    letI : NontriviallyNormedField K :=
      _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
    letI : NontriviallyNormedField F.qpadicClosureSubfield :=
      F.qpadicClosureSubfield_nontriviallyNormedField
    NormedAlgebra F.qpadicClosureSubfield K := by
  letI : Valued K F.mrangeValueGroup :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F.toCompleteDVF
  letI : NontriviallyNormedField K :=
    _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_nontriviallyNormedField F.toCompleteDVF
  letI : NontriviallyNormedField F.qpadicClosureSubfield :=
    F.qpadicClosureSubfield_nontriviallyNormedField
  exact
    { (inferInstance : Algebra F.qpadicClosureSubfield K) with
      norm_smul_le := fun a x => by
        change ‖(a : K) * x‖ ≤ ‖(a : K)‖ * ‖x‖
        exact norm_mul_le (a : K) x }

/-- The actual `p`-adic number field acts on `K` through the canonical
isomorphism with the closed `Qp` candidate and the inclusion into `K`. -/
@[implicit_reducible]
noncomputable def qpadicNumbersAlgebra
    (F : LocalField.{u, v} K) [CharZero K] :
    Algebra ℚ_[F.residueCharacteristic] K :=
  RingHom.toAlgebra
    (F.qpadicClosureSubfield.subtype.comp
      (F.qpadicNumbersEquivQpadicClosureSubfield :
        ℚ_[F.residueCharacteristic] →+* F.qpadicClosureSubfield))

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_MixedCharacteristicStructure_IntegralLattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

/-- The canonical `Q_p` scalar context supplied by a mixed-characteristic
local field.  It carries the residue-characteristic prime witness; installing
it also installs the coherent algebra and finite-dimensional structures. -/
class MixedQPadicContext (F : LocalField.{u, v} K) : Prop where
  /-- The residue characteristic of a mixed-characteristic local field is prime. -/
  residueCharacteristic_prime : F.residueCharacteristic.Prime

/-- The canonical `Q_p` scalar context attached to `F`. -/
theorem mixedQPadicContext (F : LocalField.{u, v} K) :
    MixedQPadicContext F :=
  ⟨F.residueCharacteristic_prime⟩

/-- Registers the mathematical fact `Fact F.residueCharacteristic.Prime` for typeclass inference. -/
instance mixedQPadicContextFact
    (F : LocalField.{u, v} K) [ctx : MixedQPadicContext F] :
    Fact F.residueCharacteristic.Prime :=
  ⟨ctx.residueCharacteristic_prime⟩

/--
Equips the target with its canonical `Algebra` structure, namely `Algebra
ℚ_[F.residueCharacteristic] K`.
-/
noncomputable instance mixedQPadicContextAlgebra
    (F : LocalField.{u, v} K) [CharZero K] [MixedQPadicContext F] :
    Algebra ℚ_[F.residueCharacteristic] K :=
  F.qpadicNumbersAlgebra

/-! ### the canonical `Z_p` integral basis -/

/-! ### The canonical `Z_p` action on `U^r` -/

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_CyclicIdeleClassNormIndex
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The global class-field axiom

This file proves the cyclic idele-class norm-index formula.  The first
input is the `H⁻¹` calculation for the principal-idele term in

`1 → Lˣ → I_L → C_L → 1`.

For a cyclic extension this term vanishes by Hilbert 90.  The result below
is transported through the actual low-degree Tate comparison and then
through the equivariant identification of `Lˣ` with the subgroup of
principal relative ideles.
-/

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

/-- Every degree-zero Tate class is annihilated by the order of the
acting group.  For a fixed representative `a`, its group norm is
`a ^ |G|`.  This exponent observation drives the prime-degree descent
step. -/
theorem herbrandH0_pow_card_eq_one
    {G A : Type}
    [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A]
    (q : HerbrandH0 G A) :
    q ^ Fintype.card G = 1 := by
  refine HerbrandH0.inductionOn
    (motive := fun q : HerbrandH0 G A =>
      q ^ Fintype.card G = 1)
    q ?_
  intro a
  rw [← map_pow, HerbrandH0.mk_eq_one_iff]
  refine ⟨(a : A), ?_⟩
  change (∏ g : G, g • (a : A)) =
    (a : A) ^ Fintype.card G
  calc
    (∏ g : G, g • (a : A)) =
        ∏ _g : G, (a : A) := by
      apply Finset.prod_congr rfl
      intro g _hg
      exact a.property g
    _ = (a : A) ^ Fintype.card G := by
      rw [Finset.prod_const, Finset.card_univ]

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormalization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

section UnramifiedPrimeClass

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]

noncomputable instance normalizationIntegerRingIsIntegralClosure :
    IsIntegralClosure 𝒪[L] 𝒪[K] L :=
  localCompleteDVF_integerRing_isIntegralClosure K L

/-! ## Canonical norm-residue normalization -/

/-! ## Equality with the field-facing unramified reciprocity map -/

/-! ## Continuous Frobenius normalization -/

end UnramifiedPrimeClass

end LocalClassFieldTheory
end
end


