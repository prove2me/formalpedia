-- Prove2me | Definitions.Def_OAIQ244Duke029
-- name    : OAIQ244Duke029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:35:06.561342+00:00
-- url     : https://prove2.me/theorems/3d6c0d36-c6f6-4192-b1c9-30efd4765824
-- title:
--   Definitions bundle OAIQ244Duke029 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 270 declarations of OpenAI's Lean: 95 definitions, 3 inductive types or structures, 11 instances and 161 theorems. The definitions and types are `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitClassMapOfLeKerEquivClass`, `LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration.principalUnitClassSubgroupOfEquivClassOfLe`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffSubringHom`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.laurentSeriesAlgebra`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.laurentSeriesEvalHom`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.equiv`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.homeomorph`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.equiv`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.transition`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.higherUnitInverseLimitCarrier`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.higherUnitQuotientTransition`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitHomeomorphInverseLimitCarrier`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrier`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierInv`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierToFull`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransitionAdd`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierZModModule`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitToInverseLimitCarrier`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitInverseLimitEquiv`, `LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitInverseLimitHomeomorphIntrinsic` and 58 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_LocalTensorDecomposition`, `AlgebraicNumberTheory_Idele_Relative_Support`, `DukePrimeDegree_Geometry_UpperRootChart`, `LocalField_DiscreteValuationField_Basic`, `LocalField_DiscreteValuationField_EqualCharacteristicLaurent`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_AdicProdiscreteComparison`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_FiniteQuotientPadicModule`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_InverseLimitCore`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_InverseLimitTopology`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_ProdiscretePadicModule`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_QuotientTransition`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_TopologyModelTypes`, `LocalField_DiscreteValuationField_PrincipalUnits_AutomorphismTransport`, `LocalField_DiscreteValuationField_PrincipalUnits_Core`, `LocalField_DiscreteValuationField_PrincipalUnits_Filtration`, `LocalField_DiscreteValuationField_PrincipalUnits_ResidueQuotient`, `LocalField_DiscreteValuationField_PrincipalUnits_ResidueRoots`, `LocalField_DiscreteValuationField_PrincipalUnits_TeichmullerDecomposition`, `LocalField_DiscreteValuationField_PrincipalUnits_TeichmullerLift`, `LocalField_DiscreteValuationField_Units`, `Valuation_DiscreteValuationField_Complete`, `Valuation_DiscreteValuationField_Henselian`, `Valuation_HenselLemma`.
--
--   **Imports.** It imports the published bundle `Def_DukePrimeDegree`; the bundles `OAIQ244Duke015`, `OAIQ244Duke017`, `OAIQ244Duke018` and `OAIQ244Duke022` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke038`, `OAIQ244Duke039`, `OAIQ244Duke040`, `OAIQ244Duke043` and `OAIQ244Duke044`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.MinimalAxioms
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Basic
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
import Mathlib.Dynamics.Ergodic.Conservative
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
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
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
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
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
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.WithTopology
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke015
import Definitions.Def_OAIQ244Duke017
import Definitions.Def_OAIQ244Duke018
import Definitions.Def_OAIQ244Duke022

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_Units
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

/-- The subgroup of `U^l/U^n` represented by `U^m/U^n` is canonically
the class of `U^m` in `G/U^n`. -/
noncomputable def principalUnitClassSubgroupOfEquivClassOfLe {l m n : ℕ}
    (hlm : l ≤ m) [(U.principalUnitSubgroup n).Normal] :
    (U.principalUnitSubgroupClassInQuotient m n).subgroupOf
        (U.principalUnitSubgroupClassInQuotient l n) ≃*
      U.principalUnitSubgroupClassInQuotient m n where
  toFun q :=
    ⟨((q : U.principalUnitSubgroupClassInQuotient l n) :
        G ⧸ U.principalUnitSubgroup n), by
      exact q.property⟩
  invFun q :=
    ⟨⟨(q : G ⧸ U.principalUnitSubgroup n), by
        rcases (U.mem_principalUnitSubgroupClassInQuotient_iff m n
            (q : G ⧸ U.principalUnitSubgroup n)).1 q.property with
          ⟨x, hx, hxq⟩
        exact ⟨x, U.mem_of_mem_of_le hlm hx, hxq⟩⟩, by
      change (q : G ⧸ U.principalUnitSubgroup n) ∈
        U.principalUnitSubgroupClassInQuotient m n
      exact q.property⟩
  left_inv q := by
    ext
    rfl
  right_inv q := by
    ext
    rfl
  map_mul' q r := by
    ext
    rfl

/-- Kernel form of `principalUnitClassMapOfLe_ker_eq`, with the kernel
identified as the class `U^m/U^n`. -/
noncomputable def principalUnitClassMapOfLeKerEquivClass {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (U.principalUnitClassMapOfLe hlm hmn).ker ≃*
      U.principalUnitSubgroupClassInQuotient m n :=
  (MulEquiv.subgroupCongr
      (U.principalUnitClassMapOfLe_ker_eq hlm hmn)).trans
    (U.principalUnitClassSubgroupOfEquivClassOfLe hlm)

/-- Cardinality multiplication for three levels of a principal-unit
filtration: `#(U^l/U^n) = #(U^m/U^n) * #(U^l/U^m)`. -/
theorem card_principalUnitClassInQuotient_eq_mul_of_le {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    [Finite (U.principalUnitSubgroupClassInQuotient l n)]
    [Finite (U.principalUnitSubgroupClassInQuotient m n)]
    [Finite (U.principalUnitSubgroupClassInQuotient l m)] :
    Nat.card (U.principalUnitSubgroupClassInQuotient l n) =
      Nat.card (U.principalUnitSubgroupClassInQuotient m n) *
        Nat.card (U.principalUnitSubgroupClassInQuotient l m) := by
  let φ := U.principalUnitClassMapOfLe hlm hmn
  calc
    Nat.card (U.principalUnitSubgroupClassInQuotient l n) =
        Nat.card φ.ker * φ.ker.index := by
          exact (Subgroup.card_mul_index φ.ker).symm
    _ =
        Nat.card (U.principalUnitSubgroupClassInQuotient m n) *
          Nat.card ((U.principalUnitSubgroupClassInQuotient l n) ⧸ φ.ker) := by
          rw [Subgroup.index_eq_card]
          rw [Nat.card_congr
            (U.principalUnitClassMapOfLeKerEquivClass hlm hmn).toEquiv]
    _ =
        Nat.card (U.principalUnitSubgroupClassInQuotient m n) *
          Nat.card (U.principalUnitSubgroupClassInQuotient l m) := by
          rw [Nat.card_congr
            (U.principalUnitClassQuotientKerEquivClassOfLe hlm hmn).toEquiv]

/-- Cardinality form of the class/subquotient identification. -/
theorem card_principalUnitSubquotient_eq_classInQuotient_of_le
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal]
    [Finite (U.principalUnitSubquotient m n)]
    [Finite (U.principalUnitSubgroupClassInQuotient m n)] :
    Nat.card (U.principalUnitSubquotient m n) =
      Nat.card (U.principalUnitSubgroupClassInQuotient m n) := by
  rw [Nat.card_congr
    (U.principalUnitSubquotientEquivClassInQuotientOfLe hmn).toEquiv]

/-- The degenerate subquotient `U^n/U^n` has cardinality one. -/
theorem card_principalUnitSubquotient_self
    (n : ℕ) [(U.principalUnitSubgroup n).Normal]
    [Finite (U.principalUnitSubquotient n n)] :
    Nat.card (U.principalUnitSubquotient n n) = 1 := by
  have htop :
      (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup n) = ⊤ := by
    ext x
    simp
  change Nat.card
    (U.principalUnitSubgroup n ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup n)) = 1
  rw [htop]
  simp

/-- Cardinality multiplication for principal-unit subquotients:
`#(U^l/U^n) = #(U^m/U^n) * #(U^l/U^m)`. -/
theorem card_principalUnitSubquotient_eq_mul_of_le {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    [Finite (U.principalUnitSubquotient l n)]
    [Finite (U.principalUnitSubquotient m n)]
    [Finite (U.principalUnitSubquotient l m)] :
    Nat.card (U.principalUnitSubquotient l n) =
      Nat.card (U.principalUnitSubquotient m n) *
      Nat.card (U.principalUnitSubquotient l m) := by
  let : Finite (U.principalUnitSubgroupClassInQuotient l n) :=
    Finite.of_injective
      (U.principalUnitSubquotientEquivClassInQuotientOfLe
        (le_trans hlm hmn)).symm
      (U.principalUnitSubquotientEquivClassInQuotientOfLe
        (le_trans hlm hmn)).symm.injective
  let : Finite (U.principalUnitSubgroupClassInQuotient m n) :=
    Finite.of_injective
      (U.principalUnitSubquotientEquivClassInQuotientOfLe hmn).symm
      (U.principalUnitSubquotientEquivClassInQuotientOfLe hmn).symm.injective
  let : Finite (U.principalUnitSubgroupClassInQuotient l m) :=
    Finite.of_injective
      (U.principalUnitSubquotientEquivClassInQuotientOfLe hlm).symm
      (U.principalUnitSubquotientEquivClassInQuotientOfLe hlm).symm.injective
  rw [U.card_principalUnitSubquotient_eq_classInQuotient_of_le
      (le_trans hlm hmn)]
  rw [U.card_principalUnitSubquotient_eq_classInQuotient_of_le hmn]
  rw [U.card_principalUnitSubquotient_eq_classInQuotient_of_le hlm]
  exact U.card_principalUnitClassInQuotient_eq_mul_of_le hlm hmn

/-- Iterated cardinality form of the filtration counting argument:
`#(U^l/U^(l+r))` is the product of the adjacent graded-piece cardinalities. -/
theorem card_principalUnitSubquotient_eq_prod_gradedPiece
    (hN : ∀ i : ℕ, (U.principalUnitSubgroup i).Normal)
    [∀ i j : ℕ, Finite (U.principalUnitSubquotient i j)]
    (l r : ℕ) :
    Nat.card (U.principalUnitSubquotient l (l + r)) =
      ∏ i ∈ Finset.range r,
        Nat.card (U.principalUnitGradedPiece (l + i)) := by
  induction r with
  | zero =>
      let := hN l
      exact U.card_principalUnitSubquotient_self l
  | succ r ih =>
      let := hN (l + r)
      let := hN ((l + r) + 1)
      calc
        Nat.card (U.principalUnitSubquotient l (l + Nat.succ r)) =
            Nat.card (U.principalUnitSubquotient l ((l + r) + 1)) := by
              rw [Nat.add_succ]
        _ =
            Nat.card (U.principalUnitSubquotient (l + r) ((l + r) + 1)) *
              Nat.card (U.principalUnitSubquotient l (l + r)) := by
              exact U.card_principalUnitSubquotient_eq_mul_of_le
                (Nat.le_add_right l r) (Nat.le_succ (l + r))
        _ =
            Nat.card (U.principalUnitGradedPiece (l + r)) *
              (∏ i ∈ Finset.range r,
                Nat.card (U.principalUnitGradedPiece (l + i))) := by
              rw [ih,
                U.card_principalUnitSubquotient_succ_eq_gradedPiece]
        _ =
            ∏ i ∈ Finset.range (Nat.succ r),
              Nat.card (U.principalUnitGradedPiece (l + i)) := by
              rw [Finset.prod_range_succ]
              rw [Nat.mul_comm]

end AntitoneSubgroupFiltration

end DiscreteValuationField

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Henselian
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

/-- Hensel's lemma in the simple-root form used by mathlib. -/
theorem exists_lift_root_simple (F : HenselianDVF.{u, v} K)
    (f : Polynomial F.valuationSubring) (hf : f.Monic) (a0 : F.valuationSubring)
    (hroot : f.eval a0 ∈ F.maximalIdeal)
    (hsimple : IsUnit (Ideal.Quotient.mk F.maximalIdeal (f.derivative.eval a0))) :
    ∃ a : F.valuationSubring, f.IsRoot a ∧ a - a0 ∈ F.maximalIdeal :=
  HenselianRing.is_henselian f hf a0 hroot hsimple

end HenselianDVF

end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Complete
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

/-- The maximal ideal is the principal ideal generated by a uniformizer. -/
theorem maximalIdeal_eq_span_uniformizer (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) :
    F.maximalIdeal = Ideal.span ({pi} : Set F.valuationSubring) :=
  F.toDVF.maximalIdeal_eq_span_uniformizer hpi

end CompleteDVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_HenselLemma
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
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

/-- Hensel's lemma gives a linear factor lifting from a simple approximate root. -/
theorem exists_linear_factor_lift
    (f : Polynomial F.valuationSubring) (hf : f.Monic) (a0 : F.valuationSubring)
    (hroot : f.eval a0 ∈ F.maximalIdeal)
    (hsimple : IsUnit (Ideal.Quotient.mk F.maximalIdeal (f.derivative.eval a0))) :
    ∃ a : F.valuationSubring, ∃ q : Polynomial F.valuationSubring,
      f.IsRoot a ∧ a - a0 ∈ F.maximalIdeal ∧
        f = (Polynomial.X - Polynomial.C a) * q := by
  rcases F.exists_lift_root_simple f hf a0 hroot hsimple with
    ⟨a, ha_root, ha_congruent⟩
  rcases (Polynomial.dvd_iff_isRoot.mpr ha_root) with ⟨q, hq⟩
  exact ⟨a, q, ha_root, ha_congruent, hq⟩

/-- The lifted linear factor is monic. -/
theorem exists_monic_linear_factor_lift
    (f : Polynomial F.valuationSubring) (hf : f.Monic) (a0 : F.valuationSubring)
    (hroot : f.eval a0 ∈ F.maximalIdeal)
    (hsimple : IsUnit (Ideal.Quotient.mk F.maximalIdeal (f.derivative.eval a0))) :
    ∃ a : F.valuationSubring, ∃ q : Polynomial F.valuationSubring,
      f.IsRoot a ∧ a - a0 ∈ F.maximalIdeal ∧
        (Polynomial.X - Polynomial.C a).Monic ∧
          f = (Polynomial.X - Polynomial.C a) * q := by
  rcases F.exists_linear_factor_lift f hf a0 hroot hsimple with
    ⟨a, q, ha_root, ha_congruent, hfactor⟩
  exact ⟨a, q, ha_root, ha_congruent, Polynomial.monic_X_sub_C a, hfactor⟩

/-- Hensel's lemma gives a monic linear factor whose quotient is also monic. -/
theorem exists_monic_linear_factor_lift_with_monic_quotient
    (f : Polynomial F.valuationSubring) (hf : f.Monic) (a0 : F.valuationSubring)
    (hroot : f.eval a0 ∈ F.maximalIdeal)
    (hsimple : IsUnit (Ideal.Quotient.mk F.maximalIdeal (f.derivative.eval a0))) :
    ∃ a : F.valuationSubring, ∃ q : Polynomial F.valuationSubring,
      f.IsRoot a ∧ a - a0 ∈ F.maximalIdeal ∧
        (Polynomial.X - Polynomial.C a).Monic ∧ q.Monic ∧
          f = (Polynomial.X - Polynomial.C a) * q := by
  rcases F.exists_monic_linear_factor_lift f hf a0 hroot hsimple with
    ⟨a, q, ha_root, ha_congruent, hlinear, hfactor⟩
  have hq : q.Monic := hlinear.of_mul_monic_left (hfactor ▸ hf)
  exact ⟨a, q, ha_root, ha_congruent, hlinear, hq, hfactor⟩

/-- Residue-field form of the lifted monic linear factor theorem.  Starting
from an actual simple root of the reduced polynomial over the residue field,
Hensel's lemma gives a root with the prescribed residue class, a monic lifted
linear factor, and a monic quotient. -/
theorem exists_monic_linear_factor_lift_of_residue_root
    (f : Polynomial F.valuationSubring) (hf : f.Monic)
    (aBar : F.residueField)
    (hroot : (f.map F.residueMap).eval aBar = 0)
    (hsimple : (f.derivative.map F.residueMap).eval aBar ≠ 0) :
    ∃ a : F.valuationSubring, ∃ q : Polynomial F.valuationSubring,
      f.IsRoot a ∧ F.residueMap a = aBar ∧
        (Polynomial.X - Polynomial.C a).Monic ∧ q.Monic ∧
          f = (Polynomial.X - Polynomial.C a) * q := by
  obtain ⟨a0, ha0⟩ := F.toDVF.residue_surjective aBar
  have hroot_residue : F.residueMap (f.eval a0) = 0 := by
    have heval :
        (f.map F.residueMap).eval (F.residueMap a0) =
          F.residueMap (f.eval a0) := by
      exact Polynomial.eval_map_apply (f := F.residueMap) (p := f) a0
    rw [← heval, ha0]
    exact hroot
  have hroot_mem : f.eval a0 ∈ F.maximalIdeal := by
    simpa [HenselianDVF.residueMap, DVF.residueMap]
      using (IsLocalRing.residue_eq_zero_iff (f.eval a0)).1 hroot_residue
  have hderivative_residue :
      F.residueMap (f.derivative.eval a0) ≠ 0 := by
    have heval :
        (f.derivative.map F.residueMap).eval (F.residueMap a0) =
          F.residueMap (f.derivative.eval a0) := by
      exact Polynomial.eval_map_apply (f := F.residueMap)
        (p := f.derivative) a0
    rw [← heval, ha0]
    exact hsimple
  have hsimple_unit :
      IsUnit (Ideal.Quotient.mk F.maximalIdeal (f.derivative.eval a0)) := by
    change IsUnit (F.residueMap (f.derivative.eval a0))
    exact isUnit_iff_ne_zero.mpr hderivative_residue
  rcases F.exists_monic_linear_factor_lift_with_monic_quotient
      f hf a0 hroot_mem hsimple_unit with
    ⟨a, q, ha_root, ha_congruent, hlinear, hq, hfactor⟩
  have ha_residue : F.residueMap a = aBar := by
    rw [← ha0]
    exact
      (residue_eq_residue_iff_sub_mem_maximalIdeal
        (R := F.valuationSubring) a a0).2 ha_congruent
  exact ⟨a, q, ha_root, ha_residue, hlinear, hq, hfactor⟩

/-- Natural reduced-polynomial form of the lifted monic linear factor theorem.
The simplicity condition is stated using the derivative of the reduced
polynomial itself. -/
theorem exists_monic_linear_factor_lift_of_reduced_simple_root
    (f : Polynomial F.valuationSubring) (hf : f.Monic)
    (aBar : F.residueField)
    (hroot : (f.map F.residueMap).eval aBar = 0)
    (hsimple : ((f.map F.residueMap).derivative).eval aBar ≠ 0) :
    ∃ a : F.valuationSubring, ∃ q : Polynomial F.valuationSubring,
      f.IsRoot a ∧ F.residueMap a = aBar ∧
        (Polynomial.X - Polynomial.C a).Monic ∧ q.Monic ∧
          f = (Polynomial.X - Polynomial.C a) * q := by
  exact F.exists_monic_linear_factor_lift_of_residue_root
    f hf aBar hroot (by simpa [Polynomial.derivative_map] using hsimple)

end HenselianDVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnits_Filtration
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
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
# Principal-unit filtration from a valuation ring

For a complete DVF `F`, the concrete principal-unit filtration on the unit group
of the valuation ring is

`U^n = { u | u - 1 ∈ m^n }`.

This file turns that definition into the abstract `AntitoneSubgroupFiltration`
used by ramification and norm arguments.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The concrete `n`-th principal-unit subgroup of the valuation ring unit group. -/
def higherPrincipalUnitGroup
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) (n : ℕ) :
    Subgroup F.valuationSubringˣ where
  carrier := {u | (u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n}
  one_mem' := by
    simp
  mul_mem' := by
    intro x y hx hy
    have hxy :
        ((x * y : F.valuationSubringˣ) : F.valuationSubring) - 1 =
          (x : F.valuationSubring) * ((y : F.valuationSubring) - 1) +
            ((x : F.valuationSubring) - 1) := by
      simp
      ring
    change ((x * y : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n
    rw [hxy]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) hx
  inv_mem' := by
    intro x hx
    have hxinv :
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 =
            -(((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
              ((x : F.valuationSubring) - 1)) := by
      calc
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 =
            ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) -
              ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
                (x : F.valuationSubring) := by
          simp
        _ = -(((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
              ((x : F.valuationSubring) - 1)) := by
          ring
    change ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n
    rw [hxinv]
    exact (F.maximalIdeal ^ n).neg_mem
      (Ideal.mul_mem_left (F.maximalIdeal ^ n)
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) hx)

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/--
Characterizes `u ∈ higherPrincipalUnitGroup F n` by the equivalent condition `(u :
F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n`.
-/
@[simp] theorem mem_iff (n : ℕ) (u : F.valuationSubringˣ) :
    u ∈ higherPrincipalUnitGroup F n ↔
      (u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n :=
  Iff.rfl

/-- Higher levels are contained in lower levels. -/
theorem antitone {m n : ℕ} (h : m ≤ n) :
    higherPrincipalUnitGroup F n ≤ higherPrincipalUnitGroup F m := by
  intro u hu
  exact (Ideal.pow_le_pow_right h) hu

/-- Establishes the identity `higherPrincipalUnitGroup F 0 = ⊤`. -/
@[simp] theorem zero_eq_top :
    higherPrincipalUnitGroup F 0 = ⊤ := by
  ext u
  simp [higherPrincipalUnitGroup]

/-- The residue of a valuation-ring unit, viewed as a unit of the residue
field. -/
def residueUnitHom :
    F.valuationSubringˣ →* F.residueFieldˣ :=
  Units.map F.residueMap.toMonoidHom

/--
The defining evaluation formula for `residueUnitHom` is `((higherPrincipalUnitGroup.residueUnitHom
F u : F.residueFieldˣ) : F.residueField) = F.residueMap (u : F.valuationSubring)`.
-/
@[simp] theorem residueUnitHom_apply (u : F.valuationSubringˣ) :
    ((higherPrincipalUnitGroup.residueUnitHom F u : F.residueFieldˣ) :
        F.residueField) =
      F.residueMap (u : F.valuationSubring) :=
  rfl

/-- The first concrete principal-unit level consists exactly of units whose
residue is `1`. -/
theorem mem_one_iff_residue_eq_one (u : F.valuationSubringˣ) :
    u ∈ higherPrincipalUnitGroup F 1 ↔
      F.residueMap (u : F.valuationSubring) = 1 := by
  rw [higherPrincipalUnitGroup.mem_iff, pow_one]
  constructor
  · intro hu
    have hres :
        F.residueMap (u : F.valuationSubring) = F.residueMap 1 := by
      exact
        (residue_eq_residue_iff_sub_mem_maximalIdeal
          (R := F.valuationSubring) (u : F.valuationSubring) 1).2 hu
    simpa using hres
  · intro hu
    exact
      (residue_eq_residue_iff_sub_mem_maximalIdeal
        (R := F.valuationSubring) (u : F.valuationSubring) 1).1
        (by simpa using hu)

/--
Characterizes `higherPrincipalUnitGroup.residueUnitHom F u = 1` by the equivalent condition `u ∈
higherPrincipalUnitGroup F 1`.
-/
theorem residueUnitHom_eq_one_iff (u : F.valuationSubringˣ) :
    higherPrincipalUnitGroup.residueUnitHom F u = 1 ↔
      u ∈ higherPrincipalUnitGroup F 1 := by
  constructor
  · intro hu
    apply (higherPrincipalUnitGroup.mem_one_iff_residue_eq_one F u).2
    have hval :=
      congrArg (fun z : F.residueFieldˣ => (z : F.residueField)) hu
    simpa using hval
  · intro hu
    apply Units.ext
    simpa using (higherPrincipalUnitGroup.mem_one_iff_residue_eq_one F u).1 hu

end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnits_AutomorphismTransport
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
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
# Automorphism transport for principal units

A field automorphism preserving the chosen valuation ring acts on the valuation ring,
its residue field, its units, and every principal-unit quotient.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- A field automorphism preserving the chosen valuation ring induces a ring
automorphism of the valuation ring.  This is the unit/residue source used
before invoking local reciprocity in the local-field arguments. -/
def valuationSubringRingEquivOfPreserves
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring) :
    F.valuationSubring ≃+* F.valuationSubring :=
  RingEquiv.restrict e F.valuation.valuationSubring
    F.valuation.valuationSubring hmem

/-- A valuation-ring-preserving field automorphism preserves every power of the
maximal ideal of the chosen valuation ring. -/
theorem valuationSubringRingEquivOfPreserves_mem_maximalIdeal_pow_iff
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) (x : F.valuationSubring) :
    valuationSubringRingEquivOfPreserves F e hmem x ∈ F.maximalIdeal ^ n ↔
      x ∈ F.maximalIdeal ^ n := by
  let r := valuationSubringRingEquivOfPreserves F e hmem
  have hmax :
      F.maximalIdeal.map
          (r : F.valuationSubring →+* F.valuationSubring) =
        F.maximalIdeal :=
    IsLocalRing.map_ringEquiv_maximalIdeal r
  have hmap :
      (F.maximalIdeal ^ n).map (r : F.valuationSubring →+* F.valuationSubring) =
        F.maximalIdeal ^ n := by
    rw [Ideal.map_pow, hmax]
  constructor
  · intro hx
    rw [← hmap] at hx
    rw [Ideal.mem_map_iff_of_surjective
      (r : F.valuationSubring →+* F.valuationSubring) r.surjective] at hx
    rcases hx with ⟨y, hy, hyx⟩
    have hy_eq : y = x := r.injective hyx
    simpa [hy_eq] using hy
  · intro hx
    rw [← hmap]
    exact Ideal.mem_map_of_mem (r : F.valuationSubring →+* F.valuationSubring) hx

/-- The induced automorphism on valuation-ring units. -/
def valuationSubringUnitEquivOfPreserves
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring) :
    F.valuationSubringˣ ≃* F.valuationSubringˣ :=
  Units.mapEquiv
    (valuationSubringRingEquivOfPreserves F e hmem).toMulEquiv

/--
The defining evaluation formula for `valuationSubringUnitEquivOfPreserves` is
`((valuationSubringUnitEquivOfPreserves F e hmem u : F.valuationSubringˣ) : F.valuationSubring) =
valuationSubringRingEquivOfPreserves F e hmem (u : F.valuationSubring)`.
-/
@[simp] theorem valuationSubringUnitEquivOfPreserves_apply
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (u : F.valuationSubringˣ) :
    ((valuationSubringUnitEquivOfPreserves F e hmem u :
        F.valuationSubringˣ) : F.valuationSubring) =
      valuationSubringRingEquivOfPreserves F e hmem
        (u : F.valuationSubring) :=
  rfl

/-- The induced automorphism on valuation-ring units preserves every concrete
principal-unit level `U^n`. -/
theorem valuationSubringUnitEquivOfPreserves_mem_principalUnit_iff
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) (u : F.valuationSubringˣ) :
    valuationSubringUnitEquivOfPreserves F e hmem u ∈
        higherPrincipalUnitGroup F n ↔
      u ∈ higherPrincipalUnitGroup F n := by
  rw [higherPrincipalUnitGroup.mem_iff, higherPrincipalUnitGroup.mem_iff]
  have hsub :
      ((valuationSubringUnitEquivOfPreserves F e hmem u :
          F.valuationSubringˣ) : F.valuationSubring) - 1 =
        valuationSubringRingEquivOfPreserves F e hmem
          ((u : F.valuationSubring) - 1) := by
    simp [valuationSubringUnitEquivOfPreserves_apply]
  rw [hsub]
  exact valuationSubringRingEquivOfPreserves_mem_maximalIdeal_pow_iff F e hmem
    n ((u : F.valuationSubring) - 1)

/-- The subgroup map form of principal-unit preservation for a
valuation-ring-preserving field automorphism. -/
theorem higherPrincipalUnitGroup_map_valuationSubringUnitEquivOfPreserves
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) :
    (higherPrincipalUnitGroup F n).map
        (valuationSubringUnitEquivOfPreserves F e hmem :
          F.valuationSubringˣ →* F.valuationSubringˣ) =
      higherPrincipalUnitGroup F n := by
  let ueq := valuationSubringUnitEquivOfPreserves F e hmem
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (valuationSubringUnitEquivOfPreserves_mem_principalUnit_iff
      F e hmem n v).2 hv
  · intro hu
    refine ⟨ueq.symm u, ?_, by simp [ueq]⟩
    exact (valuationSubringUnitEquivOfPreserves_mem_principalUnit_iff
      F e hmem n (ueq.symm u)).1 (by simpa [ueq] using hu)

/-- A valuation-ring-preserving field automorphism induces an automorphism on
`O^*/U^n` for every concrete principal-unit level. -/
noncomputable def unitsModPrincipalUnitEquivOfPreserves
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) :
    F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n ≃*
      F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n :=
  QuotientGroup.congr (higherPrincipalUnitGroup F n)
    (higherPrincipalUnitGroup F n)
    (valuationSubringUnitEquivOfPreserves F e hmem)
    (higherPrincipalUnitGroup_map_valuationSubringUnitEquivOfPreserves F e hmem n)

/--
Establishes the identity `unitsModPrincipalUnitEquivOfPreserves F e hmem n (QuotientGroup.mk'
(higherPrincipalUnitGroup F n) u) = QuotientGroup.mk' (higherPrincipalUnitGroup F n)
(valuationSubringUnitEquivOfPreserves F e hmem u)`.
-/
@[simp] theorem unitsModPrincipalUnitEquivOfPreserves_mk
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (n : ℕ) (u : F.valuationSubringˣ) :
    unitsModPrincipalUnitEquivOfPreserves F e hmem n
        (QuotientGroup.mk' (higherPrincipalUnitGroup F n) u) =
      QuotientGroup.mk' (higherPrincipalUnitGroup F n)
        (valuationSubringUnitEquivOfPreserves F e hmem u) :=
  rfl

end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnits_ResidueQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
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
# The first principal-unit quotient

Identifies valuation-ring units modulo first principal units with residue-field units and
records compatibility with valuation-preserving automorphisms.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The kernel of the residue map on valuation-ring units is the first
principal-unit subgroup. -/
theorem residueUnitHom_ker_eq :
    (higherPrincipalUnitGroup.residueUnitHom F).ker =
      higherPrincipalUnitGroup F 1 := by
  ext u
  rw [MonoidHom.mem_ker, higherPrincipalUnitGroup.residueUnitHom_eq_one_iff]

/-- The first-isomorphism form of the residue map on valuation-ring units:
`O_K^* / U_K^1` is the unit group of the residue field. -/
noncomputable def unitsModOneEquivResidueFieldUnits :
    F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F 1 ≃* F.residueFieldˣ :=
  QuotientGroup.liftEquiv
    (higherPrincipalUnitGroup F 1)
    (by
      simpa [higherPrincipalUnitGroup.residueUnitHom] using
        (IsLocalRing.surjective_units_map_of_local_ringHom
          F.residueMap F.residue_surjective
          (inferInstanceAs (IsLocalHom F.residueMap))))
    (higherPrincipalUnitGroup.residueUnitHom_ker_eq F).symm

/--
Establishes the identity `higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits F
(QuotientGroup.mk' (higherPrincipalUnitGroup F 1) u) = higherPrincipalUnitGroup.residueUnitHom F
u`.
-/
@[simp] theorem unitsModOneEquivResidueFieldUnits_mk
    (u : F.valuationSubringˣ) :
    higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits F
        (QuotientGroup.mk' (higherPrincipalUnitGroup F 1) u) =
      higherPrincipalUnitGroup.residueUnitHom F u := by
  rfl

end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnits_ResidueRoots
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
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
# Residue roots of unity

Hensel lifting identifies the finite residue-field unit group with the lifted roots of
unity in the valuation ring.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The `(q - 1)`-st roots of unity in the valuation ring, where
`q = #κ`. -/
abbrev residueRootsOfUnityGroup [Finite F.residueField] :
    Subgroup F.valuationSubringˣ :=
  rootsOfUnity (Nat.card F.residueField - 1) F.valuationSubring

/-- Every nonzero residue class is a simple root of
`X^(#κ - 1) - 1`. -/
theorem residueRootPolynomial_derivative_eval_ne_zero
    [Finite F.residueField] (y : F.residueFieldˣ) :
    (((Polynomial.X ^ (Nat.card F.residueField - 1) - 1 :
        Polynomial F.residueField).derivative).eval
          (y : F.residueField)) ≠ 0 := by
  classical
  let := Fintype.ofFinite F.residueField
  have hn :
      ((Nat.card F.residueField - 1 : ℕ) : F.residueField) ≠ 0 := by
    have hunitcard :
        (Fintype.card F.residueFieldˣ : F.residueField) ≠ 0 := by
      simpa using
        (FiniteField.card_cast_subgroup_card_ne_zero
          (K := F.residueField) (⊤ : Subgroup F.residueFieldˣ))
    simpa [Nat.card_eq_fintype_card, Fintype.card_units] using hunitcard
  have hy :
      (y : F.residueField) ^ ((Nat.card F.residueField - 1) - 1) ≠ 0 :=
    pow_ne_zero _ y.ne_zero
  have hmul :
      ((Nat.card F.residueField - 1 : ℕ) : F.residueField) *
          (y : F.residueField) ^
            ((Nat.card F.residueField - 1) - 1) ≠ 0 :=
    mul_ne_zero hn hy
  simpa [Polynomial.derivative_sub, Polynomial.derivative_one,
    Polynomial.derivative_X_pow, Polynomial.eval_mul] using hmul

/-- Hensel lift of finite-residue-field roots of unity: every residue-field
unit has a valuation-ring unit representative satisfying `u^(q - 1) = 1`.

This is the substantive splitting input for the multiplicative unit decomposition:
it upgrades the quotient isomorphism `O^*/U^1 ≃ κ^*` from an abstract
first-isomorphism statement to a root-of-unity representative in `O^*`. -/
theorem exists_residueRootsOfUnity_lift
    [Finite F.residueField] (y : F.residueFieldˣ) :
    ∃ u : F.valuationSubringˣ,
      u ∈ higherPrincipalUnitGroup.residueRootsOfUnityGroup F ∧
        higherPrincipalUnitGroup.residueUnitHom F u = y := by
  classical
  let n := Nat.card F.residueField - 1
  let f : Polynomial F.valuationSubring := Polynomial.X ^ n - 1
  have hnpos : 0 < n := by
    let := Fintype.ofFinite F.residueField
    have hunitpos : 0 < Fintype.card F.residueFieldˣ :=
      Fintype.card_pos_iff.mpr ⟨1⟩
    simpa [n, Nat.card_eq_fintype_card, Fintype.card_units] using hunitpos
  have hf : f.Monic := by
    dsimp [f, n]
    simpa using
      (Polynomial.monic_X_pow_sub_C
        (1 : F.valuationSubring) (ne_of_gt hnpos))
  have hroot : (f.map F.residueMap).eval (y : F.residueField) = 0 := by
    let := Fintype.ofFinite F.residueField
    have hpow :
        (y : F.residueField) ^ (Fintype.card F.residueField - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one
        (K := F.residueField) (y : F.residueField) y.ne_zero
    simp [f, n, Nat.card_eq_fintype_card, Polynomial.eval_sub, hpow]
  have hsimple :
      ((f.map F.residueMap).derivative).eval
        (y : F.residueField) ≠ 0 := by
    simpa [f, n] using
      (higherPrincipalUnitGroup.residueRootPolynomial_derivative_eval_ne_zero
        (F := F) y)
  rcases
      F.toHenselianDVF.exists_monic_linear_factor_lift_of_reduced_simple_root
        f hf (y : F.residueField) hroot hsimple with
    ⟨a, q, ha_root, ha_residue, _hlinear, _hq, _hfactor⟩
  have hunit : IsUnit a :=
    (F.residue_ne_zero_iff_isUnit a).1
      (by
        change F.toHenselianDVF.residueMap a ≠ 0
        rw [ha_residue]
        exact y.ne_zero)
  rcases hunit with ⟨u, hu⟩
  have ha_pow : a ^ n = 1 := by
    have ha_eval : f.eval a = 0 := Polynomial.IsRoot.def.mp ha_root
    have hsub : a ^ n - 1 = 0 := by
      simpa [f, n, Polynomial.eval_sub] using ha_eval
    exact sub_eq_zero.mp hsub
  refine ⟨u, ?_, ?_⟩
  · rw [mem_rootsOfUnity]
    apply Units.ext
    change
      (((u : F.toHenselianDVF.valuationSubring) : F.valuationSubring) ^
          (Nat.card F.residueField - 1)) =
        (1 : F.valuationSubring)
    simpa [n, hu] using ha_pow
  · apply Units.ext
    rw [higherPrincipalUnitGroup.residueUnitHom_apply]
    rw [hu]
    exact ha_residue

/-- The residue map restricted to the Hensel-lifted `(q - 1)`-roots of unity. -/
def residueRootsOfUnityResidueHom [Finite F.residueField] :
    higherPrincipalUnitGroup.residueRootsOfUnityGroup F →* F.residueFieldˣ :=
  (higherPrincipalUnitGroup.residueUnitHom F).comp
    (higherPrincipalUnitGroup.residueRootsOfUnityGroup F).subtype

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F)`.
-/
theorem residueRootsOfUnityResidueHom_surjective
    [Finite F.residueField] :
    Function.Surjective
      (higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F) := by
  intro y
  rcases higherPrincipalUnitGroup.exists_residueRootsOfUnity_lift
      (F := F) y with
    ⟨u, hu, hres⟩
  exact ⟨⟨u, hu⟩, hres⟩

/-- A unit satisfying the Teichmuller equation is a root of
`X^(q - 1) - 1` over the valuation ring. -/
theorem residueRootPolynomial_isRoot_of_mem
    [Finite F.residueField] {u : F.valuationSubringˣ}
    (hu : u ∈ higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
    (Polynomial.X ^ (Nat.card F.residueField - 1) - 1 :
        Polynomial F.valuationSubring).IsRoot
      (u : F.valuationSubring) := by
  rw [mem_rootsOfUnity] at hu
  have hpow :
      (u : F.valuationSubring) ^ (Nat.card F.residueField - 1) = 1 := by
    have hunit :=
      congrArg (fun z : F.valuationSubringˣ => (z : F.valuationSubring)) hu
    simpa using hunit
  exact Polynomial.IsRoot.def.mpr (by
    simp [Polynomial.eval_sub, hpow])

/-- The derivative of `X^(q - 1) - 1` at a valuation-ring unit is a unit.
This is the simple-root input for uniqueness of Teichmuller representatives. -/
theorem residueRootPolynomial_derivative_eval_isUnit
    [Finite F.residueField] (u : F.valuationSubringˣ) :
    IsUnit
      (((Polynomial.X ^ (Nat.card F.residueField - 1) - 1 :
          Polynomial F.valuationSubring).derivative).eval
        (u : F.valuationSubring)) := by
  let n := Nat.card F.residueField - 1
  let f : Polynomial F.valuationSubring := Polynomial.X ^ n - 1
  have hres :
      F.residueMap (f.derivative.eval (u : F.valuationSubring)) =
        ((f.map F.residueMap).derivative).eval
          (F.residueMap (u : F.valuationSubring)) := by
    calc
      F.residueMap (f.derivative.eval (u : F.valuationSubring)) =
          (f.derivative.map F.residueMap).eval
            (F.residueMap (u : F.valuationSubring)) := by
        exact (Polynomial.eval_map_apply (f := F.residueMap)
          (p := f.derivative) (u : F.valuationSubring)).symm
      _ = ((f.map F.residueMap).derivative).eval
          (F.residueMap (u : F.valuationSubring)) := by
        rw [Polynomial.derivative_map]
  have hsimple :
      ((f.map F.residueMap).derivative).eval
          (F.residueMap (u : F.valuationSubring)) ≠ 0 := by
    simpa [f, n, higherPrincipalUnitGroup.residueUnitHom] using
      higherPrincipalUnitGroup.residueRootPolynomial_derivative_eval_ne_zero
        (F := F) (higherPrincipalUnitGroup.residueUnitHom F u)
  exact
    (F.residue_ne_zero_iff_isUnit
      (f.derivative.eval (u : F.valuationSubring))).1
      (by
        rw [hres]
        exact hsimple)

/--
The specified map is injective: `Function.Injective
(higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F)`.
-/
theorem residueRootsOfUnityResidueHom_injective
    [Finite F.residueField] :
    Function.Injective
      (higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F) := by
  intro x y hxy
  let n := Nat.card F.residueField - 1
  let f : Polynomial F.valuationSubring := Polynomial.X ^ n - 1
  have hxroot :
      f.IsRoot ((x : F.valuationSubringˣ) : F.valuationSubring) := by
    dsimp [f, n]
    exact
      higherPrincipalUnitGroup.residueRootPolynomial_isRoot_of_mem
        (F := F) x.property
  have hyroot :
      f.IsRoot ((y : F.valuationSubringˣ) : F.valuationSubring) := by
    dsimp [f, n]
    exact
      higherPrincipalUnitGroup.residueRootPolynomial_isRoot_of_mem
        (F := F) y.property
  have hres :
      F.residueMap ((y : F.valuationSubringˣ) : F.valuationSubring) =
        F.residueMap ((x : F.valuationSubringˣ) : F.valuationSubring) := by
    have hval :=
      congrArg (fun z : F.residueFieldˣ => (z : F.residueField)) hxy
    simpa [higherPrincipalUnitGroup.residueRootsOfUnityResidueHom,
      higherPrincipalUnitGroup.residueUnitHom] using hval.symm
  have hderiv :
      IsUnit
        (f.derivative.eval
          ((x : F.valuationSubringˣ) : F.valuationSubring)) := by
    dsimp [f, n]
    exact
      higherPrincipalUnitGroup.residueRootPolynomial_derivative_eval_isUnit
        (F := F) (x : F.valuationSubringˣ)
  have hring :
      ((y : F.valuationSubringˣ) : F.valuationSubring) =
        ((x : F.valuationSubringˣ) : F.valuationSubring) :=
    F.toHenselianDVF.eq_of_isRoot_of_isRoot_of_residue_eq_of_derivative_isUnit
      (f := f) hxroot hyroot hres hderiv
  apply Subtype.ext
  apply Units.ext
  exact hring.symm

/--
The specified map is bijective: `Function.Bijective
(higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F)`.
-/
theorem residueRootsOfUnityResidueHom_bijective
    [Finite F.residueField] :
    Function.Bijective
      (higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F) :=
  ⟨higherPrincipalUnitGroup.residueRootsOfUnityResidueHom_injective F,
    higherPrincipalUnitGroup.residueRootsOfUnityResidueHom_surjective F⟩

/-- Hensel's splitting of the residue-unit map on the `(q - 1)`-roots of
unity: the Teichmuller representatives in `O^*` are exactly `κ^*`. -/
noncomputable def residueRootsOfUnityEquivResidueFieldUnits
    [Finite F.residueField] :
    higherPrincipalUnitGroup.residueRootsOfUnityGroup F ≃*
      F.residueFieldˣ :=
  MulEquiv.ofBijective
    (higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F)
    (higherPrincipalUnitGroup.residueRootsOfUnityResidueHom_bijective F)

/--
The defining evaluation formula for `residueRootsOfUnityEquivResidueFieldUnits` is
`higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F u =
higherPrincipalUnitGroup.residueUnitHom F u`.
-/
@[simp] theorem residueRootsOfUnityEquivResidueFieldUnits_apply
    [Finite F.residueField]
    (u : higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
    higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F u =
      higherPrincipalUnitGroup.residueUnitHom F u :=
  rfl
end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnits_TeichmullerLift
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
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
# Teichmuller lifts

Constructs multiplicative Teichmuller representatives, and in equal characteristic the
coefficient-field section of the residue map.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The Teichmuller representative lift from the finite residue field to the
valuation ring: `0` lifts to `0`, and nonzero residue classes lift through the
root-of-unity splitting of `κˣ`. -/
noncomputable def residueTeichmullerLift [Finite F.residueField] :
    F.residueField → F.valuationSubring :=
  fun y =>
    letI := Classical.decEq F.residueField
    if hy : y = 0 then
      0
    else
      (((higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F).symm
          (Units.mk0 y hy) :
        higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
        F.valuationSubringˣ)

/-- Establishes the identity `higherPrincipalUnitGroup.residueTeichmullerLift F 0 = 0`. -/
@[simp] theorem residueTeichmullerLift_zero [Finite F.residueField] :
    higherPrincipalUnitGroup.residueTeichmullerLift F 0 = 0 := by
  simp [higherPrincipalUnitGroup.residueTeichmullerLift]

/-- Establishes the identity `higherPrincipalUnitGroup.residueTeichmullerLift F 1 = 1`. -/
@[simp] theorem residueTeichmullerLift_one [Finite F.residueField] :
    higherPrincipalUnitGroup.residueTeichmullerLift F 1 = 1 := by
  let e :=
    higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F
  have hone : (1 : F.residueField) ≠ 0 := one_ne_zero
  have hroot :
      e.symm (Units.mk0 (1 : F.residueField) hone) = 1 := by
    apply e.injective
    simp [e]
  have hunit :
      ((e.symm (Units.mk0 (1 : F.residueField) hone) :
          higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
          F.valuationSubringˣ) = 1 := by
    simp
  simp [higherPrincipalUnitGroup.residueTeichmullerLift, hone]

/-- The Teichmuller lift reduces to the residue class it lifts. -/
theorem residueMap_residueTeichmullerLift [Finite F.residueField]
    (y : F.residueField) :
    F.residueMap (higherPrincipalUnitGroup.residueTeichmullerLift F y) = y := by
  classical
  by_cases hy : y = 0
  · simp [higherPrincipalUnitGroup.residueTeichmullerLift, hy]
  · let e :=
      higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F
    have hroot :
        higherPrincipalUnitGroup.residueUnitHom F
            (((e.symm (Units.mk0 y hy) :
              higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
              F.valuationSubringˣ)) =
          Units.mk0 y hy := by
      change e (e.symm (Units.mk0 y hy)) = Units.mk0 y hy
      simp
    have hval :=
      congrArg (fun u : F.residueFieldˣ => (u : F.residueField)) hroot
    simpa [higherPrincipalUnitGroup.residueTeichmullerLift, hy, e,
      higherPrincipalUnitGroup.residueUnitHom] using hval

/-- The Teichmuller lift is multiplicative. -/
theorem residueTeichmullerLift_mul [Finite F.residueField]
    (x y : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerLift F (x * y) =
      higherPrincipalUnitGroup.residueTeichmullerLift F x *
        higherPrincipalUnitGroup.residueTeichmullerLift F y := by
  classical
  by_cases hx : x = 0
  · simp [higherPrincipalUnitGroup.residueTeichmullerLift, hx]
  by_cases hy : y = 0
  · simp [higherPrincipalUnitGroup.residueTeichmullerLift, hy]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  let e :=
    higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F
  have hroot :
      e.symm (Units.mk0 (x * y) hxy) =
        e.symm (Units.mk0 x hx) * e.symm (Units.mk0 y hy) := by
    apply e.injective
    apply Units.ext
    simp [e]
  have hunit :
      ((e.symm (Units.mk0 (x * y) hxy) :
          higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
          F.valuationSubringˣ) =
        ((e.symm (Units.mk0 x hx) :
            higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
            F.valuationSubringˣ) *
          ((e.symm (Units.mk0 y hy) :
            higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
            F.valuationSubringˣ) := by
    simp
  simp [higherPrincipalUnitGroup.residueTeichmullerLift, hx, hy, hxy]

/-- Every Teichmuller representative is a root of `T^q - T`, where
`q = #κ`. -/
theorem residueTeichmullerLift_pow_card [Finite F.residueField]
    (y : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerLift F y ^
        Nat.card F.residueField =
      higherPrincipalUnitGroup.residueTeichmullerLift F y := by
  classical
  let := Fintype.ofFinite F.residueField
  have hcard_pos : 0 < Nat.card F.residueField := by
    simpa [Nat.card_eq_fintype_card] using
      (Fintype.card_pos : 0 < Fintype.card F.residueField)
  by_cases hy : y = 0
  · simp [higherPrincipalUnitGroup.residueTeichmullerLift, hy]
  · let u : higherPrincipalUnitGroup.residueRootsOfUnityGroup F :=
      (higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F).symm
        (Units.mk0 y hy)
    have hpowUnits :
        (u : F.valuationSubringˣ) ^
            (Nat.card F.residueField - 1) = 1 :=
      u.property
    have hpowRing :
        ((u : F.valuationSubringˣ) : F.valuationSubring) ^
            (Nat.card F.residueField - 1) = 1 := by
      simpa using
        congrArg (fun z : F.valuationSubringˣ => (z : F.valuationSubring))
          hpowUnits
    have hpow :
        ((u : F.valuationSubringˣ) : F.valuationSubring) ^
            Nat.card F.residueField =
          ((u : F.valuationSubringˣ) : F.valuationSubring) := by
      calc
        ((u : F.valuationSubringˣ) : F.valuationSubring) ^
            Nat.card F.residueField =
            ((u : F.valuationSubringˣ) : F.valuationSubring) ^
              ((Nat.card F.residueField - 1) + 1) := by
              rw [Nat.sub_one_add_one_eq_of_pos hcard_pos]
        _ =
            ((u : F.valuationSubringˣ) : F.valuationSubring) ^
              (Nat.card F.residueField - 1) *
            ((u : F.valuationSubringˣ) : F.valuationSubring) := by
              rw [pow_succ]
        _ = ((u : F.valuationSubringˣ) : F.valuationSubring) := by
              rw [hpowRing, one_mul]
    simpa [higherPrincipalUnitGroup.residueTeichmullerLift, hy, u] using hpow

/--
Every residue Teichmüller lift is a root of the polynomial `X^q - X`, where `q` is the
residue-field cardinality.
-/
theorem residueTeichmullerLift_isRoot_X_pow_card_sub_X
    [Finite F.residueField] (y : F.residueField) :
    (Polynomial.X ^ Nat.card F.residueField - Polynomial.X :
        Polynomial F.valuationSubring).IsRoot
      (higherPrincipalUnitGroup.residueTeichmullerLift F y) := by
  rw [Polynomial.IsRoot.def]
  simp [Polynomial.eval_sub,
    higherPrincipalUnitGroup.residueTeichmullerLift_pow_card]

/-- In equal characteristic, `T^q - T` has unit derivative at every
Teichmuller representative. -/
theorem residueTeichmullerRootPolynomial_derivative_eval_isUnit_of_charP
    [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (y : F.residueField) :
    IsUnit
      (((Polynomial.X ^ Nat.card F.residueField - Polynomial.X :
          Polynomial F.valuationSubring).derivative).eval
        (higherPrincipalUnitGroup.residueTeichmullerLift F y)) := by
  have hp_dvd_card : p ∣ Nat.card F.residueField := by
    rw [hcard]
    exact dvd_pow_self p n.ne_zero
  have hcard_cast :
      ((Nat.card F.residueField : ℕ) : F.valuationSubring) = 0 :=
    (CharP.cast_eq_zero_iff F.valuationSubring p
      (Nat.card F.residueField)).2 hp_dvd_card
  have hderiv :
      ((Polynomial.X ^ Nat.card F.residueField - Polynomial.X :
          Polynomial F.valuationSubring).derivative).eval
        (higherPrincipalUnitGroup.residueTeichmullerLift F y) = -1 := by
    simp [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_X, hcard_cast]
  rw [hderiv]
  exact isUnit_neg_one

/-- In equal characteristic, the Teichmuller lift from the finite residue field
to the valuation ring is additive. -/
theorem residueTeichmullerLift_add_of_charP [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (x y : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerLift F (x + y) =
      higherPrincipalUnitGroup.residueTeichmullerLift F x +
        higherPrincipalUnitGroup.residueTeichmullerLift F y := by
  let f : Polynomial F.valuationSubring :=
    Polynomial.X ^ Nat.card F.residueField - Polynomial.X
  let a : F.valuationSubring :=
    higherPrincipalUnitGroup.residueTeichmullerLift F (x + y)
  let b : F.valuationSubring :=
    higherPrincipalUnitGroup.residueTeichmullerLift F x +
      higherPrincipalUnitGroup.residueTeichmullerLift F y
  have ha : f.IsRoot a := by
    simpa [f, a] using
      higherPrincipalUnitGroup.residueTeichmullerLift_isRoot_X_pow_card_sub_X
        (F := F) (x + y)
  have hb : f.IsRoot b := by
    rw [Polynomial.IsRoot.def]
    have hxpow :=
      higherPrincipalUnitGroup.residueTeichmullerLift_pow_card (F := F) x
    have hypow :=
      higherPrincipalUnitGroup.residueTeichmullerLift_pow_card (F := F) y
    have hfresh :
        b ^ (p ^ (n : ℕ)) =
          higherPrincipalUnitGroup.residueTeichmullerLift F x ^
              (p ^ (n : ℕ)) +
            higherPrincipalUnitGroup.residueTeichmullerLift F y ^
              (p ^ (n : ℕ)) := by
      simpa [b] using
        add_pow_char_pow
          (higherPrincipalUnitGroup.residueTeichmullerLift F x)
          (higherPrincipalUnitGroup.residueTeichmullerLift F y)
          p (n : ℕ)
    have hxpow' :
        higherPrincipalUnitGroup.residueTeichmullerLift F x ^
            (p ^ (n : ℕ)) =
          higherPrincipalUnitGroup.residueTeichmullerLift F x := by
      simpa [hcard] using hxpow
    have hypow' :
        higherPrincipalUnitGroup.residueTeichmullerLift F y ^
            (p ^ (n : ℕ)) =
          higherPrincipalUnitGroup.residueTeichmullerLift F y := by
      simpa [hcard] using hypow
    have hbpow : b ^ Nat.card F.residueField = b := by
      rw [hcard, hfresh]
      rw [hxpow', hypow']
    simp [f, b, Polynomial.eval_sub, hbpow]
  have hres : F.residueMap b = F.residueMap a := by
    simp [a, b, map_add,
      higherPrincipalUnitGroup.residueMap_residueTeichmullerLift]
  have hderiv : IsUnit (f.derivative.eval a) := by
    simpa [f, a] using
      higherPrincipalUnitGroup.residueTeichmullerRootPolynomial_derivative_eval_isUnit_of_charP
        (F := F) p hcard (x + y)
  have hba : b = a :=
    F.toHenselianDVF.eq_of_isRoot_of_isRoot_of_residue_eq_of_derivative_isUnit
      (f := f) ha hb hres hderiv
  simpa [a, b] using hba.symm

/-- In equal characteristic, the Teichmuller lift is a ring homomorphic
coefficient-field section of the residue map. -/
noncomputable def residueTeichmullerRingHomOfCharP
    [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ)) :
    F.residueField →+* F.valuationSubring where
  toFun := higherPrincipalUnitGroup.residueTeichmullerLift F
  map_zero' := by
    exact higherPrincipalUnitGroup.residueTeichmullerLift_zero (F := F)
  map_one' := by
    exact higherPrincipalUnitGroup.residueTeichmullerLift_one (F := F)
  map_mul' := fun x y =>
    higherPrincipalUnitGroup.residueTeichmullerLift_mul (F := F) x y
  map_add' := fun x y =>
    higherPrincipalUnitGroup.residueTeichmullerLift_add_of_charP
      (F := F) p hcard x y

/--
The defining evaluation formula for `residueTeichmullerRingHomOfCharP` is
`higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP (F := F) p hcard x =
higherPrincipalUnitGroup.residueTeichmullerLift F x`.
-/
@[simp] theorem residueTeichmullerRingHomOfCharP_apply
    [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (x : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP
        (F := F) p hcard x =
      higherPrincipalUnitGroup.residueTeichmullerLift F x :=
  rfl

/-- The corresponding coefficient-field embedding into the fraction field. -/
noncomputable def residueTeichmullerFieldHomOfCharP
    [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ)) :
    F.residueField →+* K :=
  F.valuation.valuationSubring.subtype.comp
    (higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP
      (F := F) p hcard)

/--
The defining evaluation formula for `residueTeichmullerFieldHomOfCharP` is
`higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP (F := F) p hcard x =
(higherPrincipalUnitGroup.residueTeichmullerLift F x : K)`.
-/
@[simp] theorem residueTeichmullerFieldHomOfCharP_apply
    [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (x : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP
        (F := F) p hcard x =
      (higherPrincipalUnitGroup.residueTeichmullerLift F x : K) :=
  rfl
end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnits_TeichmullerDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.normSubgroupClassInZeroQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.residueDegreeClassSubgroup_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.ofWithZeroValuation_val _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientZeroSubgroupEquivValueSubgroup_norm_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.toAdd_quotientZeroSubgroupEquivValueSubgroup_norm_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.toAdd_valuationHom_apply_norm _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valuationHom_apply_norm _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valuationHom_apply_norm_div _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valuation_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valuation_apply_div _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valuation_apply_uniformizer_pow _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valuation_apply_uniformizer_zpow _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.valueModResidueDegreeHom_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_uniformizerClass_zpow _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.zeroQuotientModuloResidueDegreeClassEquivNormClass_uniformizerClass_zpow _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
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

/-- Multiplication of a Teichmuller representative and a first principal unit,
as a homomorphism into the full valuation-ring unit group. -/
def residueRootsTimesPrincipalUnitMulHom
    [Finite F.residueField] :
    higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
        higherPrincipalUnitGroup F 1 →*
      F.valuationSubringˣ where
  toFun z := (z.1 : F.valuationSubringˣ) * (z.2 : F.valuationSubringˣ)
  map_one' := by
    simp
  map_mul' := by
    intro x y
    simp [mul_left_comm, mul_comm]

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F)`.
-/
theorem residueRootsTimesPrincipalUnitMulHom_surjective
    [Finite F.residueField] :
    Function.Surjective
      (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F) := by
  intro u
  rcases higherPrincipalUnitGroup.residueRootsOfUnityResidueHom_surjective
      (F := F) (higherPrincipalUnitGroup.residueUnitHom F u) with
    ⟨zeta, hzeta⟩
  have hzeta' :
      higherPrincipalUnitGroup.residueUnitHom F
          (zeta : F.valuationSubringˣ) =
        higherPrincipalUnitGroup.residueUnitHom F u := by
    simpa [higherPrincipalUnitGroup.residueRootsOfUnityResidueHom] using hzeta
  let p : F.valuationSubringˣ := (zeta : F.valuationSubringˣ)⁻¹ * u
  have hp : p ∈ higherPrincipalUnitGroup F 1 := by
    rw [← higherPrincipalUnitGroup.residueUnitHom_eq_one_iff F p]
    dsimp [p]
    rw [map_mul, map_inv, hzeta']
    simp
  refine ⟨(zeta, ⟨p, hp⟩), ?_⟩
  change (zeta : F.valuationSubringˣ) * p = u
  dsimp [p]
  simp

/--
The specified map is injective: `Function.Injective
(higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F)`.
-/
theorem residueRootsTimesPrincipalUnitMulHom_injective
    [Finite F.residueField] :
    Function.Injective
      (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F) := by
  intro x y hxy
  have hxprincipal :
      higherPrincipalUnitGroup.residueUnitHom F
          (x.2 : F.valuationSubringˣ) = 1 :=
    (higherPrincipalUnitGroup.residueUnitHom_eq_one_iff
      F (x.2 : F.valuationSubringˣ)).2 x.2.property
  have hyprincipal :
      higherPrincipalUnitGroup.residueUnitHom F
          (y.2 : F.valuationSubringˣ) = 1 :=
    (higherPrincipalUnitGroup.residueUnitHom_eq_one_iff
      F (y.2 : F.valuationSubringˣ)).2 y.2.property
  have hmul :
      (x.1 : F.valuationSubringˣ) * (x.2 : F.valuationSubringˣ) =
        (y.1 : F.valuationSubringˣ) * (y.2 : F.valuationSubringˣ) := by
    simpa [higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom]
      using hxy
  have hresroot :
      higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F x.1 =
        higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F y.1 := by
    have hres :=
      congrArg (higherPrincipalUnitGroup.residueUnitHom F) hmul
    simpa [higherPrincipalUnitGroup.residueRootsOfUnityResidueHom,
      map_mul, hxprincipal, hyprincipal] using hres
  have hroot :
      x.1 = y.1 :=
    higherPrincipalUnitGroup.residueRootsOfUnityResidueHom_injective
      (F := F) hresroot
  apply Prod.ext
  · exact hroot
  · apply Subtype.ext
    calc
      (x.2 : F.valuationSubringˣ) =
          (x.1 : F.valuationSubringˣ)⁻¹ *
            ((x.1 : F.valuationSubringˣ) *
              (x.2 : F.valuationSubringˣ)) := by
        simp
      _ = (x.1 : F.valuationSubringˣ)⁻¹ *
            ((y.1 : F.valuationSubringˣ) *
              (y.2 : F.valuationSubringˣ)) := by
        rw [hmul]
      _ = (y.1 : F.valuationSubringˣ)⁻¹ *
            ((y.1 : F.valuationSubringˣ) *
              (y.2 : F.valuationSubringˣ)) := by
        rw [hroot]
      _ = (y.2 : F.valuationSubringˣ) := by
        simp

/--
The specified map is bijective: `Function.Bijective
(higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F)`.
-/
theorem residueRootsTimesPrincipalUnitMulHom_bijective
    [Finite F.residueField] :
    Function.Bijective
      (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F) :=
  ⟨higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom_injective F,
    higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom_surjective F⟩

/-- Unit-level form of the multiplicative unit decomposition:
`O^*` is the product of the lifted `(q - 1)`-roots of unity and `U^1`. -/
noncomputable def valuationSubringUnitsEquivRootsTimesPrincipalUnits
    [Finite F.residueField] :
    higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
        higherPrincipalUnitGroup F 1 ≃*
      F.valuationSubringˣ :=
  MulEquiv.ofBijective
    (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom F)
    (higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom_bijective F)

/--
The defining evaluation formula for `valuationSubringUnitsEquivRootsTimesPrincipalUnits` is
`higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits F z = (z.1 :
F.valuationSubringˣ) * (z.2 : F.valuationSubringˣ)`.
-/
@[simp] theorem valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply
    [Finite F.residueField]
    (z :
      higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
        higherPrincipalUnitGroup F 1) :
    higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F z =
      (z.1 : F.valuationSubringˣ) * (z.2 : F.valuationSubringˣ) :=
  rfl

/-- The natural inclusion of valuation-ring units into field units, kept local
to the principal-unit API to state the field-unit form of the multiplicative unit decomposition. -/
def valuationSubringUnitFieldUnitHom :
    F.valuationSubringˣ →* Kˣ :=
  Units.map F.valuation.valuationSubring.subtype.toMonoidHom

/--
The defining evaluation formula for `coe_valuationSubringUnitFieldUnitHom` is
`((higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u : Kˣ) : K) = (u :
F.valuationSubring)`.
-/
@[simp] theorem coe_valuationSubringUnitFieldUnitHom_apply
    (u : F.valuationSubringˣ) :
    ((higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u : Kˣ) :
        K) =
      (u : F.valuationSubring) :=
  rfl

/--
The specified map is injective: `Function.Injective
(higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F)`.
-/
theorem valuationSubringUnitFieldUnitHom_injective :
    Function.Injective
      (higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F) :=
  by
    change Function.Injective
      (Units.map F.valuation.valuationSubring.subtype.toMonoidHom)
    exact
      Units.map_injective
        F.valuation.valuationSubring.subtype_injective

/-- Field-unit representative form of the multiplicative unit decomposition.

Given an existing unit-uniformizer decomposition for a normalized
integer-valued valuation whose zero subgroup is exactly the image of `O^*`,
every field unit is a product of a Teichmuller root, a first principal unit,
and a power of the chosen uniformizer. -/
theorem exists_roots_principalUnit_uniformizer_zpow
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ) (x : Kˣ) :
    ∃ ζ : higherPrincipalUnitGroup.residueRootsOfUnityGroup F,
    ∃ p : higherPrincipalUnitGroup F 1,
    ∃ n : ℤ,
      x =
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (ζ : F.valuationSubringˣ) *
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (p : F.valuationSubringˣ) *
          ϖ ^ n := by
  rcases V.exists_zeroSubgroup_mul_uniformizer_zpow hϖ x with
    ⟨u, hu, n, hx⟩
  rcases (hzero u).1 hu with ⟨a, ha⟩
  rcases
      higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom_surjective
        (F := F) a with
    ⟨zp, hzp⟩
  have hunit :
      (zp.1 : F.valuationSubringˣ) * (zp.2 : F.valuationSubringˣ) = a := by
    simpa [higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom]
      using hzp
  refine ⟨zp.1, zp.2, n, ?_⟩
  calc
    x = u * ϖ ^ n := hx
    _ =
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F a *
          ϖ ^ n := by
      rw [ha]
    _ =
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            ((zp.1 : F.valuationSubringˣ) *
              (zp.2 : F.valuationSubringˣ)) *
          ϖ ^ n := by
      rw [hunit]
    _ =
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (zp.1 : F.valuationSubringˣ) *
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (zp.2 : F.valuationSubringˣ) *
          ϖ ^ n := by
      rw [map_mul]

/-- Uniqueness of the field-unit form of the multiplicative unit decomposition:
with a fixed uniformizer, the Teichmuller representative, the first principal
unit, and the exponent are all uniquely determined. -/
theorem roots_principalUnit_uniformizer_zpow_eq_iff
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ)
    (ζ η : higherPrincipalUnitGroup.residueRootsOfUnityGroup F)
    (p q : higherPrincipalUnitGroup F 1) (m n : ℤ) :
    higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (ζ : F.valuationSubringˣ) *
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (p : F.valuationSubringˣ) *
        ϖ ^ m =
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (η : F.valuationSubringˣ) *
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (q : F.valuationSubringˣ) *
        ϖ ^ n ↔
      ζ = η ∧ p = q ∧ m = n := by
  have hleft :
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (ζ : F.valuationSubringˣ) *
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (p : F.valuationSubringˣ) ∈
        V.zeroSubgroup :=
    (hzero _).2
      ⟨(ζ : F.valuationSubringˣ) * (p : F.valuationSubringˣ), by
        rw [map_mul]⟩
  have hright :
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (η : F.valuationSubringˣ) *
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (q : F.valuationSubringˣ) ∈
        V.zeroSubgroup :=
    (hzero _).2
      ⟨(η : F.valuationSubringˣ) * (q : F.valuationSubringˣ), by
        rw [map_mul]⟩
  constructor
  · intro h
    have hnormal :=
      (V.unit_uniformizer_normal_form_eq_iff hϖ hleft hright).1 h
    rcases hnormal with ⟨hunit, hmn⟩
    have hvaluationUnit :
        (ζ : F.valuationSubringˣ) * (p : F.valuationSubringˣ) =
          (η : F.valuationSubringˣ) * (q : F.valuationSubringˣ) :=
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_injective
        (F := F)
        (by
          simpa [map_mul] using hunit)
    have hpair :
        (ζ, p) = (η, q) :=
      higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom_injective
        (F := F)
        (by
          simpa [higherPrincipalUnitGroup.residueRootsTimesPrincipalUnitMulHom]
            using hvaluationUnit)
    cases hpair
    exact ⟨rfl, rfl, hmn⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- The three factors in the multiplicative field-unit decomposition: Teichmuller roots,
first principal units, and an integral power of a fixed uniformizer. -/
abbrev fieldUnitDecompositionFactors [Finite F.residueField] :
    Type u :=
  (higherPrincipalUnitGroup.residueRootsOfUnityGroup F ×
      higherPrincipalUnitGroup F 1) × Multiplicative ℤ

/--
Multiplication map from the three the multiplicative unit decomposition factors to field units.
-/
noncomputable def rootsPrincipalUnitUniformizerMulHom
    [Finite F.residueField] (ϖ : Kˣ) :
    higherPrincipalUnitGroup.fieldUnitDecompositionFactors F →* Kˣ where
  toFun z :=
    higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
        (z.1.1 : F.valuationSubringˣ) *
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
        (z.1.2 : F.valuationSubringˣ) *
      ϖ ^ Multiplicative.toAdd z.2
  map_one' := by
    simp
  map_mul' := by
    intro x y
    simp [higherPrincipalUnitGroup.fieldUnitDecompositionFactors,
      mul_assoc, mul_left_comm, mul_comm, zpow_add]

/--
The defining evaluation formula for `rootsPrincipalUnitUniformizerMulHom` is
`higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ z =
higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F (z.1.1 : F.valuationSubringˣ) *
higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F (z.1.2 : F.valuationSubringˣ) * ϖ ^
Multiplicative.toAdd z.2`.
-/
@[simp] theorem rootsPrincipalUnitUniformizerMulHom_apply
    [Finite F.residueField] (ϖ : Kˣ)
    (z : higherPrincipalUnitGroup.fieldUnitDecompositionFactors F) :
    higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ z =
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (z.1.1 : F.valuationSubringˣ) *
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (z.1.2 : F.valuationSubringˣ) *
        ϖ ^ Multiplicative.toAdd z.2 :=
  rfl

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ)`.
-/
theorem rootsPrincipalUnitUniformizerMulHom_surjective
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ) :
    Function.Surjective
      (higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ) := by
  intro x
  rcases
      higherPrincipalUnitGroup.exists_roots_principalUnit_uniformizer_zpow
        (F := F) V hzero hϖ x with
    ⟨ζ, p, n, hx⟩
  refine ⟨((ζ, p), Multiplicative.ofAdd n), ?_⟩
  exact hx.symm

/--
The specified map is injective: `Function.Injective
(higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ)`.
-/
theorem rootsPrincipalUnitUniformizerMulHom_injective
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ) :
    Function.Injective
      (higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ) := by
  rintro ⟨⟨ζ, p⟩, m⟩ ⟨⟨η, q⟩, n⟩ h
  have hmul :
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (ζ : F.valuationSubringˣ) *
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (p : F.valuationSubringˣ) *
          ϖ ^ Multiplicative.toAdd m =
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (η : F.valuationSubringˣ) *
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
            (q : F.valuationSubringˣ) *
          ϖ ^ Multiplicative.toAdd n := by
    exact h
  have hdecomp :=
    (higherPrincipalUnitGroup.roots_principalUnit_uniformizer_zpow_eq_iff
      (F := F) V hzero hϖ ζ η p q
        (Multiplicative.toAdd m) (Multiplicative.toAdd n)).1 hmul
  rcases hdecomp with ⟨hζη, hpq, hmn⟩
  have hmn' : m = n :=
    Multiplicative.toAdd.injective hmn
  simp [hζη, hpq, hmn']

/--
The specified map is bijective: `Function.Bijective
(higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ)`.
-/
theorem rootsPrincipalUnitUniformizerMulHom_bijective
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ) :
    Function.Bijective
      (higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ) :=
  ⟨higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_injective
      (F := F) V hzero hϖ,
    higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_surjective
      (F := F) V hzero hϖ⟩

/-- Group-isomorphism form of the multiplicative unit decomposition: after fixing
a uniformizer, `Kˣ` is the product of the lifted residue roots of unity, the
first principal units, and the infinite cyclic uniformizer factor. -/
noncomputable def fieldUnitsEquivRootsPrincipalUnitsUniformizer
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ) :
    higherPrincipalUnitGroup.fieldUnitDecompositionFactors F ≃* Kˣ :=
  MulEquiv.ofBijective
    (higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom F ϖ)
    (higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_bijective
      (F := F) V hzero hϖ)

/--
The defining evaluation formula for `fieldUnitsEquivRootsPrincipalUnitsUniformizer` is
`higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer (F := F) V hzero hϖ z =
higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F (z.1.1 : F.valuationSubringˣ) *
higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F (z.1.2 : F.valuationSubringˣ) * ϖ ^
Multiplicative.toAdd z.2`.
-/
@[simp] theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply
    [Finite F.residueField]
    (V : MultiplicativeIntegerValuation Kˣ)
    (hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F u = y)
    {ϖ : Kˣ} (hϖ : V.IsUniformizer ϖ)
    (z : higherPrincipalUnitGroup.fieldUnitDecompositionFactors F) :
    higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer
        (F := F) V hzero hϖ z =
      higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (z.1.1 : F.valuationSubringˣ) *
        higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom F
          (z.1.2 : F.valuationSubringˣ) *
        ϖ ^ Multiplicative.toAdd z.2 :=
  rfl

end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnits_Core
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesCommGroup _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Develops quotients of valuation-ring units by higher principal units and compares their first
layer with residue-field units.
-/

namespace LocalFieldTheory

open ValuationTheory

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

open ValuationTheory.DiscreteValuationField.DVF

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- Reduction of valuation-ring units modulo the `n`-th power of the maximal
ideal. -/
def quotientUnitHom (n : ℕ) :
    F.valuationSubringˣ →*
      (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ :=
  Units.map (Ideal.Quotient.mk (F.maximalIdeal ^ n))

/--
The defining evaluation formula for `quotientUnitHom` is
`((higherPrincipalUnitGroup.quotientUnitHom F n u : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
F.valuationSubring ⧸ F.maximalIdeal ^ n) = Ideal.Quotient.mk (F.maximalIdeal ^ n) (u :
F.valuationSubring)`.
-/
@[simp] theorem quotientUnitHom_apply (n : ℕ) (u : F.valuationSubringˣ) :
    ((higherPrincipalUnitGroup.quotientUnitHom F n u :
        (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ) :
      F.valuationSubring ⧸ F.maximalIdeal ^ n) =
      Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) :=
  rfl

/-- The kernel of unit reduction modulo `m^n` is exactly the concrete
principal-unit subgroup `U^n`. -/
theorem quotientUnitHom_ker_eq (n : ℕ) :
    (higherPrincipalUnitGroup.quotientUnitHom F n).ker =
      higherPrincipalUnitGroup F n := by
  ext u
  rw [MonoidHom.mem_ker, higherPrincipalUnitGroup.mem_iff]
  constructor
  · intro hu
    have hval := congrArg
      (fun z : (F.valuationSubring ⧸ F.maximalIdeal ^ n)ˣ =>
        (z : F.valuationSubring ⧸ F.maximalIdeal ^ n)) hu
    change
      Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) =
        1 at hval
    have hmk :
        Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) =
          Ideal.Quotient.mk (F.maximalIdeal ^ n)
            (1 : F.valuationSubring) := by
      simpa using hval
    exact
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ n) (u : F.valuationSubring)
        (1 : F.valuationSubring)).1 hmk
  · intro hu
    apply Units.ext
    change
      Ideal.Quotient.mk (F.maximalIdeal ^ n) (u : F.valuationSubring) =
        1
    simpa using
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := F.maximalIdeal ^ n) (u : F.valuationSubring)
        (1 : F.valuationSubring)).2 hu

/-- First-isomorphism form of unit reduction modulo `m^n`: `O^*/U^n` is the
range of the unit group of `O/m^n`. -/
noncomputable def unitsModHigherPrincipalUnitGroupEquivRange (n : ℕ) :
    F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n ≃*
      (higherPrincipalUnitGroup.quotientUnitHom F n).range :=
  (QuotientGroup.quotientMulEquivOfEq
    (higherPrincipalUnitGroup.quotientUnitHom_ker_eq F n).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (higherPrincipalUnitGroup.quotientUnitHom F n))

/-- The maximal ideal of a complete DVF valuation ring is finitely generated:
it is generated by any uniformizer. -/
theorem maximalIdeal_fg :
    F.maximalIdeal.FG := by
  rcases F.exists_uniformizer with ⟨pi, hpi⟩
  refine ⟨{pi}, ?_⟩
  simpa using (F.maximalIdeal_eq_span_uniformizer hpi).symm

/-- If the residue field is finite, then every quotient by a power of the
maximal ideal is finite. -/
theorem finite_quotient_maximalIdeal_pow_of_finite_residue
    [Finite F.residueField] (n : ℕ) :
    Finite (F.valuationSubring ⧸ F.maximalIdeal ^ n) := by
  have : Finite (F.valuationSubring ⧸ F.maximalIdeal) := by
    change Finite F.residueField
    infer_instance
  exact Ideal.finite_quotient_pow
    (I := F.maximalIdeal) (higherPrincipalUnitGroup.maximalIdeal_fg F) n

/-- Finite-residue complete DVFs have finite unit quotients `O^*/U^n`. -/
theorem finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
    [Finite F.residueField] (n : ℕ) :
    Finite (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n) := by
  have : Finite (F.valuationSubring ⧸ F.maximalIdeal ^ n) :=
    higherPrincipalUnitGroup.finite_quotient_maximalIdeal_pow_of_finite_residue
      F n
  exact
    Finite.of_equiv
      ((higherPrincipalUnitGroup.quotientUnitHom F n).range)
      (higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupEquivRange F n).symm

/-- Every concrete principal-unit subquotient is finite when the residue
field is finite.  It is identified with the range of the inclusion into the
finite full unit quotient. -/
theorem finite_principalUnitSubquotient_of_finite_residue
    [Finite F.residueField] (m n : ℕ) :
    Finite (higherPrincipalUnitGroup F m ⧸
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m)) := by
  let : Finite
      (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n) := by
    exact
      higherPrincipalUnitGroup.finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
        F n
  let f : higherPrincipalUnitGroup F m →*
      F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n :=
    (QuotientGroup.mk' (higherPrincipalUnitGroup F n)).comp
      (higherPrincipalUnitGroup F m).subtype
  have hker : f.ker =
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change QuotientGroup.mk' (higherPrincipalUnitGroup F n)
        (x : F.valuationSubringˣ) = 1 ↔
      (x : F.valuationSubringˣ) ∈ higherPrincipalUnitGroup F n
    exact QuotientGroup.eq_one_iff
      (N := higherPrincipalUnitGroup F n) (x : F.valuationSubringˣ)
  let e : (higherPrincipalUnitGroup F m ⧸
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m)) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  exact Finite.of_equiv f.range e.symm

/-- The concrete principal-unit filtration as the abstract filtration API. -/
def toPrincipalUnitFiltration :
    AntitoneSubgroupFiltration F.valuationSubringˣ where
  subgroup := higherPrincipalUnitGroup F
  antitone := fun h => higherPrincipalUnitGroup.antitone F h

/--
Establishes the identity `(higherPrincipalUnitGroup.toPrincipalUnitFiltration F).subgroup n =
higherPrincipalUnitGroup F n`.
-/
@[simp] theorem toPrincipalUnitFiltration_subgroup (n : ℕ) :
    (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).subgroup n =
      higherPrincipalUnitGroup F n :=
  rfl

/-! ### Successive principal-unit quotients -/

/-- The adjacent quotient `U^n/U^(n+1)` for the concrete complete-DVF
principal-unit filtration. -/
def principalUnitSuccQuot (n : ℕ) : Type u :=
  higherPrincipalUnitGroup F n ⧸
    (higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)

/--
Equips the target with its canonical `CommGroup` structure, namely `CommGroup
(higherPrincipalUnitGroup.principalUnitSuccQuot F n)`.
-/
instance principalUnitSuccQuotCommGroup (n : ℕ) :
    CommGroup (higherPrincipalUnitGroup.principalUnitSuccQuot F n) := by
  change CommGroup
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  infer_instance

/-- Explicit access to the concrete quotient used to implement
`principalUnitSuccQuot`. -/
def principalUnitSuccQuotConcreteEquiv (n : ℕ) :
    higherPrincipalUnitGroup.principalUnitSuccQuot F n ≃*
      (higherPrincipalUnitGroup F n ⧸
        (higherPrincipalUnitGroup F (n + 1)).subgroupOf
          (higherPrincipalUnitGroup F n)) := by
  change
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) ≃*
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  exact MulEquiv.refl _

/-- The quotient map `U^n → U^n/U^(n+1)`. -/
def principalUnitSuccQuotMk (n : ℕ) :
    higherPrincipalUnitGroup F n →*
      higherPrincipalUnitGroup.principalUnitSuccQuot F n := by
  change higherPrincipalUnitGroup F n →*
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  exact QuotientGroup.mk' ((higherPrincipalUnitGroup F (n + 1)).subgroupOf
    (higherPrincipalUnitGroup F n))

/--
Establishes the identity `higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv F n
(higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) = QuotientGroup.mk u`.
-/
@[simp] theorem principalUnitSuccQuotConcreteEquiv_mk (n : ℕ)
    (u : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv F n
        (higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) =
      QuotientGroup.mk u :=
  rfl

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.principalUnitSuccQuotMk F n)`.
-/
theorem principalUnitSuccQuotMk_surjective (n : ℕ) :
    Function.Surjective (higherPrincipalUnitGroup.principalUnitSuccQuotMk F n) :=
  QuotientGroup.mk'_surjective ((higherPrincipalUnitGroup F (n + 1)).subgroupOf
    (higherPrincipalUnitGroup F n))

/-- Descend a homomorphism from `U^n` that kills `U^(n+1)`. -/
def principalUnitSuccQuotLift
    {H : Type*} [Group H] (n : ℕ)
    (f : higherPrincipalUnitGroup F n →* H)
    (h : (higherPrincipalUnitGroup F (n + 1)).subgroupOf
      (higherPrincipalUnitGroup F n) ≤ f.ker) :
    higherPrincipalUnitGroup.principalUnitSuccQuot F n →* H := by
  change
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) →* H
  exact QuotientGroup.lift
    ((higherPrincipalUnitGroup F (n + 1)).subgroupOf
      (higherPrincipalUnitGroup F n)) f h

/--
Establishes the identity `higherPrincipalUnitGroup.principalUnitSuccQuotLift F n f h
(higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) = f u`.
-/
@[simp] theorem principalUnitSuccQuotLift_mk
    {H : Type*} [Group H] (n : ℕ)
    (f : higherPrincipalUnitGroup F n →* H)
    (h : (higherPrincipalUnitGroup F (n + 1)).subgroupOf
      (higherPrincipalUnitGroup F n) ≤ f.ker)
    (u : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotLift F n f h
        (higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) = f u :=
  rfl

/-- The concrete complete-DVF adjacent quotient agrees with the generic
graded-piece wrapper through explicit public equivalences. -/
def principalUnitSuccQuotEquivGradedPiece (n : ℕ) :
    higherPrincipalUnitGroup.principalUnitSuccQuot F n ≃*
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitGradedPiece n :=
  (higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv F n).trans
    ((AntitoneSubgroupFiltration.principalUnitGradedPieceEquivSubquotient
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) n).trans
      (AntitoneSubgroupFiltration.principalUnitSubquotientConcreteEquiv
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) n (n + 1))).symm

/--
Establishes the identity `higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece F n
(higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) =
(higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitGradedPieceMk n u`.
-/
@[simp] theorem principalUnitSuccQuotEquivGradedPiece_mk
    (n : ℕ) (u : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece F n
        (higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u) =
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitGradedPieceMk
        n u :=
  rfl

/--
Characterizes `higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u = 1` by the equivalent
condition `u ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)`.
-/
theorem principalUnitSuccQuotMk_eq_one_iff (n : ℕ)
    (u : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u = 1 ↔
      u ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n) := by
  change
    ((u : higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) = 1 ↔ _)
  exact QuotientGroup.eq_one_iff u

/--
Characterizes `higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u =
higherPrincipalUnitGroup.principalUnitSuccQuotMk F n v` by the equivalent condition `u / v ∈
(higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)`.
-/
theorem principalUnitSuccQuotMk_eq_iff_div_mem (n : ℕ)
    (u v : higherPrincipalUnitGroup F n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotMk F n u =
        higherPrincipalUnitGroup.principalUnitSuccQuotMk F n v ↔
      u / v ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n) := by
  change
    ((u : higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) =
      (v : higherPrincipalUnitGroup F n ⧸
        (higherPrincipalUnitGroup F (n + 1)).subgroupOf
          (higherPrincipalUnitGroup F n)) ↔ _)
  exact QuotientGroup.eq_iff_div_mem

/--
Characterizes `u ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)`
by the equivalent condition `((u : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈ F.maximalIdeal
^ (n + 1)`.
-/
theorem mem_succ_subgroupOf_iff (n : ℕ)
    (u : higherPrincipalUnitGroup F n) :
    u ∈ (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n) ↔
      ((u : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈
        F.maximalIdeal ^ (n + 1) := by
  rw [Subgroup.mem_subgroupOf, higherPrincipalUnitGroup.mem_iff]

/-- If `a ∈ m^n` with `n ≥ 1`, then `1 + a` is a unit of the valuation ring. -/
theorem isUnit_one_add_of_mem_maximalIdeal_pow {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) : IsUnit (1 + a) := by
  have ha1 : a ∈ F.maximalIdeal := by
    have hle : F.maximalIdeal ^ n ≤ F.maximalIdeal ^ 1 :=
      Ideal.pow_le_pow_right hn
    simpa using hle ha
  have hnon : (-a) ∈ nonunits F.valuationSubring := by
    rw [← IsLocalRing.mem_maximalIdeal]
    exact F.maximalIdeal.neg_mem ha1
  have hunit : IsUnit (1 - (-a)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-a) hnon
  simpa [sub_neg_eq_add] using hunit

/-- The unit `1 + a` attached to an element `a ∈ m^n`, for `n ≥ 1`. -/
noncomputable def principalUnitOneAddOfMemPow {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) : F.valuationSubringˣ :=
  (higherPrincipalUnitGroup.isUnit_one_add_of_mem_maximalIdeal_pow F hn a ha).unit

/--
Establishes the identity `((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha :
F.valuationSubringˣ) : F.valuationSubring) = 1 + a`.
-/
@[simp] theorem principalUnitOneAddOfMemPow_val {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) :
    ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha :
        F.valuationSubringˣ) : F.valuationSubring) =
      1 + a :=
  IsUnit.unit_spec
    (higherPrincipalUnitGroup.isUnit_one_add_of_mem_maximalIdeal_pow F hn a ha)

/-- The unit `1 + a`, viewed as an element of `U^n`. -/
noncomputable def principalUnitOneAddOfMemPowSubgroup {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) :
    higherPrincipalUnitGroup F n :=
  ⟨higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha, by
    rw [higherPrincipalUnitGroup.mem_iff]
    simp [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val, ha]
  ⟩

/--
Establishes the identity `((higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a ha
: higherPrincipalUnitGroup F n) : F.valuationSubringˣ) =
higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha`.
-/
@[simp] theorem principalUnitOneAddOfMemPowSubgroup_val {n : ℕ} (hn : 1 ≤ n)
    (a : F.valuationSubring) (ha : a ∈ F.maximalIdeal ^ n) :
    ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a ha :
        higherPrincipalUnitGroup F n) : F.valuationSubringˣ) =
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn a ha :=
  rfl

/-- The concrete map `m^n → U^n/U^(n+1)` sending `a` to the class of
`1 + a`. -/
noncomputable def principalUnitSuccQuotOfIdealPow (n : ℕ) (hn : 1 ≤ n) :
    ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) →
      higherPrincipalUnitGroup.principalUnitSuccQuot F n :=
  fun a =>
    higherPrincipalUnitGroup.principalUnitSuccQuotMk F n
      (higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a.1 a.2)

/--
The defining evaluation formula for `principalUnitSuccQuotOfIdealPow` is
`higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a =
higherPrincipalUnitGroup.principalUnitSuccQuotMk F n
(higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a.1 a.2)`.
-/
@[simp] theorem principalUnitSuccQuotOfIdealPow_apply (n : ℕ) (hn : 1 ≤ n)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a =
      higherPrincipalUnitGroup.principalUnitSuccQuotMk F n
        (higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup F hn a.1 a.2) :=
  rfl

/-- Elements of `m^(n+1)` map to the trivial class in `U^n/U^(n+1)`. -/
theorem principalUnitSuccQuotOfIdealPow_eq_one_of_mem_succ
    (n : ℕ) (hn : 1 ≤ n)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u))
    (ha : (a : F.valuationSubring) ∈ F.maximalIdeal ^ (n + 1)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a = 1 := by
  apply (higherPrincipalUnitGroup.principalUnitSuccQuotMk_eq_one_iff F n _).2
  rw [higherPrincipalUnitGroup.mem_succ_subgroupOf_iff]
  simp [higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup,
    higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val, ha]

/-- The map `a ↦ [1 + a]` is insensitive to changing `a` modulo `m^(n+1)`. -/
theorem principalUnitSuccQuotOfIdealPow_eq_of_sub_mem_succ
    (n : ℕ) (hn : 1 ≤ n)
    (a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u))
    (hab : ((a : F.valuationSubring) - (b : F.valuationSubring)) ∈
      F.maximalIdeal ^ (n + 1)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn b := by
  apply (higherPrincipalUnitGroup.principalUnitSuccQuotMk_eq_iff_div_mem F n _ _).2
  rw [higherPrincipalUnitGroup.mem_succ_subgroupOf_iff]
  change (((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (a : F.valuationSubring) a.2 /
          higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
        F.valuationSubring) - 1) ∈ F.maximalIdeal ^ (n + 1)
  rw [show (((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (a : F.valuationSubring) a.2 /
          higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
        F.valuationSubring) - 1) =
      ((a : F.valuationSubring) - (b : F.valuationSubring)) *
        ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
          (b : F.valuationSubring) b.2)⁻¹ by
    simp only [div_eq_mul_inv, Units.val_mul]
    rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
      (a : F.valuationSubring) a.2]
    have hbval :
        ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
          F.valuationSubring) = 1 + (b : F.valuationSubring) :=
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
        (b : F.valuationSubring) b.2
    have hbinv :
        ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
          F.valuationSubring) *
          ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            (b : F.valuationSubring) b.2)⁻¹ = 1 := by
      simp
    calc
      (1 + (a : F.valuationSubring)) *
            ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (b : F.valuationSubring) b.2)⁻¹ - 1 =
          (1 + (a : F.valuationSubring)) *
              ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                (b : F.valuationSubring) b.2)⁻¹ -
            ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                (b : F.valuationSubring) b.2 : F.valuationSubringˣ) :
              F.valuationSubring) *
              ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                (b : F.valuationSubring) b.2)⁻¹ := by
        rw [hbinv]
      _ = ((a : F.valuationSubring) - (b : F.valuationSubring)) *
            ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (b : F.valuationSubring) b.2)⁻¹ := by
        rw [hbval]
        ring]
  exact (F.maximalIdeal ^ (n + 1)).mul_mem_right _ hab

/-- The class `[1+a]` is trivial exactly when `a ∈ m^(n+1)`. -/
theorem principalUnitSuccQuotOfIdealPow_eq_one_iff
    (n : ℕ) (hn : 1 ≤ n)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a = 1 ↔
      (a : F.valuationSubring) ∈ F.maximalIdeal ^ (n + 1) := by
  constructor
  · intro h
    have hmem :=
      (higherPrincipalUnitGroup.principalUnitSuccQuotMk_eq_one_iff F n _).1 h
    rw [higherPrincipalUnitGroup.mem_succ_subgroupOf_iff] at hmem
    simpa [higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow,
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup,
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val] using hmem
  · intro ha
    exact higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_eq_one_of_mem_succ
      F n hn a ha

/-- Products of two elements of `m^n`, for `n ≥ 1`, lie in `m^(n+1)`. -/
theorem maximalIdealPow_mul_mem_succ {n : ℕ} (hn : 1 ≤ n)
    (a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    ((a : F.valuationSubring) * (b : F.valuationSubring)) ∈
      F.maximalIdeal ^ (n + 1) := by
  have hmul :
      ((a : F.valuationSubring) * (b : F.valuationSubring)) ∈
        F.maximalIdeal ^ (n + n) := by
    simpa [pow_add] using (Ideal.mul_mem_mul a.2 b.2)
  have hle : F.maximalIdeal ^ (n + n) ≤ F.maximalIdeal ^ (n + 1) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_left hn n)
  exact hle hmul

/-- The map `a ↦ [1+a]` is additive after passing to the successive
principal-unit quotient. -/
theorem principalUnitSuccQuotOfIdealPow_add
    (n : ℕ) (hn : 1 ≤ n)
    (a b : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn (a + b) =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a *
        higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn b := by
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply,
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply,
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply,
    ← map_mul]
  symm
  apply (higherPrincipalUnitGroup.principalUnitSuccQuotMk_eq_iff_div_mem F n _ _).2
  rw [higherPrincipalUnitGroup.mem_succ_subgroupOf_iff]
  change ((((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (a : F.valuationSubring) a.2 *
            higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (b : F.valuationSubring) b.2 : F.valuationSubringˣ) /
          higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
        F.valuationSubring) - 1) ∈ F.maximalIdeal ^ (n + 1)
  rw [show ((((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (a : F.valuationSubring) a.2 *
            higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              (b : F.valuationSubring) b.2 : F.valuationSubringˣ) /
          higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
        F.valuationSubring) - 1) =
      ((a : F.valuationSubring) * (b : F.valuationSubring)) *
        ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
          ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
            F.valuationSubring) (a + b).2)⁻¹ by
    simp only [div_eq_mul_inv, Units.val_mul]
    rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
      (a : F.valuationSubring) a.2,
      higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
        (b : F.valuationSubring) b.2]
    have habval :
        ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
          F.valuationSubring) =
          1 + (a : F.valuationSubring) + (b : F.valuationSubring) := by
      rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val F hn
        ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
          F.valuationSubring) (a + b).2]
      change 1 + ((a : F.valuationSubring) + (b : F.valuationSubring)) =
        1 + (a : F.valuationSubring) + (b : F.valuationSubring)
      ring
    have habinv :
        ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
          F.valuationSubring) *
          ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
            ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
              F.valuationSubring) (a + b).2)⁻¹ = 1 := by
      simp
    calc
      ((1 + (a : F.valuationSubring)) * (1 + (b : F.valuationSubring))) *
            ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                F.valuationSubring) (a + b).2)⁻¹ - 1 =
          ((1 + (a : F.valuationSubring)) * (1 + (b : F.valuationSubring))) *
              ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                  F.valuationSubring) (a + b).2)⁻¹ -
            ((higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                  F.valuationSubring) (a + b).2 : F.valuationSubringˣ) :
              F.valuationSubring) *
              ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
                ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                  F.valuationSubring) (a + b).2)⁻¹ := by
        rw [habinv]
      _ = ((a : F.valuationSubring) * (b : F.valuationSubring)) *
            ↑(higherPrincipalUnitGroup.principalUnitOneAddOfMemPow F hn
              ((a + b : (F.maximalIdeal ^ n : Ideal F.valuationSubring)) :
                F.valuationSubring) (a + b).2)⁻¹ := by
        rw [habval]
        ring]
  exact (F.maximalIdeal ^ (n + 1)).mul_mem_right _
    (higherPrincipalUnitGroup.maximalIdealPow_mul_mem_succ F hn a b)

/-- The descent of `a ↦ [1+a]` to `m^n/m^(n+1)`. -/
noncomputable def principalUnitSuccQuotOfMaximalIdealPowSuccQuot
    (n : ℕ) (hn : 1 ≤ n) :
    _root_.ValuationTheory.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot F.toDVF n →
      higherPrincipalUnitGroup.principalUnitSuccQuot F n :=
  _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotLift
    F.toDVF n
    (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn)
    (fun a b hsub =>
      higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_eq_of_sub_mem_succ
        F n hn a b (by simpa using hsub))

/--
Establishes the identity `higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
F n hn (maximalIdealPowSuccQuotMk F.toDVF n a) =
higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a`.
-/
@[simp] theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk
    (n : ℕ) (hn : 1 ≤ n)
    (a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk F.toDVF n a) =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn a :=
  rfl

/--
`principalUnitSuccQuotOfMaximalIdealPowSuccQuot` has the zero-value formula
`higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn 0 = 1`.
-/
@[simp] theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero
    (n : ℕ) (hn : 1 ≤ n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn 0 = 1 := by
  rw [← map_zero
    (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk F.toDVF n)]
  change higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
      (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk F.toDVF n
        (0 : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u))) = 1
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk]
  exact higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_eq_one_of_mem_succ
    F n hn (0 : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u)) (by simp)

/--
`principalUnitSuccQuotOfMaximalIdealPowSuccQuot` satisfies the addition formula
`higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn (x + y) =
higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x *
higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn y`.
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_add
    (n : ℕ) (hn : 1 ≤ n)
    (x y : _root_.ValuationTheory.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot F.toDVF n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn (x + y) =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x *
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn y := by
  refine
    _root_.ValuationTheory.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot.inductionOn₂
      (motive := fun x' y' =>
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
            F n hn (x' + y') =
          higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
              F n hn x' *
            higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
              F n hn y')
      F.toDVF n x y ?_
  intro a b
  let qa :
      _root_.ValuationTheory.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot F.toDVF n :=
    _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk F.toDVF n a
  let qb :
      _root_.ValuationTheory.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot F.toDVF n :=
    _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk F.toDVF n b
  have hleft :
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
          (qa + qb) =
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
          (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk
            F.toDVF n (a + b)) := by
    have hadd : qa + qb =
        _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk
          F.toDVF n (a + b) := by
      exact (map_add
        (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk
          F.toDVF n) a b).symm
    exact congrArg
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn) hadd
  have hrep :
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
          (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk
            F.toDVF n (a + b)) =
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn qa *
          higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn qb := by
    dsimp [qa, qb]
    change higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk F.toDVF n (a + b)) =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk F.toDVF n a) *
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk F.toDVF n b)
    rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk,
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk,
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk]
    exact higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_add F n hn a b
  exact hleft.trans hrep

/-- Additive form of the descended map `m^n/m^(n+1) → U^n/U^(n+1)`. -/
noncomputable def principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd
    (n : ℕ) (hn : 1 ≤ n) :
    _root_.ValuationTheory.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot F.toDVF n →+
      Additive (higherPrincipalUnitGroup.principalUnitSuccQuot F n) where
  toFun x := Additive.ofMul
    (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x)
  map_zero' := by
    change Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn 0) = 0
    simp
  map_add' x y := by
    change Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn (x + y)) =
      Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x *
          higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn y)
    rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_add]

/--
The defining evaluation formula for `principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd` is
`higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn x =
Additive.ofMul (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
x)`.
-/
@[simp] theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply
    (n : ℕ) (hn : 1 ≤ n) (x : _root_.ValuationTheory.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot F.toDVF n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn x =
      Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x) :=
  rfl

/--
Characterizes `higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x =
1` by the equivalent condition `x = 0`.
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_eq_one_iff
    (n : ℕ) (hn : 1 ≤ n) (x : _root_.ValuationTheory.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot F.toDVF n) :
    higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x = 1 ↔
      x = 0 := by
  refine
    _root_.ValuationTheory.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot.inductionOn
      (motive := fun x' =>
        higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot
            F n hn x' = 1 ↔ x' = 0)
      F.toDVF n x ?_
  intro a
  rw [← map_zero
    (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk F.toDVF n)]
  change higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
      (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk F.toDVF n a) = 1 ↔
    (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk F.toDVF n a :
      _root_.ValuationTheory.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot F.toDVF n) = 0
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk,
    _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk_eq_zero_iff]
  exact higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_eq_one_iff F n hn a

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn)`.
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuot_surjective
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn) := by
  intro x
  rcases higherPrincipalUnitGroup.principalUnitSuccQuotMk_surjective F n x with ⟨u, rfl⟩
  let a0 : F.valuationSubring := ((u : F.valuationSubringˣ) : F.valuationSubring) - 1
  have ha0 : a0 ∈ F.maximalIdeal ^ n := by
    dsimp [a0]
    exact (higherPrincipalUnitGroup.mem_iff F n (u : F.valuationSubringˣ)).1 u.2
  let a : ((F.maximalIdeal ^ n : Ideal F.valuationSubring) : Type u) := ⟨a0, ha0⟩
  refine ⟨_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk F.toDVF n a, ?_⟩
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk,
    higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply]
  congr 1
  dsimp [a]
  apply Subtype.ext
  rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val]
  apply Units.ext
  rw [higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val]
  dsimp [a0]
  ring

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn)`.
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_surjective
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn) := by
  intro y
  rcases higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_surjective
      F n hn (Additive.toMul y) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change Additive.ofMul
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn x) = y
  rw [hx]
  rfl

/--
The specified map is injective: `Function.Injective
(higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn)`.
-/
theorem principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_injective
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn) := by
  intro x y hxy
  have hzero :
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn
        (x - y) = 0 := by
    rw [map_sub, hxy]
    exact sub_self
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd
        F n hn y)
  have hmul :
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (x - y) = 1 := by
    change Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
          (x - y)) =
      Additive.ofMul (1 : higherPrincipalUnitGroup.principalUnitSuccQuot F n) at hzero
    exact Additive.ofMul.injective hzero
  have hxmy : x - y = 0 :=
    (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_eq_one_iff
      F n hn (x - y)).1 hmul
  exact sub_eq_zero.mp hxmy

/-- The additive isomorphism `m^n/m^(n+1) ≃ U^n/U^(n+1)` induced by
`a ↦ 1+a`. -/
noncomputable def maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot
    (n : ℕ) (hn : 1 ≤ n) :
    _root_.ValuationTheory.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot F.toDVF n ≃+
      Additive (higherPrincipalUnitGroup.principalUnitSuccQuot F n) :=
  AddEquiv.ofBijective
    (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn)
    ⟨higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_injective
        F n hn,
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_surjective
        F n hn⟩

/--
The defining evaluation formula for `maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot` is
`higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot F n hn x =
higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn x`.
-/
@[simp] theorem maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply
    (n : ℕ) (hn : 1 ≤ n) (x : _root_.ValuationTheory.DiscreteValuationField.DVF.MaximalIdealPowSuccQuot F.toDVF n) :
    higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot
        F n hn x =
      higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd F n hn x :=
  rfl

/-- The unit-quotient coordinate theorem for a complete DVF with a specified
uniformizer: `U^n/U^(n+1)` is additively the residue field. -/
noncomputable def principalUnitSuccQuotAddEquivResidueOfUniformizer
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) :
    Additive (higherPrincipalUnitGroup.principalUnitSuccQuot F n) ≃+ F.residueField :=
  (higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot
      F n hn).symm.trans
    (residueAddEquivMaximalIdealPowSuccQuotOfUniformizer F.toDVF hpi n).symm

/-- Cardinality form of the associated-graded identification
`U^n/U^(n+1) ≃ k` for `n ≥ 1`. -/
theorem card_principalUnitSuccQuot_eq_residue_of_uniformizer
    [Finite F.residueField]
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (higherPrincipalUnitGroup.principalUnitSuccQuot F n) =
      Nat.card F.residueField := by
  calc
    Nat.card (higherPrincipalUnitGroup.principalUnitSuccQuot F n) =
        Nat.card (Additive
          (higherPrincipalUnitGroup.principalUnitSuccQuot F n)) :=
      Nat.card_congr
        (Additive.ofMul :
          higherPrincipalUnitGroup.principalUnitSuccQuot F n ≃
            Additive (higherPrincipalUnitGroup.principalUnitSuccQuot F n))
    _ = Nat.card F.residueField :=
      Nat.card_congr
        (higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer
          F hpi n hn).toEquiv

/-- Cardinality of the finite principal-unit range `U^1/U^n`, obtained by
iterating the adjacent quotients `U^i/U^(i+1) ≃ k`. -/
theorem card_principalUnitSubquotient_one_eq_residue_pow_of_uniformizer
    [Finite F.residueField]
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (higherPrincipalUnitGroup F 1 ⧸
        (higherPrincipalUnitGroup F n).subgroupOf
          (higherPrincipalUnitGroup F 1)) =
      Nat.card F.residueField ^ (n - 1) := by
  let U := higherPrincipalUnitGroup.toPrincipalUnitFiltration F
  let hfinite (i j : ℕ) : Finite (U.principalUnitSubquotient i j) := by
    exact
      higherPrincipalUnitGroup.finite_principalUnitSubquotient_of_finite_residue
        F i j
  have hN : ∀ i : ℕ, (U.principalUnitSubgroup i).Normal := by
    intro i
    change (higherPrincipalUnitGroup F i).Normal
    infer_instance
  have hn_eq : 1 + (n - 1) = n :=
    by
      simpa [Nat.succ_eq_add_one, Nat.add_comm] using
        (Nat.succ_pred_eq_of_pos hn)
  calc
    Nat.card (U.principalUnitSubquotient 1 n) =
        Nat.card (U.principalUnitSubquotient 1 (1 + (n - 1))) := by
          rw [hn_eq]
    _ =
        ∏ i ∈ Finset.range (n - 1),
          Nat.card (U.principalUnitGradedPiece (1 + i)) := by
          rw [U.card_principalUnitSubquotient_eq_prod_gradedPiece hN 1 (n - 1)]
    _ =
        ∏ _i ∈ Finset.range (n - 1), Nat.card F.residueField := by
          apply Finset.prod_congr rfl
          intro i _hi
          have hpos : 1 ≤ 1 + i := by omega
          calc
            Nat.card (U.principalUnitGradedPiece (1 + i)) =
                Nat.card
                  (higherPrincipalUnitGroup.principalUnitSuccQuot F (1 + i)) :=
              Nat.card_congr
                (higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece
                  F (1 + i)).symm.toEquiv
            _ = Nat.card F.residueField :=
              higherPrincipalUnitGroup.card_principalUnitSuccQuot_eq_residue_of_uniformizer
                F hpi (1 + i) hpos
    _ = Nat.card F.residueField ^ (n - 1) := by
          simp

/-- Under the inverse of `U^n/U^(n+1) ≃ k`, the residue of `r` is represented
by the principal unit `1 + r * pi^n`. -/
@[simp] theorem principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (r : F.valuationSubring) :
    (higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer
        F hpi n hn).symm (F.residueMap r) =
      Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
          (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r)) := by
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer]
  rw [AddEquiv.symm_trans_apply]
  simp only [AddEquiv.symm_symm]
  rw [residueAddEquivMaximalIdealPowSuccQuotOfUniformizer_residue]
  rw [higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply]
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply]
  change Additive.ofMul
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot F n hn
        (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotMk F.toDVF n
          (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r))) =
    Additive.ofMul
      (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
        (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r))
  rw [higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk]

/-- The equivalence `U^n/U^(n+1) ≃ k` sends the coordinate class
`[1 + r * pi^n]` to the residue of `r`. -/
@[simp] theorem principalUnitSuccQuotAddEquivResidueOfUniformizer_coord
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    (n : ℕ) (hn : 1 ≤ n) (r : F.valuationSubring) :
    higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer
        F hpi n hn
        (Additive.ofMul
          (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
            (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r))) =
      F.residueMap r := by
  let E := higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer
    F hpi n hn
  have hcoord :
      E.symm (F.residueMap r) =
        Additive.ofMul
          (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
            (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r)) := by
    simp [E]
  change E
      (Additive.ofMul
        (higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow F n hn
          (_root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowMulUniformizerPowMap F.toDVF hpi n r))) =
    F.residueMap r
  rw [← hcoord]
  exact E.apply_symm_apply (F.residueMap r)

end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_Support
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.principalQuotientAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RelativeIdeleGroup.Cohomology.ideleClassNorm_mk _root_.RelativeIdeleGroup.Cohomology.ideleClass_smul_mk _root_.RelativeIdeleGroup.Cohomology.relativeIdele_smul_def _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.RelativeIdeleGroup.smul_class_mk _root_.TowerRelativeIdeleGroup.classGroupEquiv_mk _root_.TowerRelativeIdeleGroup.classNorm_mk _root_.TowerRelativeIdeleGroup.norm_principalIdele _root_.TowerRelativeIdeleGroup.towerRelativeIdeleEquiv_principalIdele _root_.bottomAdeleToTower_apply _root_.compositeToBaseNormQuotient_mk _root_.intermediateAdeleInclusion_tmul _root_.intermediateToCompositeNormQuotient_mk _root_.scaledRelativeBasisDiscriminantInteger_coe _root_.scaledRelativeExtensionBasis_apply _root_.scaledRelativeExtensionInteger_coe _root_.topFieldToOneStep_apply _root_.topFieldToTower_apply _root_.towerRelativeAdeleFlatten_tmul _root_.towerRelativeAdeleUnflatten_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite coefficient support for relative ideles

This file supplies the finite-support input for the actual scalar-extension model

`𝔸_K ⊗[K] L`.

Fixing the canonical chosen `K`-basis of `L`, every relative adele has
finitely many base-adele coefficients.  For a relative idele we take
the union of the nonintegral finite places of the coefficients of the
idele and of its inverse.  Outside this finite set both local tensor
components therefore lie in the lattice spanned by that basis over
the local valuation ring.

This produces the finite support from a basis lattice.  Passing from
that lattice to the product of local integer rings additionally requires
integral compatibility of the relative tensor decomposition.
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
/-- Expansion of a relative adele in the chosen extension basis. -/
theorem relativeAdele_eq_sum_tmul_coefficients
    (z : RelativeAdeleRing K L) :
    z =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        relativeAdeleCoefficient
            (K := K) (L := L) z i ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
  symm
  simpa [relativeAdeleCoefficient, relativeAdeleBasis,
    relativeExtensionBasis, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def] using
      (relativeAdeleBasis (K := K) (L := L)).sum_repr z

omit [NumberField L] in
/-- Evaluation at a finite place is coefficientwise in the chosen
basis expansion. -/
theorem relativeAdeleFiniteComponent_eq_sum_tmul_coefficients
    (z : RelativeAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeAdeleFiniteComponent
        (K := K) (L := L) w z =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L) z i).2 w ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
  have h :=
    congrArg
      (relativeAdeleFiniteComponent
        (K := K) (L := L) w)
      (relativeAdele_eq_sum_tmul_coefficients
        (K := K) (L := L) z)
  simpa only [map_sum,
    relativeAdeleFiniteComponent_tmul] using h

omit [NumberField L] in
/-- Evaluation at an infinite place is coefficientwise in the chosen
basis expansion. -/
theorem relativeAdeleInfiniteComponent_eq_sum_tmul_coefficients
    (z : RelativeAdeleRing K L)
    (w : InfinitePlace K) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w z =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L) z i).1 w ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
  have h :=
    congrArg
      (relativeAdeleInfiniteComponent
        (K := K) (L := L) w)
      (relativeAdele_eq_sum_tmul_coefficients
        (K := K) (L := L) z)
  simpa only [map_sum,
    relativeAdeleInfiniteComponent_tmul] using h

omit [NumberField L] in
/-- Outside the exact coefficient support, every coefficient of both
the relative idele and its inverse is integral at the given finite
place. -/
theorem relativeIdele_coefficients_integral_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      (relativeAdeleCoefficient
          (K := K) (L := L)
          (z : RelativeAdeleRing K L) i).2 w ∈
        w.adicCompletionIntegers K) ∧
    (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      (relativeAdeleCoefficient
          (K := K) (L := L)
          ((z⁻¹ : RelativeIdeleGroup K L) :
            RelativeAdeleRing K L) i).2 w ∈
        w.adicCompletionIntegers K) := by
  constructor
  · intro i
    by_contra hi
    apply hw
    exact
      (mem_relativeIdeleCoefficientSupport_iff
        (K := K) (L := L) z w).2
        (Or.inl ⟨i, hi⟩)
  · intro i
    by_contra hi
    apply hw
    exact
      (mem_relativeIdeleCoefficientSupport_iff
        (K := K) (L := L) z w).2
        (Or.inr ⟨i, hi⟩)

omit [NumberField L] in
/-- Basis-lattice integrality in the local tensor algebra: all
coordinates in the fixed extension basis belong to the valuation
ring of `K_w`. -/
def RelativeBasisIntegralAt
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L) : Prop :=
  ∃ c :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        w.adicCompletionIntegers K,
    x =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        ((c i : w.adicCompletionIntegers K) :
            w.adicCompletion K) ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i

omit [NumberField L] in
/-- A local tensor unit is basis-integral when both it and its inverse
belong to the local valuation-ring coefficient lattice. -/
def RelativeBasisIntegralUnitAt
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ) : Prop :=
  RelativeBasisIntegralAt
      (K := K) (L := L) w
      (x : w.adicCompletion K ⊗[K] L) ∧
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      ((x⁻¹ : (w.adicCompletion K ⊗[K] L)ˣ) :
        w.adicCompletion K ⊗[K] L)

omit [NumberField L] in
/-- The finite component of a relative idele is given by the evaluated
base-adele coefficients. -/
theorem relativeIdele_finiteComponent_eq_sum_tmul_coefficients
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    ((RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z :
        (w.adicCompletion K ⊗[K] L)ˣ) :
        w.adicCompletion K ⊗[K] L) =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L)
            (z : RelativeAdeleRing K L) i).2 w ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
  rw [RelativeIdeleGroup.finiteComponent_coe]
  exact
    relativeAdeleFiniteComponent_eq_sum_tmul_coefficients
      (K := K) (L := L)
      (z : RelativeAdeleRing K L) w

omit [NumberField L] in
/-- Outside the coefficient support, the actual finite component lies
in the local lattice spanned by the chosen extension basis. -/
theorem relativeIdele_finiteComponent_basisIntegral_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      ((RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z :
          (w.adicCompletion K ⊗[K] L)ˣ) :
          w.adicCompletion K ⊗[K] L) := by
  let c :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        w.adicCompletionIntegers K :=
    fun i =>
      ⟨(relativeAdeleCoefficient
          (K := K) (L := L)
          (z : RelativeAdeleRing K L) i).2 w,
        (relativeIdele_coefficients_integral_of_notMem
          (K := K) (L := L) z w hw).1 i⟩
  refine ⟨c, ?_⟩
  simpa only [c, Subtype.coe_mk] using
    relativeIdele_finiteComponent_eq_sum_tmul_coefficients
      (K := K) (L := L) z w

omit [NumberField L] in
/-- Outside the same support, the actual finite component of the
inverse lies in the same local basis lattice. -/
theorem relativeIdele_inverse_finiteComponent_basisIntegral_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      ((RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w
          (z⁻¹ : RelativeIdeleGroup K L) :
          (w.adicCompletion K ⊗[K] L)ˣ) :
          w.adicCompletion K ⊗[K] L) := by
  let c :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        w.adicCompletionIntegers K :=
    fun i =>
      ⟨(relativeAdeleCoefficient
          (K := K) (L := L)
          ((z⁻¹ : RelativeIdeleGroup K L) :
            RelativeAdeleRing K L) i).2 w,
        (relativeIdele_coefficients_integral_of_notMem
          (K := K) (L := L) z w hw).2 i⟩
  refine ⟨c, ?_⟩
  simpa only [c, Subtype.coe_mk] using
    relativeIdele_finiteComponent_eq_sum_tmul_coefficients
      (K := K) (L := L)
      (z⁻¹ : RelativeIdeleGroup K L) w

omit [NumberField L] in
/-- Equivalently, the inverse of the actual local unit component lies
in the same basis lattice outside the coefficient support. -/
theorem relativeIdele_finiteComponent_inv_basisIntegral_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      ((((RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z)⁻¹ :
          (w.adicCompletion K ⊗[K] L)ˣ) :
          w.adicCompletion K ⊗[K] L)) := by
  simpa using
    relativeIdele_inverse_finiteComponent_basisIntegral_of_notMem
      (K := K) (L := L) z w hw

omit [NumberField L] in
/-- Thus the actual local unit component is basis-integral outside the
explicit coefficient support. -/
theorem relativeIdele_finiteComponent_basisIntegralUnit_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralUnitAt
      (K := K) (L := L) w
      (RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z) :=
  ⟨relativeIdele_finiteComponent_basisIntegral_of_notMem
      (K := K) (L := L) z w hw,
    relativeIdele_finiteComponent_inv_basisIntegral_of_notMem
      (K := K) (L := L) z w hw⟩
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.scaledRelativeBasisDiscriminantInteger_coe
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

/-- The `𝓞 K`-lattice in `𝓞 L` generated by the scaled basis. -/
noncomputable def scaledRelativeIntegerLattice :
    Submodule (𝓞 K) (𝓞 L) :=
  Submodule.span (𝓞 K)
    (Set.range
      (scaledRelativeExtensionInteger
        (K := K) (L := L)))

/-- The same scaled lattice, viewed inside the field `L`. -/
noncomputable def scaledRelativeFieldLattice :
    Submodule (𝓞 K) L :=
  Submodule.span (𝓞 K)
    (Set.range
      (scaledRelativeExtensionBasis
        (K := K) (L := L)))

/-- Mapping the integral lattice into `L` gives the field-valued
lattice spanned by the scaled basis. -/
theorem scaledRelativeIntegerLattice_map_toField :
    (scaledRelativeIntegerLattice
      (K := K) (L := L)).map
        (ringOfIntegersToFieldLinearMap
          (K := K) (L := L)) =
      scaledRelativeFieldLattice
        (K := K) (L := L) := by
  rw [scaledRelativeIntegerLattice,
    scaledRelativeFieldLattice,
    Submodule.map_span]
  congr 1
  exact
    (Set.range_comp
      (ringOfIntegersToFieldLinearMap (K := K) (L := L))
      (scaledRelativeExtensionInteger (K := K) (L := L))).symm

/-- Every algebraic integer becomes a member of the scaled lattice
after multiplication by some non-zero-divisor of `𝓞 K`.  This is the
direct denominator-clearing statement behind torsion of the lattice
quotient. -/
theorem exists_nonZeroDivisor_smul_mem_scaledRelativeIntegerLattice
    (x : 𝓞 L) :
    ∃ d : nonZeroDivisors (𝓞 K),
      (d : 𝓞 K) • x ∈
        scaledRelativeIntegerLattice
          (K := K) (L := L) := by
  let s : Set L :=
    Set.range
      (scaledRelativeExtensionBasis
        (K := K) (L := L))
  have hx :
      (x : L) ∈ Submodule.span K s := by
    change
      (x : L) ∈
        Submodule.span K
          (Set.range
            (scaledRelativeExtensionBasis
              (K := K) (L := L)))
    rw [(scaledRelativeExtensionBasis
      (K := K) (L := L)).span_eq]
    exact Submodule.mem_top
  obtain ⟨d, hd⟩ :=
    multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors (𝓞 K)) K s (x : L) hx
  refine ⟨d, ?_⟩
  have hdmap :
      d • (x : L) ∈
        (scaledRelativeIntegerLattice
          (K := K) (L := L)).map
            (ringOfIntegersToFieldLinearMap
              (K := K) (L := L)) := by
    rw [scaledRelativeIntegerLattice_map_toField
      (K := K) (L := L)]
    exact hd
  obtain ⟨y, hy, hyx⟩ := hdmap
  have hyx' : y = (d : 𝓞 K) • x := by
    apply ringOfIntegersToFieldLinearMap_injective
      (K := K) (L := L)
    simpa [ringOfIntegersToFieldLinearMap,
      Submonoid.smul_def] using hyx
  rw [← hyx']
  exact hy

/-- The finite quotient measuring the index of the scaled basis
lattice in `𝓞 L`. -/
abbrev ScaledRelativeIntegerLatticeQuotient :=
  (𝓞 L) ⧸
    scaledRelativeIntegerLattice
      (K := K) (L := L)

/-- The lattice quotient is finitely generated over `𝓞 K`. -/
noncomputable instance
    scaledRelativeIntegerLatticeQuotientFinite :
    Module.Finite (𝓞 K)
      (ScaledRelativeIntegerLatticeQuotient
        (K := K) (L := L)) :=
  Module.Finite.quotient (𝓞 K)
    (scaledRelativeIntegerLattice
      (K := K) (L := L))

/-- The lattice quotient is torsion. -/
theorem scaledRelativeIntegerLatticeQuotient_isTorsion :
    Module.IsTorsion (𝓞 K)
      (ScaledRelativeIntegerLatticeQuotient
        (K := K) (L := L)) := by
  intro q
  refine
    Submodule.Quotient.induction_on
      (p := scaledRelativeIntegerLattice
        (K := K) (L := L)) q ?_
  intro x
  obtain ⟨d, hd⟩ :=
    exists_nonZeroDivisor_smul_mem_scaledRelativeIntegerLattice
      (K := K) (L := L) x
  refine ⟨d, ?_⟩
  rw [Submonoid.smul_def,
    ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  exact hd

/-- A chosen nonzero element of the annihilator of the finite lattice
quotient. -/
noncomputable def chosenScaledRelativeIntegerLatticeAnnihilatorData :
    { r : 𝓞 K //
      r ∈
          (⊤ : Submodule (𝓞 K)
            (ScaledRelativeIntegerLatticeQuotient
              (K := K) (L := L))).annihilator ∧
        r ∈ nonZeroDivisors (𝓞 K) } := by
  let h :=
    Submodule.annihilator_top_inter_nonZeroDivisors
      (scaledRelativeIntegerLatticeQuotient_isTorsion
        (K := K) (L := L))
  exact
    ⟨Classical.choose h,
      (Classical.choose_spec h).1,
      (Classical.choose_spec h).2⟩

/-- The chosen annihilator element in `𝓞 K`. -/
noncomputable def scaledRelativeIntegerLatticeAnnihilator :
    𝓞 K :=
  (chosenScaledRelativeIntegerLatticeAnnihilatorData
    (K := K) (L := L) : 𝓞 K)

/-- The selected annihilator element is nonzero. -/
theorem scaledRelativeIntegerLatticeAnnihilator_ne_zero :
    scaledRelativeIntegerLatticeAnnihilator
      (K := K) (L := L) ≠ 0 :=
  nonZeroDivisors.ne_zero
    (chosenScaledRelativeIntegerLatticeAnnihilatorData
      (K := K) (L := L)).2.2
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_LocalTensorDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral comparison for local tensor decompositions

This module identifies integrality and units in a finite-place tensor factor
with the corresponding componentwise conditions in the completions above that
place.
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

section LocalTensorDecompositionIntegralComparison

/-- The discriminant control integer is nonzero. -/
theorem scaledRelativeBasisDiscriminantInteger_ne_zero :
    scaledRelativeBasisDiscriminantInteger
      (K := K) (L := L) ≠ 0 := by
  intro h
  apply Algebra.discr_not_zero_of_basis K
    (scaledRelativeExtensionBasis (K := K) (L := L))
  exact congrArg (fun x : 𝓞 K => (x : K)) h

/-- The principal discriminant ideal of the scaled relative basis. -/
noncomputable def scaledRelativeBasisDiscriminantIdeal :
    Ideal (𝓞 K) :=
  Ideal.span
    ({scaledRelativeBasisDiscriminantInteger
      (K := K) (L := L)} : Set (𝓞 K))

/-- The discriminant control ideal is nontrivial. -/
theorem scaledRelativeBasisDiscriminantIdeal_ne_bot :
    scaledRelativeBasisDiscriminantIdeal
      (K := K) (L := L) ≠ ⊥ := by
  rw [scaledRelativeBasisDiscriminantIdeal,
    ne_eq, Ideal.span_singleton_eq_bot]
  exact scaledRelativeBasisDiscriminantInteger_ne_zero
    (K := K) (L := L)

/-- Finite set of places at which the scaled relative basis has
nonunit discriminant. -/
noncomputable def scaledRelativeBasisDiscriminantBadPlaces :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors
    (scaledRelativeBasisDiscriminantIdeal_ne_bot
      (K := K) (L := L))).toFinset

/-- Membership in the discriminant bad-place set is ideal membership. -/

@[simp]
theorem mem_scaledRelativeBasisDiscriminantBadPlaces_iff
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ scaledRelativeBasisDiscriminantBadPlaces
        (K := K) (L := L) ↔
      w.asIdeal ∣
        scaledRelativeBasisDiscriminantIdeal
          (K := K) (L := L) :=
  Set.Finite.mem_toFinset
    (Ideal.finite_factors
      (scaledRelativeBasisDiscriminantIdeal_ne_bot
        (K := K) (L := L)))

/-- Outside the discriminant bad places, the control integer avoids the prime. -/
theorem scaledRelativeBasisDiscriminantInteger_not_mem_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ scaledRelativeBasisDiscriminantBadPlaces
      (K := K) (L := L)) :
    scaledRelativeBasisDiscriminantInteger
        (K := K) (L := L) ∉ w.asIdeal := by
  intro hmem
  apply hw
  rw [mem_scaledRelativeBasisDiscriminantBadPlaces_iff,
    scaledRelativeBasisDiscriminantIdeal,
    Ideal.dvd_span_singleton]
  exact hmem

/-- Outside the discriminant bad places, its adic absolute value is one. -/
theorem adicAbv_scaledRelativeBasisDiscriminant_eq_one_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ scaledRelativeBasisDiscriminantBadPlaces
      (K := K) (L := L)) :
    NumberField.HeightOneSpectrum.adicAbv K w
        (Algebra.discr K
          (scaledRelativeExtensionBasis (K := K) (L := L))) = 1 := by
  have hnorm :
      ‖FinitePlace.embedding (K := K) w
        (scaledRelativeBasisDiscriminantInteger
          (K := K) (L := L))‖ = 1 :=
    (FinitePlace.norm_eq_one_iff_notMem
      (R := 𝓞 K) K w
      (scaledRelativeBasisDiscriminantInteger
        (K := K) (L := L))).2
      (scaledRelativeBasisDiscriminantInteger_not_mem_of_notMem
        (K := K) (L := L) w hw)
  exact (FinitePlace.norm_embedding w
    (scaledRelativeBasisDiscriminantInteger (K := K) (L := L) : K)).symm.trans hnorm

end LocalTensorDecompositionIntegralComparison
end
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootChart
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual charts for the full upper unipotent group

The complete Gaussian elimination chain supplies an open group chart.
Left translation and the discrete lattice covering then give local
product charts in the arithmetic quotient around every point. Every
time factor is an actual ordered product of positive-root matrices.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def upperRootQuotientParam (n : ℕ) (g : G n)
    (z : UpperRootTransverse n × UpperRootTime n) : X n :=
  Quotient.mk _ (g * upperRootParam n z)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

/-- The maximal ideal of the valuation subring. -/
abbrev maximalIdeal (F : LocalField.{u, v} K) : Ideal F.valuationSubring :=
  F.toCompleteDVF.maximalIdeal

end LocalField
end LocalFieldTheory.DiscreteValuationField
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_EqualCharacteristicLaurent
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

/-- The Teichmuller coefficient-field section `κ -> O_K` used before passing
to the fraction field. -/
abbrev coeffSubringHom [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ)) :
    F.residueField →+* F.valuationSubring :=
  LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP
    (F := F) p hcard

/-- The Teichmuller coefficient-field embedding `κ -> K` used in the
equal-characteristic Laurent-series branch. -/
abbrev coeffHom [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ)) :
    F.residueField →+* K :=
  LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP
    (F := F) p hcard

/-- The field-valued coefficient embedding is the valuation-ring coefficient
section followed by the valuation-subring inclusion. -/
@[simp] theorem coeffHom_apply [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (a : F.residueField) :
    coeffHom (F := F) p hcard a =
      (coeffSubringHom (F := F) p hcard a : K) := by
  rfl

/-- The valuation-ring Teichmuller coefficient section is continuous from the
discrete residue-field topology to any topology on the valuation ring. -/
theorem continuous_coeffSubringHom_of_discrete [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    [UniformSpace F.residueField] [DiscreteUniformity F.residueField]
    [TopologicalSpace F.valuationSubring] :
    Continuous (coeffSubringHom (F := F) p hcard) :=
  continuous_of_discreteTopology

/-- A complete-DVF uniformizer is topologically nilpotent in the valuation
ring for the maximal-ideal adic topology. -/
theorem uniformizer_hasEval_valuationSubring_withIdeal
    {π : F.valuationSubring}
    (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
    PowerSeries.HasEval π := by
  let : WithIdeal F.valuationSubring := { i := F.maximalIdeal }
  change Filter.Tendsto (fun m : ℕ => π ^ m) Filter.atTop
    (nhds (0 : F.valuationSubring))
  refine (F.maximalIdeal.hasBasis_nhds_zero_adic).tendsto_right_iff.2 ?_
  intro n _
  refine Filter.eventually_atTop.2 ⟨n, fun m hm => ?_⟩
  have hπmem : π ∈ F.maximalIdeal :=
    F.uniformizer_mem_maximalIdeal hπ
  have hpow : π ^ m ∈ F.maximalIdeal ^ m :=
    Ideal.pow_mem_pow hπmem m
  exact Ideal.pow_le_pow_right hm hpow

/-- Evaluation of power series into the valuation ring through the
Teichmuller coefficient section, sending `X` to a chosen uniformizer. -/
noncomputable def powerSeriesEvalSubringHom [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    F.residueField⟦X⟧ →+* F.valuationSubring :=
  PowerSeries.eval₂Hom hcoeff hπeval

/--
Establishes the identity `powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval
(PowerSeries.C a) = coeffSubringHom (F := F) p hcard a`.
-/
@[simp] theorem powerSeriesEvalSubringHom_C [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) (a : F.residueField) :
    powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval
        (PowerSeries.C a) =
      coeffSubringHom (F := F) p hcard a := by
  have hfun :
      ⇑(PowerSeries.eval₂Hom hcoeff hπeval) =
        PowerSeries.eval₂ (coeffSubringHom (F := F) p hcard) π :=
    PowerSeries.coe_eval₂Hom hcoeff hπeval
  have happ := congrFun hfun (PowerSeries.C a)
  simpa [powerSeriesEvalSubringHom, PowerSeries.eval₂_C] using happ

/--
Establishes the identity `powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval PowerSeries.X
= π`.
-/
@[simp] theorem powerSeriesEvalSubringHom_X [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval
        PowerSeries.X =
      π := by
  have hfun :
      ⇑(PowerSeries.eval₂Hom hcoeff hπeval) =
        PowerSeries.eval₂ (coeffSubringHom (F := F) p hcard) π :=
    PowerSeries.coe_eval₂Hom hcoeff hπeval
  have happ := congrFun hfun PowerSeries.X
  simpa [powerSeriesEvalSubringHom, PowerSeries.eval₂_X] using happ

/-- The valuation-ring evaluation composed with the inclusion `O_K -> K`. -/
noncomputable def powerSeriesEvalHom [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    F.residueField⟦X⟧ →+* K :=
  F.valuation.valuationSubring.subtype.comp
    (powerSeriesEvalSubringHom (F := F) p hcard π hcoeff hπeval)

/--
Establishes the identity `powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval (PowerSeries.C a) =
coeffHom (F := F) p hcard a`.
-/
@[simp] theorem powerSeriesEvalHom_C [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) (a : F.residueField) :
    powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval
        (PowerSeries.C a) =
      coeffHom (F := F) p hcard a := by
  have hsub :=
    powerSeriesEvalSubringHom_C
      (F := F) p hcard π hcoeff hπeval a
  exact congrArg F.valuation.valuationSubring.subtype hsub

/--
Establishes the identity `powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval PowerSeries.X = (π :
K)`.
-/
@[simp] theorem powerSeriesEvalHom_X [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval
        PowerSeries.X =
      (π : K) := by
  have hsub :=
    powerSeriesEvalSubringHom_X
      (F := F) p hcard π hcoeff hπeval
  exact congrArg F.valuation.valuationSubring.subtype hsub

/--
Proves that the specified element is a unit: `IsUnit (powerSeriesEvalHom (F := F) p hcard π hcoeff
hπeval PowerSeries.X)`.
-/
theorem powerSeriesEvalHom_X_isUnit [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K))
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    IsUnit
      (powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval
        PowerSeries.X) := by
  simpa using
    (isUnit_iff_ne_zero.mpr hπ.ne_zero : IsUnit (π : K))

/-- The Laurent-series evaluation map `κ((X)) -> K` attached to the
Teichmuller coefficient field and the chosen uniformizer. -/
noncomputable def laurentSeriesEvalHom [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K))
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    F.residueField⸨X⸩ →+* K :=
  IsLocalization.Away.lift
    (S := F.residueField⸨X⸩)
    (P := K)
    (x := (PowerSeries.X : F.residueField⟦X⟧))
    (g := powerSeriesEvalHom (F := F) p hcard π hcoeff hπeval)
    (powerSeriesEvalHom_X_isUnit
      (F := F) p hcard π hπ hcoeff hπeval)

/-- The algebra structure on `K` induced by the Laurent-series evaluation map.
This is the base algebra for the remaining finite-dimensionality step. -/
@[reducible] noncomputable def laurentSeriesAlgebra [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p]
    {n : ℕ+} (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (π : F.valuationSubring)
    (hπ : F.valuation.IsUniformizer (π : K))
    [UniformSpace F.residueField] [IsUniformAddGroup F.residueField]
    [IsTopologicalSemiring F.residueField]
    [UniformSpace F.valuationSubring] [IsUniformAddGroup F.valuationSubring]
    [T2Space F.valuationSubring] [CompleteSpace F.valuationSubring]
    [IsTopologicalRing F.valuationSubring]
    [IsLinearTopology F.valuationSubring F.valuationSubring]
    (hcoeff : Continuous (coeffSubringHom (F := F) p hcard))
    (hπeval : PowerSeries.HasEval π) :
    Algebra F.residueField⸨X⸩ K :=
  RingHom.toAlgebra
    (laurentSeriesEvalHom (F := F) p hcard π hπ hcoeff hπeval)

end EqualCharacteristicLaurent
end CompleteDVF

end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_InverseLimitCore
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The canonical p-adic action on first principal units

This file constructs the common source used in both cases of LubinTate,
The field-unit structure theorem.  A first principal unit is recovered from its
classes in the level quotients `U^1 / U^(n+1)`.  For a local field these
quotients are finite and have exponent dividing `p^(f*n)`, where the residue
field has cardinality `p^f`.
Reduction of a p-adic integer modulo these powers therefore acts on every
finite coordinate, and compatibility of reduction transports the action to
`U^1`.
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

/-- A fixed uniformizer used only to invoke the direct quotient form of
the adic inverse-limit equivalence.  The resulting p-adic action is characterized below by its
ordinary integral powers. -/
noncomputable def chosenPrincipalUnitPadicUniformizer
    (F : CompleteDVF.{u, v} K) : F.valuationSubring :=
  Classical.choose F.exists_uniformizer

/-- The chosen principal-unit parameter has valuation one and is a uniformizer. -/
theorem chosenPrincipalUnitPadicUniformizer_isUniformizer
    (F : CompleteDVF.{u, v} K) :
    F.valuation.IsUniformizer (chosenPrincipalUnitPadicUniformizer F : K) :=
  Classical.choose_spec F.exists_uniformizer

/-- The chosen valuation-ring uniformizer is irreducible. -/
theorem chosenPrincipalUnitPadicUniformizer_irreducible
    (F : CompleteDVF.{u, v} K) :
    Irreducible (chosenPrincipalUnitPadicUniformizer F) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  exact F.maximalIdeal_eq_span_uniformizer
    (chosenPrincipalUnitPadicUniformizer_isUniformizer F)

/-- For the chosen uniformizer, the higher-unit subgroup `1 + pi^n O` is the
intrinsic `n`-th higher principal-unit group. -/
theorem higherUnitSubgroup_chosenPrincipalUnitPadicUniformizer
    (F : CompleteDVF.{u, v} K) (n : ℕ) :
    higherUnitSubgroup (chosenPrincipalUnitPadicUniformizer F) n =
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) n := by
  ext x
  rw [mem_higherUnitSubgroup_iff_sub_one_mem_powerIdeal,
    higherPrincipalUnitGroup.mem_iff]
  have hideal :
      uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) n =
        F.maximalIdeal ^ n := by
    calc
      uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) n =
        (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1) ^ n :=
        (dvrPowerIdeal_one_pow _ n).symm
      _ = F.maximalIdeal ^ n := by
        rw [uniformizerPowerIdeal, pow_one,
          ← F.maximalIdeal_eq_span_uniformizer
            (chosenPrincipalUnitPadicUniformizer_isUniformizer F)]
  rw [hideal]

/-- Transition on the intrinsic quotients `O^*/U^(n+1)`. -/
def Internal.higherUnitQuotientTransition
    (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n) :
    F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1) →*
      F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (m + 1) :=
  (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).quotient_principalUnitSubgroup_mapOfLe
    (Nat.succ_le_succ hmn)

/-- The intrinsic full unit inverse limit `lim O^*/U^(n+1)`. -/
abbrev Internal.higherUnitInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) : Type u :=
  compatibleGroupFamilies
    (fun n : ℕ =>
      F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1))
    (fun {_ _} hmn => Internal.higherUnitQuotientTransition F hmn)

open Internal

/-- Changing from the uniformizer presentation of a level quotient to the
intrinsic principal-unit presentation. -/
noncomputable def Internal.uniformizerHigherUnitQuotientEquiv
    (F : CompleteDVF.{u, v} K) (n : ℕ) :
    F.valuationSubringˣ ⧸
        higherUnitSubgroup (chosenPrincipalUnitPadicUniformizer F) (n + 1) ≃*
      F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1) :=
  QuotientGroup.quotientMulEquivOfEq
    (higherUnitSubgroup_chosenPrincipalUnitPadicUniformizer F (n + 1))

/--
Establishes the identity `uniformizerHigherUnitQuotientEquiv F n (QuotientGroup.mk x) =
QuotientGroup.mk x`.
-/
@[simp] theorem Internal.uniformizerHigherUnitQuotientEquiv_mk
    (F : CompleteDVF.{u, v} K) (n : ℕ) (x : F.valuationSubringˣ) :
    uniformizerHigherUnitQuotientEquiv F n (QuotientGroup.mk x) =
      QuotientGroup.mk x := by
  exact QuotientGroup.quotientMulEquivOfEq_mk _ x

/-- The uniformizer and intrinsic presentations give the same full inverse
limit. -/
noncomputable def Internal.uniformizerHigherUnitInverseLimitEquiv
    (F : CompleteDVF.{u, v} K) :
    dvrHigherUnitQuotientInverseLimit
        (chosenPrincipalUnitPadicUniformizer F) ≃*
      Internal.higherUnitInverseLimitCarrier F :=
  (dvrHigherUnitQuotientInverseLimitRepresentation
      (chosenPrincipalUnitPadicUniformizer F)).trans
    (compatibleGroupFamiliesMulEquiv
      (fun n : ℕ =>
        F.valuationSubringˣ ⧸
          higherUnitSubgroup (chosenPrincipalUnitPadicUniformizer F) (n + 1))
      (fun n : ℕ =>
        F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1))
      (fun {_ _} hmn =>
        dvrHigherUnitQuotientTransition
          (chosenPrincipalUnitPadicUniformizer F) hmn)
      (fun {_ _} hmn => higherUnitQuotientTransition F hmn)
      (uniformizerHigherUnitQuotientEquiv F)
      (by
        intro m n hmn q
        refine QuotientGroup.induction_on q ?_
        intro x
        rw [uniformizerHigherUnitQuotientEquiv_mk]
        change QuotientGroup.mk x = QuotientGroup.mk x
        rfl))

/-- The direct quotient isomorphism of the adic inverse-limit equivalence, rewritten using the
intrinsic higher principal-unit filtration. -/
noncomputable def Internal.unitsEquivHigherUnitQuotientInverseLimit
    (F : CompleteDVF.{u, v} K) :
    F.valuationSubringˣ ≃* Internal.higherUnitInverseLimitCarrier F := by
  let pi := chosenPrincipalUnitPadicUniformizer F
  have hpi : Irreducible pi := chosenPrincipalUnitPadicUniformizer_irreducible F
  letI : IsAdicComplete (uniformizerPowerIdeal pi 1) F.valuationSubring := by
    have hmax : uniformizerPowerIdeal pi 1 = F.maximalIdeal := by
      rw [uniformizerPowerIdeal, pow_one,
        ← F.maximalIdeal_eq_span_uniformizer
          (chosenPrincipalUnitPadicUniformizer_isUniformizer F)]
    rw [hmax]
    exact ValuationTheory.DiscreteValuationField.Valuation.isAdicComplete F.valuation
  exact
    (dvrUnitsEquivHigherUnitQuotientInverseLimit hpi).trans
      (uniformizerHigherUnitInverseLimitEquiv F)

/--
The defining evaluation formula for `Internal.unitsEquivHigherUnitQuotientInverseLimit` is
`(unitsEquivHigherUnitQuotientInverseLimit F x).1 n = QuotientGroup.mk x`.
-/
theorem Internal.unitsEquivHigherUnitQuotientInverseLimit_apply
    (F : CompleteDVF.{u, v} K) (x : F.valuationSubringˣ) (n : ℕ) :
    (unitsEquivHigherUnitQuotientInverseLimit F x).1 n =
      QuotientGroup.mk x := by
  let pi := chosenPrincipalUnitPadicUniformizer F
  have hpi : Irreducible pi := chosenPrincipalUnitPadicUniformizer_irreducible F
  let : IsAdicComplete (uniformizerPowerIdeal pi 1) F.valuationSubring := by
    have hmax : uniformizerPowerIdeal pi 1 = F.maximalIdeal := by
      rw [uniformizerPowerIdeal, pow_one,
        ← F.maximalIdeal_eq_span_uniformizer
          (chosenPrincipalUnitPadicUniformizer_isUniformizer F)]
    rw [hmax]
    exact ValuationTheory.DiscreteValuationField.Valuation.isAdicComplete F.valuation
  change
    uniformizerHigherUnitQuotientEquiv F n
        (dvrHigherUnitQuotientInverseLimit_eval pi n
          (dvrUnitsEquivHigherUnitQuotientInverseLimit hpi x)) =
      QuotientGroup.mk x
  rw [dvrUnitsEquivHigherUnitQuotientInverseLimit_apply,
    uniformizerHigherUnitQuotientEquiv_mk]

/-- The change from the uniformizer presentation of the full unit inverse
limit to the intrinsic presentation is a homeomorphism when all quotient
coordinates are discrete. -/
noncomputable def Internal.uniformizerHigherUnitInverseLimitHomeomorphIntrinsic
    (F : CompleteDVF.{u, v} K) :
    letI : (n : ℕ) → TopologicalSpace
        (F.valuationSubringˣ ⧸
          higherUnitSubgroup (chosenPrincipalUnitPadicUniformizer F) (n + 1)) :=
      fun _ => ⊥
    letI : (n : ℕ) → TopologicalSpace
        (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
      fun _ => ⊥
    dvrHigherUnitQuotientInverseLimit
        (chosenPrincipalUnitPadicUniformizer F) ≃ₜ
      Internal.higherUnitInverseLimitCarrier F := by
  letI : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸
        higherUnitSubgroup (chosenPrincipalUnitPadicUniformizer F) (n + 1)) :=
    fun _ => ⊥
  letI : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
    fun _ => ⊥
  letI : (n : ℕ) → DiscreteTopology
      (F.valuationSubringˣ ⧸
        higherUnitSubgroup (chosenPrincipalUnitPadicUniformizer F) (n + 1)) :=
    fun _ => ⟨rfl⟩
  letI : (n : ℕ) → DiscreteTopology
      (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
    fun _ => ⟨rfl⟩
  let e := uniformizerHigherUnitInverseLimitEquiv F
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change Continuous fun x => e x
    exact Continuous.subtype_mk
      (continuous_pi fun n => by
        change Continuous fun x :
            dvrHigherUnitQuotientInverseLimit
              (chosenPrincipalUnitPadicUniformizer F) =>
          uniformizerHigherUnitQuotientEquiv F n
            (dvrHigherUnitQuotientInverseLimit_eval
              (chosenPrincipalUnitPadicUniformizer F) n x)
        have heval : Continuous fun x :
            dvrHigherUnitQuotientInverseLimit
              (chosenPrincipalUnitPadicUniformizer F) =>
            dvrHigherUnitQuotientInverseLimit_eval
              (chosenPrincipalUnitPadicUniformizer F) n x :=
          (DiscreteHigherUnitQuotient.homeomorph
            (chosenPrincipalUnitPadicUniformizer F) (n + 1)).continuous.comp
            (dvrHigherUnitQuotientInverseLimit_discreteEval_continuous
              (chosenPrincipalUnitPadicUniformizer F) n)
        exact continuous_of_discreteTopology.comp heval)
      (fun x : dvrHigherUnitQuotientInverseLimit
          (chosenPrincipalUnitPadicUniformizer F) => by
        intro i j hij
        show higherUnitQuotientTransition F hij
            (uniformizerHigherUnitQuotientEquiv F j
              (dvrHigherUnitQuotientInverseLimit_eval
                (chosenPrincipalUnitPadicUniformizer F) j x)) =
          uniformizerHigherUnitQuotientEquiv F i
            (dvrHigherUnitQuotientInverseLimit_eval
              (chosenPrincipalUnitPadicUniformizer F) i x)
        exact (e x).2 hij)
  · change Continuous fun x => e.symm x
    apply (dvrHigherUnitQuotientInverseLimit_continuous_iff
      (chosenPrincipalUnitPadicUniformizer F) (fun x => e.symm x)).2
    intro n
    change Continuous fun x : Internal.higherUnitInverseLimitCarrier F =>
      DiscreteHigherUnitQuotient.of
        (chosenPrincipalUnitPadicUniformizer F) (n + 1)
        ((uniformizerHigherUnitQuotientEquiv F n).symm (x.1 n))
    exact
      (DiscreteHigherUnitQuotient.homeomorph
        (chosenPrincipalUnitPadicUniformizer F) (n + 1)).symm.continuous.comp
        (continuous_of_discreteTopology.comp
          ((continuous_apply n).comp continuous_subtype_val))

/-- Topological full-unit form of the adic inverse-limit equivalence, rewritten intrinsically. -/
noncomputable def Internal.unitsHomeomorphHigherUnitQuotientInverseLimit
    (F : CompleteDVF.{u, v} K) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    letI : (n : ℕ) → TopologicalSpace
        (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
      fun _ => ⊥
    F.valuationSubringˣ ≃ₜ Internal.higherUnitInverseLimitCarrier F := by
  let pi := chosenPrincipalUnitPadicUniformizer F
  letI : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal pi 1).adicTopology
  letI : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
    fun _ => ⊥
  letI : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸ higherUnitSubgroup pi (n + 1)) :=
    fun _ => ⊥
  have hpi : Irreducible pi := chosenPrincipalUnitPadicUniformizer_irreducible F
  letI : IsAdicComplete (uniformizerPowerIdeal pi 1) F.valuationSubring := by
    have hmax : uniformizerPowerIdeal pi 1 = F.maximalIdeal := by
      rw [uniformizerPowerIdeal, pow_one,
        ← F.maximalIdeal_eq_span_uniformizer
          (chosenPrincipalUnitPadicUniformizer_isUniformizer F)]
    rw [hmax]
    exact ValuationTheory.DiscreteValuationField.Valuation.isAdicComplete F.valuation
  exact
    (WithTopology.homeomorph
      (α := F.valuationSubringˣ)
      (topology := adicUnitsTopology (uniformizerPowerIdeal pi 1))).symm.trans
      ((unitsEquivHigherUnitQuotientInverseLimitHomeomorph hpi).trans
        (Internal.uniformizerHigherUnitInverseLimitHomeomorphIntrinsic F))

/--
The unit-to-inverse-limit homeomorphism sends a unit to its canonical class at every higher-unit
quotient level.
-/
theorem Internal.unitsHomeomorphHigherUnitQuotientInverseLimit_apply
    (F : CompleteDVF.{u, v} K) (x : F.valuationSubringˣ) (n : ℕ) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    letI : (n : ℕ) → TopologicalSpace
        (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
      fun _ => ⊥
    (Internal.unitsHomeomorphHigherUnitQuotientInverseLimit F x).1 n =
      QuotientGroup.mk x := by
  let pi := chosenPrincipalUnitPadicUniformizer F
  let : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal pi 1).adicTopology
  let : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) :=
    fun _ => ⊥
  let : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸ higherUnitSubgroup pi (n + 1)) :=
    fun _ => ⊥
  have hpi : Irreducible pi := chosenPrincipalUnitPadicUniformizer_irreducible F
  let : IsAdicComplete (uniformizerPowerIdeal pi 1) F.valuationSubring := by
    have hmax : uniformizerPowerIdeal pi 1 = F.maximalIdeal := by
      rw [uniformizerPowerIdeal, pow_one,
        ← F.maximalIdeal_eq_span_uniformizer
          (chosenPrincipalUnitPadicUniformizer_isUniformizer F)]
    rw [hmax]
    exact ValuationTheory.DiscreteValuationField.Valuation.isAdicComplete F.valuation
  change uniformizerHigherUnitQuotientEquiv F n
      (dvrHigherUnitQuotientInverseLimit_eval pi n
        (unitsEquivHigherUnitQuotientInverseLimitHomeomorph
          hpi
          (WithTopology.toTopology (adicUnitsTopology (uniformizerPowerIdeal pi 1)) x))) =
    QuotientGroup.mk x
  change uniformizerHigherUnitQuotientEquiv F n (QuotientGroup.mk x) =
    QuotientGroup.mk x
  exact uniformizerHigherUnitQuotientEquiv_mk F n x

/-! ## Restriction of the adic inverse-limit equivalence to first principal units -/

/-- The raw carrier of the `n`-th coordinate `U^1/U^(n+1)`. -/
abbrev Internal.principalUnitQuotientCarrier
    (F : CompleteDVF.{u, v} K) (n : ℕ) : Type u :=
  (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotient
    1 (n + 1)

/-- Transition `U^1/U^(n+1) -> U^1/U^(m+1)` for `m <= n`. -/
def Internal.principalUnitQuotientCarrierTransition
    (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n) :
    Internal.principalUnitQuotientCarrier F n →*
      Internal.principalUnitQuotientCarrier F m := by
  let U := higherPrincipalUnitGroup.toPrincipalUnitFiltration F
  change U.principalUnitSubquotient 1 (n + 1) →*
    U.principalUnitSubquotient 1 (m + 1)
  refine U.principalUnitSubquotientLift 1 (n + 1)
    (U.principalUnitSubquotientMk 1 (m + 1)) ?_
  intro x hx
  rw [MonoidHom.mem_ker,
    U.principalUnitSubquotient_mk_eq_one_iff]
  change (x : F.valuationSubringˣ) ∈
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
      (m + 1)
  exact higherPrincipalUnitGroup.antitone F (Nat.succ_le_succ hmn) hx

/--
Establishes the identity `principalUnitQuotientCarrierTransition F hmn
((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk 1 (n + 1) x) =
(higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk 1 (m + 1) x`.
-/
@[simp] theorem Internal.principalUnitQuotientCarrierTransition_mk
    (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n)
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    principalUnitQuotientCarrierTransition F hmn
        ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
          1 (n + 1) x) =
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
        1 (m + 1) x :=
  rfl

/-- The projective limit `lim_n U^1/U^(n+1)`. -/
abbrev Internal.principalUnitInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) : Type u :=
  compatibleGroupFamilies
    (Internal.principalUnitQuotientCarrier F)
    (fun {_ _} hmn => principalUnitQuotientCarrierTransition F hmn)

/-- Evaluation of a principal-unit compatible family at level `n`. -/
def Internal.principalUnitInverseLimitCarrierEval
    (F : CompleteDVF.{u, v} K) (n : ℕ) :
    Internal.principalUnitInverseLimitCarrier F →*
      Internal.principalUnitQuotientCarrier F n :=
  compatibleGroupFamiliesEval
    (Internal.principalUnitQuotientCarrier F)
    (fun {_ _} hmn => principalUnitQuotientCarrierTransition F hmn) n

/--
The defining evaluation formula for `Internal.principalUnitInverseLimitCarrierEval` is
`principalUnitInverseLimitCarrierEval F n x = x.1 n`.
-/
@[simp]
theorem Internal.principalUnitInverseLimitCarrierEval_apply
    (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : Internal.principalUnitInverseLimitCarrier F) :
    principalUnitInverseLimitCarrierEval F n x = x.1 n :=
  rfl

/-- Principal-unit inverse-limit families are determined by their
coordinates. -/
@[ext]
theorem Internal.principalUnitInverseLimitCarrier_ext
    (F : CompleteDVF.{u, v} K)
    {x y : Internal.principalUnitInverseLimitCarrier F}
    (h : ∀ n, principalUnitInverseLimitCarrierEval F n x =
      principalUnitInverseLimitCarrierEval F n y) : x = y :=
  compatibleGroupFamilies_ext
    (Internal.principalUnitQuotientCarrier F)
    (fun {_ _} hij => principalUnitQuotientCarrierTransition F hij) h
end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_TopologyModelTypes
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Type-level topology models for principal units

Adic principal units, discrete finite quotients, and the prodiscrete inverse limit are
represented by distinct wrapper types so that their topologies cannot be confused by instance
selection.
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

/-! ## Topology is part of the type

The algebraic quotient and inverse-limit types above deliberately carry no
preferred topology.  The following models distinguish the topologies used in
the p-adic action at the type level.  In particular, no theorem below can
silently reinterpret the same quotient as both a quotient-topological and a
discrete space.
-/

/-- The topology on additive first principal units induced by the maximal-
ideal adic topology on the valuation ring. -/
@[implicit_reducible]
noncomputable def principalUnitAdicTopology
    (F : CompleteDVF.{u, v} K) :
    TopologicalSpace
      (Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)) := by
  letI : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
  exact inferInstance

/-- First principal units with their canonical adic topology fixed in the
type. -/
structure AdicPrincipalUnits (F : CompleteDVF.{u, v} K) where
  /-- The underlying additive principal unit. -/
  val : Additive
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)

namespace AdicPrincipalUnits

/-- The carrier equivalence of the adic model. -/
def equiv (F : CompleteDVF.{u, v} K) :
    AdicPrincipalUnits F ≃
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) where
  toFun := AdicPrincipalUnits.val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/--
Equips the target with its canonical `TopologicalSpace` structure, namely `TopologicalSpace
(AdicPrincipalUnits F)`.
-/
noncomputable instance instTopologicalSpace (F : CompleteDVF.{u, v} K) :
    TopologicalSpace (AdicPrincipalUnits F) :=
  (principalUnitAdicTopology F).induced AdicPrincipalUnits.val

/-- Forget the wrapper while retaining the topology recorded in its type. -/
noncomputable def homeomorph (F : CompleteDVF.{u, v} K) :
    AdicPrincipalUnits F ≃ₜ
      WithTopology
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1))
        (principalUnitAdicTopology F) where
  toEquiv := (equiv F).trans
    (WithTopology.equiv _ (principalUnitAdicTopology F)).symm
  continuous_toFun := by
    let : TopologicalSpace
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)) :=
      principalUnitAdicTopology F
    change Continuous fun x : AdicPrincipalUnits F =>
      WithTopology.toTopology (principalUnitAdicTopology F) x.val
    exact
      (WithTopology.continuous_toTopology (principalUnitAdicTopology F)).comp
        continuous_induced_dom
  continuous_invFun := by
    let : TopologicalSpace
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)) :=
      principalUnitAdicTopology F
    change Continuous fun x : WithTopology
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1))
        (principalUnitAdicTopology F) =>
      (⟨x.ofTopology⟩ : AdicPrincipalUnits F)
    exact
      continuous_induced_rng.2
        (WithTopology.continuous_ofTopology (principalUnitAdicTopology F))

/--
Equips the target with its canonical `AddCommGroup` structure, namely `AddCommGroup
(AdicPrincipalUnits F)`.
-/
instance instAddCommGroup (F : CompleteDVF.{u, v} K) : AddCommGroup (AdicPrincipalUnits F) :=
  (equiv F).addCommGroup

/-- Put a first principal unit into the canonical adic model. -/
def of (F : CompleteDVF.{u, v} K)
    (x : Additive
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)) :
    AdicPrincipalUnits F :=
  ⟨x⟩

/-- Establishes the identity `(of F x).val = x`. -/
@[simp] theorem val_of (F : CompleteDVF.{u, v} K)
    (x : Additive
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)) :
    (of F x).val = x := rfl

/-- Establishes the identity `of F x.val = x`. -/
@[simp] theorem of_val (F : CompleteDVF.{u, v} K)
    (x : AdicPrincipalUnits F) : of F x.val = x := by
  cases x
  rfl

/-- The algebraic equivalence underlying the adic model. -/
def addEquiv (F : CompleteDVF.{u, v} K) :
    AdicPrincipalUnits F ≃+
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :=
  (equiv F).addEquiv

end AdicPrincipalUnits

/-- The `n`-th principal-unit quotient with its mathematically intended
discrete topology fixed in the type.  Its carrier is finite when `F` is a
`LocalField`, but not for an arbitrary `CompleteDVF`. -/
structure DiscretePrincipalUnitQuotient
    (F : CompleteDVF.{u, v} K) (n : ℕ) where
  /-- The underlying quotient class. -/
  val : Additive (Internal.principalUnitQuotientCarrier F n)

namespace DiscretePrincipalUnitQuotient

/-- Establishes the identity `x = y`. -/
@[ext]
theorem ext {F : CompleteDVF.{u, v} K} {n : ℕ}
    {x y : DiscretePrincipalUnitQuotient F n} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- The carrier equivalence of a discrete coordinate. -/
def equiv (F : CompleteDVF.{u, v} K) (n : ℕ) :
    DiscretePrincipalUnitQuotient F n ≃
      Additive (Internal.principalUnitQuotientCarrier F n) where
  toFun := DiscretePrincipalUnitQuotient.val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/--
Equips the target with its canonical `AddCommGroup` structure, namely `AddCommGroup
(DiscretePrincipalUnitQuotient F n)`.
-/
instance instAddCommGroup (F : CompleteDVF.{u, v} K) (n : ℕ) :
    AddCommGroup (DiscretePrincipalUnitQuotient F n) :=
  (equiv F n).addCommGroup

/-- Algebraic equivalence forgetting the discrete coordinate wrapper. -/
def addEquiv (F : CompleteDVF.{u, v} K) (n : ℕ) :
    DiscretePrincipalUnitQuotient F n ≃+
      Additive (Internal.principalUnitQuotientCarrier F n) :=
  (equiv F n).addEquiv

/-- The defining evaluation formula for `addEquiv` is `addEquiv F n x = x.val`. -/
@[simp] theorem addEquiv_apply (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : DiscretePrincipalUnitQuotient F n) :
    addEquiv F n x = x.val :=
  rfl

/-- Put a quotient class into its discrete model. -/
def of (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : Additive (Internal.principalUnitQuotientCarrier F n)) :
    DiscretePrincipalUnitQuotient F n :=
  ⟨x⟩

/-- The defining evaluation formula for `addEquiv` is `(addEquiv F n).symm x = of F n x`. -/
@[simp] theorem addEquiv_symm_apply (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : Additive (Internal.principalUnitQuotientCarrier F n)) :
    (addEquiv F n).symm x = of F n x :=
  rfl

/-- Establishes the identity `(of F n x).val = x`. -/
@[simp] theorem val_of (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : Additive (Internal.principalUnitQuotientCarrier F n)) :
    (of F n x).val = x := rfl

/-- Establishes the identity `addEquiv F n (of F n x) = x`. -/
@[simp] theorem addEquiv_of (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : Additive (Internal.principalUnitQuotientCarrier F n)) :
    addEquiv F n (of F n x) = x := by
  rw [addEquiv_apply, val_of]

/-- Establishes the identity `of F n x.val = x`. -/
@[simp] theorem of_val (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : DiscretePrincipalUnitQuotient F n) :
    of F n x.val = x := by
  cases x
  rfl

end DiscretePrincipalUnitQuotient

/-- The product topology of the discrete coordinates on the additive
principal-unit inverse limit. -/
@[implicit_reducible]
noncomputable def principalUnitProdiscreteTopology
    (F : CompleteDVF.{u, v} K) :
    TopologicalSpace (Additive (Internal.principalUnitInverseLimitCarrier F)) := by
  letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  exact inferInstance

/-- The principal-unit inverse limit with its prodiscrete topology fixed in
the type.  For a local field, the coordinate quotients are finite and this
specializes to the usual profinite topology. -/
structure PrincipalUnitProdiscreteLimit (F : CompleteDVF.{u, v} K) where
  /-- The underlying compatible family. -/
  val : Additive (Internal.principalUnitInverseLimitCarrier F)

namespace PrincipalUnitProdiscreteLimit

/-- The carrier equivalence of the prodiscrete inverse-limit model. -/
def equiv (F : CompleteDVF.{u, v} K) :
    PrincipalUnitProdiscreteLimit F ≃
      Additive (Internal.principalUnitInverseLimitCarrier F) where
  toFun := PrincipalUnitProdiscreteLimit.val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/--
Equips the target with its canonical `TopologicalSpace` structure, namely `TopologicalSpace
(PrincipalUnitProdiscreteLimit F)`.
-/
noncomputable instance instTopologicalSpace (F : CompleteDVF.{u, v} K) :
    TopologicalSpace (PrincipalUnitProdiscreteLimit F) :=
  (principalUnitProdiscreteTopology F).induced PrincipalUnitProdiscreteLimit.val

/-- Forget the wrapper while retaining its fixed prodiscrete topology. -/
noncomputable def homeomorph (F : CompleteDVF.{u, v} K) :
    PrincipalUnitProdiscreteLimit F ≃ₜ
      WithTopology
        (Additive (Internal.principalUnitInverseLimitCarrier F))
        (principalUnitProdiscreteTopology F) where
  toEquiv := (equiv F).trans
    (WithTopology.equiv _ (principalUnitProdiscreteTopology F)).symm
  continuous_toFun := by
    let : TopologicalSpace
        (Additive (Internal.principalUnitInverseLimitCarrier F)) :=
      principalUnitProdiscreteTopology F
    change Continuous fun x : PrincipalUnitProdiscreteLimit F =>
      WithTopology.toTopology (principalUnitProdiscreteTopology F) x.val
    exact
      (WithTopology.continuous_toTopology (principalUnitProdiscreteTopology F)).comp
        continuous_induced_dom
  continuous_invFun := by
    let : TopologicalSpace
        (Additive (Internal.principalUnitInverseLimitCarrier F)) :=
      principalUnitProdiscreteTopology F
    change Continuous fun x : WithTopology
        (Additive (Internal.principalUnitInverseLimitCarrier F))
        (principalUnitProdiscreteTopology F) =>
      (⟨x.ofTopology⟩ : PrincipalUnitProdiscreteLimit F)
    exact
      continuous_induced_rng.2
        (WithTopology.continuous_ofTopology (principalUnitProdiscreteTopology F))

/--
Equips the target with its canonical `AddCommGroup` structure, namely `AddCommGroup
(PrincipalUnitProdiscreteLimit F)`.
-/
instance instAddCommGroup (F : CompleteDVF.{u, v} K) :
    AddCommGroup (PrincipalUnitProdiscreteLimit F) :=
  (equiv F).addCommGroup

/-- The algebraic equivalence forgetting the type-level prodiscrete model. -/
def addEquiv (F : CompleteDVF.{u, v} K) :
    PrincipalUnitProdiscreteLimit F ≃+
      Additive (Internal.principalUnitInverseLimitCarrier F) :=
  (equiv F).addEquiv

/-- The defining evaluation formula for `addEquiv` is `addEquiv F x = x.val`. -/
@[simp] theorem addEquiv_apply (F : CompleteDVF.{u, v} K)
    (x : PrincipalUnitProdiscreteLimit F) :
    addEquiv F x = x.val :=
  rfl

/-- Put a compatible family into its prodiscrete model. -/
def of (F : CompleteDVF.{u, v} K)
    (x : Additive (Internal.principalUnitInverseLimitCarrier F)) :
    PrincipalUnitProdiscreteLimit F :=
  ⟨x⟩

/-- The defining evaluation formula for `addEquiv` is `(addEquiv F).symm x = of F x`. -/
@[simp] theorem addEquiv_symm_apply (F : CompleteDVF.{u, v} K)
    (x : Additive (Internal.principalUnitInverseLimitCarrier F)) :
    (addEquiv F).symm x = of F x :=
  rfl

/-- Establishes the identity `(of F x).val = x`. -/
@[simp] theorem val_of (F : CompleteDVF.{u, v} K)
    (x : Additive (Internal.principalUnitInverseLimitCarrier F)) :
    (of F x).val = x := rfl

/-- Establishes the identity `of F x.val = x`. -/
@[simp] theorem of_val (F : CompleteDVF.{u, v} K)
    (x : PrincipalUnitProdiscreteLimit F) : of F x.val = x := by
  cases x
  rfl

/-- Evaluation at one discrete coordinate, as an additive homomorphism. -/
def coordinate (F : CompleteDVF.{u, v} K) (n : ℕ) :
    PrincipalUnitProdiscreteLimit F →+
      DiscretePrincipalUnitQuotient F n :=
  (DiscretePrincipalUnitQuotient.addEquiv F n).symm.toAddMonoidHom.comp
    ((MonoidHom.toAdditive
      (Internal.principalUnitInverseLimitCarrierEval F n)).comp
        (addEquiv F).toAddMonoidHom)

/--
The defining evaluation formula for `coordinate` is `coordinate F n x =
DiscretePrincipalUnitQuotient.of F n (Additive.ofMul
(Internal.principalUnitInverseLimitCarrierEval F n (Additive.toMul (addEquiv F x))))`.
-/
@[simp] theorem coordinate_apply (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : PrincipalUnitProdiscreteLimit F) :
    coordinate F n x = DiscretePrincipalUnitQuotient.of F n
      (Additive.ofMul
        (Internal.principalUnitInverseLimitCarrierEval F n
          (Additive.toMul (addEquiv F x)))) :=
  rfl

end PrincipalUnitProdiscreteLimit

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_InverseLimitTopology
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Topology of the principal-unit inverse limit

This module identifies first principal units algebraically and topologically with the
inverse limit of their finite principal-unit quotients.
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

/-- Embed `U^1/U^(n+1)` as its class inside `O^*/U^(n+1)`. -/
noncomputable def Internal.principalUnitQuotientCarrierToFull
    (F : CompleteDVF.{u, v} K) (n : ℕ) :
    Internal.principalUnitQuotientCarrier F n →*
      F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1) :=
  ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubgroupClassInQuotient
      1 (n + 1)).subtype.comp
    ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientEquivClassInQuotientOfLe
      (Nat.le_add_left 1 n)).toMonoidHom

/--
Establishes the identity `principalUnitQuotientCarrierToFull F n
((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk 1 (n + 1) x) =
(QuotientGroup.mk (x : F.valuationSubringˣ) : F.valuationSubringˣ ⧸
(CompleteDVF.higherPrincipalUnitGroup F) (n + 1))`.
-/
@[simp] theorem Internal.principalUnitQuotientCarrierToFull_mk
    (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    principalUnitQuotientCarrierToFull F n
        ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
          1 (n + 1) x) =
      (QuotientGroup.mk (x : F.valuationSubringˣ) :
        F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) := by
  exact
    (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).coe_principalUnitSubquotientEquivClassInQuotientOfLe_mk
        (Nat.le_add_left 1 n) x

/--
The specified map is injective: `Function.Injective (principalUnitQuotientCarrierToFull F n)`.
-/
theorem Internal.principalUnitQuotientCarrierToFull_injective
    (F : CompleteDVF.{u, v} K) (n : ℕ) :
    Function.Injective (principalUnitQuotientCarrierToFull F n) := by
  exact Subtype.val_injective.comp
    ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientEquivClassInQuotientOfLe
        (Nat.le_add_left 1 n)).injective

/--
Establishes the identity `higherUnitQuotientTransition F hmn (principalUnitQuotientCarrierToFull F
n q) = principalUnitQuotientCarrierToFull F m (principalUnitQuotientCarrierTransition F hmn q)`.
-/
theorem Internal.principalUnitQuotientCarrierToFull_transition
    (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n)
    (q : Internal.principalUnitQuotientCarrier F n) :
    higherUnitQuotientTransition F hmn
        (principalUnitQuotientCarrierToFull F n q) =
      principalUnitQuotientCarrierToFull F m
        (principalUnitQuotientCarrierTransition F hmn q) := by
  refine
    AntitoneSubgroupFiltration.principalUnitSubquotient.inductionOn
      (motive := fun q =>
        higherUnitQuotientTransition F hmn
            (principalUnitQuotientCarrierToFull F n q) =
          principalUnitQuotientCarrierToFull F m
            (principalUnitQuotientCarrierTransition F hmn q))
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) 1 (n + 1) q ?_
  intro x
  exact (congrArg (higherUnitQuotientTransition F hmn)
    (principalUnitQuotientCarrierToFull_mk F n x)).trans
      (principalUnitQuotientCarrierToFull_mk F m x).symm

/-- Forget that every coordinate is represented by a first principal unit. -/
noncomputable def Internal.principalUnitInverseLimitCarrierToFull
    (F : CompleteDVF.{u, v} K) :
    Internal.principalUnitInverseLimitCarrier F →*
      Internal.higherUnitInverseLimitCarrier F where
  toFun q :=
    ⟨fun n => principalUnitQuotientCarrierToFull F n (q.1 n), by
      intro m n hmn
      rw [principalUnitQuotientCarrierToFull_transition, q.2 hmn]⟩
  map_one' := by
    apply Subtype.ext
    funext n
    change principalUnitQuotientCarrierToFull F n 1 = 1
    exact map_one _
  map_mul' q r := by
    apply Subtype.ext
    funext n
    change principalUnitQuotientCarrierToFull F n (q.1 n * r.1 n) =
      principalUnitQuotientCarrierToFull F n (q.1 n) *
        principalUnitQuotientCarrierToFull F n (r.1 n)
    exact map_mul _ _ _

/-- Canonical carrier map from `U^1` to its level-quotient limit. -/
def Internal.principalUnitToInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 →*
      Internal.principalUnitInverseLimitCarrier F where
  toFun x :=
    ⟨fun n =>
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
          1 (n + 1) x, by
      intro m n hmn
      exact principalUnitQuotientCarrierTransition_mk F hmn x⟩
  map_one' := by ext n; rfl
  map_mul' x y := by ext n; rfl

/--
Establishes the identity `principalUnitInverseLimitCarrierToFull F
(principalUnitToInverseLimitCarrier F x) = unitsEquivHigherUnitQuotientInverseLimit F (x :
F.valuationSubringˣ)`.
-/
theorem Internal.principalUnitInverseLimitCarrierToFull_to
    (F : CompleteDVF.{u, v} K) (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :
    principalUnitInverseLimitCarrierToFull F
        (principalUnitToInverseLimitCarrier F x) =
      unitsEquivHigherUnitQuotientInverseLimit F
        (x : F.valuationSubringˣ) := by
  ext n
  simp only [compatibleGroupFamiliesEval_apply]
  rw [unitsEquivHigherUnitQuotientInverseLimit_apply]
  exact principalUnitQuotientCarrierToFull_mk F n x

/-- Establishes the identity `principalUnitQuotientCarrierToFull F 0 q = 1`. -/
theorem Internal.principalUnitQuotientCarrierToFull_zero_eq_one
    (F : CompleteDVF.{u, v} K)
    (q : Internal.principalUnitQuotientCarrier F 0) :
    principalUnitQuotientCarrierToFull F 0 q = 1 := by
  refine
    AntitoneSubgroupFiltration.principalUnitSubquotient.inductionOn
      (motive := fun q => principalUnitQuotientCarrierToFull F 0 q = 1)
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F) 1 1 q ?_
  intro x
  exact (principalUnitQuotientCarrierToFull_mk F 0 x).trans
    ((QuotientGroup.eq_one_iff (x : F.valuationSubringˣ)).2 x.property)

/-- Recover a first principal unit from a compatible family of its finite
classes, by applying the adic inverse-limit equivalence to the underlying full unit family. -/
noncomputable def Internal.principalUnitInverseLimitCarrierInv
    (F : CompleteDVF.{u, v} K)
    (q : Internal.principalUnitInverseLimitCarrier F) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 := by
  let e := unitsEquivHigherUnitQuotientInverseLimit F
  let qfull := principalUnitInverseLimitCarrierToFull F q
  refine ⟨e.symm qfull, ?_⟩
  rw [← QuotientGroup.eq_one_iff]
  calc
    (QuotientGroup.mk (e.symm qfull) :
        F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) =
        (e (e.symm qfull)).1 0 :=
      (unitsEquivHigherUnitQuotientInverseLimit_apply F (e.symm qfull) 0).symm
    _ = qfull.1 0 := by rw [e.apply_symm_apply]
    _ = 1 := principalUnitQuotientCarrierToFull_zero_eq_one F (q.1 0)

/--
Establishes the identity `unitsEquivHigherUnitQuotientInverseLimit F
(principalUnitInverseLimitCarrierInv F q : F.valuationSubringˣ) =
principalUnitInverseLimitCarrierToFull F q`.
-/
theorem Internal.unitsEquiv_principalUnitInverseLimitCarrierInv
    (F : CompleteDVF.{u, v} K)
    (q : Internal.principalUnitInverseLimitCarrier F) :
    unitsEquivHigherUnitQuotientInverseLimit F
        (principalUnitInverseLimitCarrierInv F q : F.valuationSubringˣ) =
      principalUnitInverseLimitCarrierToFull F q := by
  exact (unitsEquivHigherUnitQuotientInverseLimit F).apply_symm_apply _

/-- Algebraic restriction of the adic inverse-limit equivalence:
`U^1` is the inverse limit of `U^1/U^(n+1)`. -/
noncomputable def Internal.principalUnitMulEquivInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃*
      Internal.principalUnitInverseLimitCarrier F where
  toFun := principalUnitToInverseLimitCarrier F
  invFun := principalUnitInverseLimitCarrierInv F
  left_inv x := by
    apply Subtype.ext
    change
      (unitsEquivHigherUnitQuotientInverseLimit F).symm
          (principalUnitInverseLimitCarrierToFull F
            (principalUnitToInverseLimitCarrier F x)) =
        (x : F.valuationSubringˣ)
    rw [principalUnitInverseLimitCarrierToFull_to]
    exact (unitsEquivHigherUnitQuotientInverseLimit F).symm_apply_apply _
  right_inv q := by
    ext n
    apply principalUnitQuotientCarrierToFull_injective F n
    change
      principalUnitQuotientCarrierToFull F n
          ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
            1 (n + 1) (principalUnitInverseLimitCarrierInv F q)) =
        principalUnitQuotientCarrierToFull F n (q.1 n)
    rw [principalUnitQuotientCarrierToFull_mk]
    calc
      (QuotientGroup.mk
          (principalUnitInverseLimitCarrierInv F q : F.valuationSubringˣ) :
          F.valuationSubringˣ ⧸ (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) (n + 1)) =
          (unitsEquivHigherUnitQuotientInverseLimit F
            (principalUnitInverseLimitCarrierInv F q :
              F.valuationSubringˣ)).1 n :=
        (unitsEquivHigherUnitQuotientInverseLimit_apply F _ n).symm
      _ = (principalUnitInverseLimitCarrierToFull F q).1 n := by
        rw [unitsEquiv_principalUnitInverseLimitCarrierInv]
      _ = principalUnitQuotientCarrierToFull F n (q.1 n) := rfl
  map_mul' x y := by
    exact (principalUnitToInverseLimitCarrier F).map_mul x y

/-- Topological restriction of the adic inverse-limit equivalence: with the adic topology on `U^1` and
the product topology of the discrete quotient coordinates,
`U^1` is homeomorphic to `lim U^1/U^(n+1)`. -/
noncomputable def Internal.principalUnitHomeomorphInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
      fun _ => ⊥
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 ≃ₜ
      Internal.principalUnitInverseLimitCarrier F := by
  let pi := chosenPrincipalUnitPadicUniformizer F
  letI : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal pi 1).adicTopology
  letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  letI : (n : ℕ) → DiscreteTopology (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⟨rfl⟩
  let fullQuotientTopology (n : ℕ) : TopologicalSpace
      (F.valuationSubringˣ ⧸
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
          (n + 1)) := ⊥
  letI : (n : ℕ) → TopologicalSpace
      (F.valuationSubringˣ ⧸
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
          (n + 1)) :=
    fullQuotientTopology
  letI : (n : ℕ) → DiscreteTopology
      (F.valuationSubringˣ ⧸
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
          (n + 1)) :=
    fun _ => ⟨rfl⟩
  let e := principalUnitMulEquivInverseLimitCarrier F
  let hfull := Internal.unitsHomeomorphHigherUnitQuotientInverseLimit F
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change Continuous fun x => e x
    exact Continuous.subtype_mk
      (continuous_pi fun n => by
        change Continuous fun x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 =>
          (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
            1 (n + 1) x
        have hfullCoord : Continuous fun x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 =>
            (QuotientGroup.mk (x : F.valuationSubringˣ) :
              F.valuationSubringˣ ⧸
                (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
                  (n + 1)) := by
          have hsub : Continuous fun x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 =>
              (x : F.valuationSubringˣ) := continuous_subtype_val
          have hcoord : Continuous fun z : Internal.higherUnitInverseLimitCarrier F =>
              z.1 n :=
            (continuous_apply n).comp continuous_subtype_val
          have h := hcoord.comp (hfull.continuous.comp hsub)
          convert h using 1
          all_goals try with_reducible_and_instances rfl
          funext x
          have hx :=
            Internal.unitsHomeomorphHigherUnitQuotientInverseLimit_apply
              F (x : F.valuationSubringˣ) n
          simpa only [hfull, Function.comp_apply] using hx.symm
        let f := principalUnitQuotientCarrierToFull F n
        let decode :
            (F.valuationSubringˣ ⧸
              (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
                (n + 1)) →
              Internal.principalUnitQuotientCarrier F n :=
          Function.invFun f
        have hdecode : Continuous decode :=
          continuous_of_discreteTopology
        have hstage : Continuous fun x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 =>
            decode
              (QuotientGroup.mk (x : F.valuationSubringˣ) :
                F.valuationSubringˣ ⧸
                  (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
                    (n + 1)) :=
          hdecode.comp hfullCoord
        convert hstage using 1
        all_goals try with_reducible_and_instances rfl
        funext x
        symm
        change Function.invFun f
            (QuotientGroup.mk (x : F.valuationSubringˣ) :
              F.valuationSubringˣ ⧸
                (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
                  (n + 1)) =
          (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
            1 (n + 1) x
        rw [← principalUnitQuotientCarrierToFull_mk F n x]
        exact Function.leftInverse_invFun
          (principalUnitQuotientCarrierToFull_injective F n) _)
      (fun x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1 => by
        intro i j hij
        exact (e x).2 hij)
  · have hToFull : Continuous fun q : Internal.principalUnitInverseLimitCarrier F =>
        principalUnitInverseLimitCarrierToFull F q := by
      exact Continuous.subtype_mk
        (continuous_pi fun n => by
          change Continuous fun q : Internal.principalUnitInverseLimitCarrier F =>
            principalUnitQuotientCarrierToFull F n (q.1 n)
          exact continuous_of_discreteTopology.comp
            ((continuous_apply n).comp continuous_subtype_val))
        (fun q : Internal.principalUnitInverseLimitCarrier F => by
          intro i j hij
          exact (principalUnitInverseLimitCarrierToFull F q).2 hij)
    have hInvFull : Continuous fun q : Internal.principalUnitInverseLimitCarrier F =>
        hfull.symm (principalUnitInverseLimitCarrierToFull F q) :=
      hfull.continuous_symm.comp hToFull
    change Continuous fun q => e.symm q
    exact Continuous.subtype_mk
      (by
        convert hInvFull using 1
        all_goals try with_reducible_and_instances rfl
        funext q
        change
          (principalUnitInverseLimitCarrierInv F q : F.valuationSubringˣ) =
            hfull.symm (principalUnitInverseLimitCarrierToFull F q)
        apply hfull.injective
        rw [hfull.apply_symm_apply]
        ext n
        change
          (hfull
            (principalUnitInverseLimitCarrierInv F q :
              F.valuationSubringˣ)).1 n =
            (principalUnitInverseLimitCarrierToFull F q).1 n
        calc
          (hfull
              (principalUnitInverseLimitCarrierInv F q :
                F.valuationSubringˣ)).1 n =
              (QuotientGroup.mk
                (principalUnitInverseLimitCarrierInv F q :
                  F.valuationSubringˣ) :
              F.valuationSubringˣ ⧸
                (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F)
                  (n + 1)) := by
            simpa only [hfull] using
              (Internal.unitsHomeomorphHigherUnitQuotientInverseLimit_apply F
                (principalUnitInverseLimitCarrierInv F q :
                  F.valuationSubringˣ) n)
          _ =
              (unitsEquivHigherUnitQuotientInverseLimit F
                (principalUnitInverseLimitCarrierInv F q :
                  F.valuationSubringˣ)).1 n :=
            (unitsEquivHigherUnitQuotientInverseLimit_apply F _ n).symm
          _ = (principalUnitInverseLimitCarrierToFull F q).1 n := by
            rw [unitsEquiv_principalUnitInverseLimitCarrierInv])
      (fun q : Internal.principalUnitInverseLimitCarrier F => (e.symm q).property)

/--
The defining evaluation formula for `Internal.principalUnitMulEquivInverseLimitCarrier` is
`principalUnitInverseLimitCarrierEval F n (principalUnitMulEquivInverseLimitCarrier F x) =
(higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk 1 (n + 1) x`.
-/
@[simp] theorem Internal.principalUnitMulEquivInverseLimitCarrier_apply
    (F : CompleteDVF.{u, v} K)
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) (n : ℕ) :
    principalUnitInverseLimitCarrierEval F n
        (principalUnitMulEquivInverseLimitCarrier F x) =
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotientMk
        1 (n + 1) x :=
  rfl



/-- Additive form of the algebraic restriction `U^1 ≃ lim U^1/U^(n+1)`. -/
noncomputable def Internal.principalUnitAddEquivInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) :
    Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) ≃+
      Additive (Internal.principalUnitInverseLimitCarrier F) where
  toFun x := Additive.ofMul
    (principalUnitMulEquivInverseLimitCarrier F (Additive.toMul x))
  invFun x := Additive.ofMul
    ((principalUnitMulEquivInverseLimitCarrier F).symm (Additive.toMul x))
  left_inv x := by
    change Additive.ofMul
        ((principalUnitMulEquivInverseLimitCarrier F).symm
          (principalUnitMulEquivInverseLimitCarrier F (Additive.toMul x))) = x
    rw [(principalUnitMulEquivInverseLimitCarrier F).symm_apply_apply]
    rfl
  right_inv x := by
    change Additive.ofMul
        (principalUnitMulEquivInverseLimitCarrier F
          ((principalUnitMulEquivInverseLimitCarrier F).symm
            (Additive.toMul x))) = x
    rw [(principalUnitMulEquivInverseLimitCarrier F).apply_symm_apply]
    rfl
  map_add' x y := by
    change Additive.ofMul
        (principalUnitMulEquivInverseLimitCarrier F
          (Additive.toMul x * Additive.toMul y)) =
      Additive.ofMul
        (principalUnitMulEquivInverseLimitCarrier F (Additive.toMul x) *
          principalUnitMulEquivInverseLimitCarrier F (Additive.toMul y))
    rw [map_mul]

/-- Additive form of the topological inverse-limit equivalence. -/
noncomputable def Internal.principalUnitAddHomeomorphInverseLimitCarrier
    (F : CompleteDVF.{u, v} K) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
      fun _ => ⊥
    Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) ≃ₜ
      Additive (Internal.principalUnitInverseLimitCarrier F) :=
  Internal.principalUnitHomeomorphInverseLimitCarrier F

/--
The principal-unit homeomorphism to the inverse-limit carrier has the same underlying map as the
algebraic additive equivalence.
-/
@[simp]
theorem Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply
    (F : CompleteDVF.{u, v} K)
    (x : Additive
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    letI : (n : ℕ) → TopologicalSpace
        (Internal.principalUnitQuotientCarrier F n) := fun _ => ⊥
    Internal.principalUnitAddHomeomorphInverseLimitCarrier F x =
      Internal.principalUnitAddEquivInverseLimitCarrier F x :=
  rfl

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_AdicProdiscreteComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
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

namespace Internal

/-- Internal comparison from the type-level adic model to the raw
instance-parametric carrier. -/
noncomputable def adicPrincipalUnitsHomeomorphUnderlying
    (F : CompleteDVF.{u, v} K) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal
        (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    AdicPrincipalUnits F ≃ₜ
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) := by
  letI : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal
      (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
  exact (AdicPrincipalUnits.homeomorph F).trans
    (WithTopology.homeomorph
      (α := Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1))
      (topology := principalUnitAdicTopology F))

/--
The homeomorphism from the adic principal-unit model evaluates through its underlying additive
equivalence.
-/
@[simp]
theorem adicPrincipalUnitsHomeomorphUnderlying_apply
    (F : CompleteDVF.{u, v} K) (x : AdicPrincipalUnits F) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal
        (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    adicPrincipalUnitsHomeomorphUnderlying F x =
      AdicPrincipalUnits.addEquiv F x :=
  rfl

/-- Internal comparison from the type-level prodiscrete model to the raw
instance-parametric inverse-limit carrier. -/
noncomputable def principalUnitProdiscreteLimitHomeomorphUnderlying
    (F : CompleteDVF.{u, v} K) :
    letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
      fun _ => ⊥
    PrincipalUnitProdiscreteLimit F ≃ₜ
      Additive (Internal.principalUnitInverseLimitCarrier F) := by
  letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  exact (PrincipalUnitProdiscreteLimit.homeomorph F).trans
    (WithTopology.homeomorph
      (α := Additive (Internal.principalUnitInverseLimitCarrier F))
      (topology := principalUnitProdiscreteTopology F))

/--
The homeomorphism from the prodiscrete limit evaluates through its underlying additive
equivalence.
-/
@[simp]
theorem principalUnitProdiscreteLimitHomeomorphUnderlying_apply
    (F : CompleteDVF.{u, v} K) (x : PrincipalUnitProdiscreteLimit F) :
    letI : (n : ℕ) → TopologicalSpace
        (Internal.principalUnitQuotientCarrier F n) := fun _ => ⊥
    principalUnitProdiscreteLimitHomeomorphUnderlying F x =
      PrincipalUnitProdiscreteLimit.addEquiv F x :=
  rfl

end Internal

/-- The only bridge where the raw instance-parametric presentations are
installed.  Public topology APIs use `AdicPrincipalUnits` and
`PrincipalUnitProdiscreteLimit` instead. -/
noncomputable def adicPrincipalUnitsHomeomorphProdiscreteLimit
    (F : CompleteDVF.{u, v} K) :
    AdicPrincipalUnits F ≃ₜ PrincipalUnitProdiscreteLimit F := by
  letI : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal
      (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
  letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  let source := Internal.adicPrincipalUnitsHomeomorphUnderlying F
  let target := Internal.principalUnitProdiscreteLimitHomeomorphUnderlying F
  exact source.trans
    ((Internal.principalUnitAddHomeomorphInverseLimitCarrier F).trans target.symm)

/--
Establishes the identity `PrincipalUnitProdiscreteLimit.addEquiv F
(adicPrincipalUnitsHomeomorphProdiscreteLimit F x) = principalUnitAddEquivInverseLimitCarrier F
(AdicPrincipalUnits.addEquiv F x)`.
-/
@[simp]
theorem adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv
    (F : CompleteDVF.{u, v} K) (x : AdicPrincipalUnits F) :
    PrincipalUnitProdiscreteLimit.addEquiv F
        (adicPrincipalUnitsHomeomorphProdiscreteLimit F x) =
      principalUnitAddEquivInverseLimitCarrier F
        (AdicPrincipalUnits.addEquiv F x) := by
  let : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal
      (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
  let : (n : ℕ) → TopologicalSpace
      (Internal.principalUnitQuotientCarrier F n) := fun _ => ⊥
  let source := Internal.adicPrincipalUnitsHomeomorphUnderlying F
  let target := Internal.principalUnitProdiscreteLimitHomeomorphUnderlying F
  calc
    PrincipalUnitProdiscreteLimit.addEquiv F
        (adicPrincipalUnitsHomeomorphProdiscreteLimit F x) =
      target (adicPrincipalUnitsHomeomorphProdiscreteLimit F x) := by
        rw [Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply]
    _ = principalUnitAddHomeomorphInverseLimitCarrier F (source x) := by
      exact target.apply_symm_apply _
    _ = principalUnitAddEquivInverseLimitCarrier F
        (AdicPrincipalUnits.addEquiv F x) := by
      rw [principalUnitAddHomeomorphInverseLimitCarrier_apply,
        Internal.adicPrincipalUnitsHomeomorphUnderlying_apply]

/-- Algebraic form of the canonical identification between adic principal
units and their prodiscrete limit. -/
noncomputable def adicPrincipalUnitsAddEquivProdiscreteLimit
    (F : CompleteDVF.{u, v} K) :
    AdicPrincipalUnits F ≃+ PrincipalUnitProdiscreteLimit F :=
  (AdicPrincipalUnits.addEquiv F).trans
    ((principalUnitAddEquivInverseLimitCarrier F).trans
      (PrincipalUnitProdiscreteLimit.addEquiv F).symm)

/--
The defining evaluation formula for `adicPrincipalUnitsHomeomorphProdiscreteLimit` is
`adicPrincipalUnitsHomeomorphProdiscreteLimit F x = adicPrincipalUnitsAddEquivProdiscreteLimit F
x`.
-/
@[simp] theorem adicPrincipalUnitsHomeomorphProdiscreteLimit_apply
    (F : CompleteDVF.{u, v} K) (x : AdicPrincipalUnits F) :
    adicPrincipalUnitsHomeomorphProdiscreteLimit F x =
      adicPrincipalUnitsAddEquivProdiscreteLimit F x :=
  (PrincipalUnitProdiscreteLimit.addEquiv F).injective (by
    rw [adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv]
    change
      principalUnitAddEquivInverseLimitCarrier F
          (AdicPrincipalUnits.addEquiv F x) =
        PrincipalUnitProdiscreteLimit.addEquiv F
          ((PrincipalUnitProdiscreteLimit.addEquiv F).symm
            (principalUnitAddEquivInverseLimitCarrier F
              (AdicPrincipalUnits.addEquiv F x)))
    exact ((PrincipalUnitProdiscreteLimit.addEquiv F).apply_symm_apply _).symm)

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_QuotientTransition
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Transitions between principal-unit quotients

These additive maps use the concrete principal-unit filtration of a complete
discrete valuation field. Neither finiteness nor a scalar action is required.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

open ValuationTheory.DiscreteValuationField
open Internal

universe u v

variable {K : Type u} [Field K]

/-- Additive form of a transition between principal-unit quotients. -/
def Internal.principalUnitQuotientCarrierTransitionAdd
    (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n) :
    Additive (Internal.principalUnitQuotientCarrier F n) →+
      Additive (Internal.principalUnitQuotientCarrier F m) where
  toFun x := Additive.ofMul
    (principalUnitQuotientCarrierTransition F hmn (Additive.toMul x))
  map_zero' := by
    change Additive.ofMul
        (principalUnitQuotientCarrierTransition F hmn 1) = Additive.ofMul 1
    rw [map_one]
  map_add' x y := by
    change Additive.ofMul
        (principalUnitQuotientCarrierTransition F hmn
          (Additive.toMul x * Additive.toMul y)) =
      Additive.ofMul
        (principalUnitQuotientCarrierTransition F hmn (Additive.toMul x) *
          principalUnitQuotientCarrierTransition F hmn (Additive.toMul y))
    rw [map_mul]

namespace DiscretePrincipalUnitQuotient

/-- Reduction between two wrapped discrete quotient coordinates. -/
def transition (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n) :
    DiscretePrincipalUnitQuotient F n →+
      DiscretePrincipalUnitQuotient F m where
  toFun x := of F m
    (Internal.principalUnitQuotientCarrierTransitionAdd F hmn x.val)
  map_zero' := by
    apply (addEquiv F m).injective
    change Internal.principalUnitQuotientCarrierTransitionAdd F hmn 0 = 0
    exact (Internal.principalUnitQuotientCarrierTransitionAdd F hmn).map_zero
  map_add' x y := by
    apply (addEquiv F m).injective
    change Internal.principalUnitQuotientCarrierTransitionAdd F hmn
        (x.val + y.val) =
      Internal.principalUnitQuotientCarrierTransitionAdd F hmn x.val +
        Internal.principalUnitQuotientCarrierTransitionAdd F hmn y.val
    exact (Internal.principalUnitQuotientCarrierTransitionAdd F hmn).map_add x.val y.val

/-- The wrapped transition has the original additive transition as its value. -/
@[simp] theorem val_transition
    (F : CompleteDVF.{u, v} K) {m n : ℕ} (hmn : m ≤ n)
    (x : DiscretePrincipalUnitQuotient F n) :
    (transition F hmn x).val =
      Internal.principalUnitQuotientCarrierTransitionAdd F hmn x.val :=
  rfl

end DiscretePrincipalUnitQuotient

end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_FiniteQuotientPadicModule
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
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

/-- The residue degree `f`, chosen from the finite-field identity `q = p^f`. -/
noncomputable def principalUnitResidueDegree
    (F : LocalField.{u, v} K) : ℕ+ := by
  letI := Fintype.ofFinite F.residueField
  exact Classical.choose
    (FiniteField.card F.residueField F.residueCharacteristic)

/--
Establishes the identity `F.residueCharacteristic.Prime ∧ Nat.card F.residueField =
F.residueCharacteristic ^ (principalUnitResidueDegree F : ℕ)`.
-/
theorem residueCharacteristic_prime_and_card_eq_pow_residueDegree
    (F : LocalField.{u, v} K) :
    F.residueCharacteristic.Prime ∧
      Nat.card F.residueField =
        F.residueCharacteristic ^ (principalUnitResidueDegree F : ℕ) := by
  let := Fintype.ofFinite F.residueField
  have h := Classical.choose_spec
    (FiniteField.card F.residueField F.residueCharacteristic)
  refine ⟨h.1, ?_⟩
  simpa [principalUnitResidueDegree, Nat.card_eq_fintype_card] using h.2

/-- The type in `Finite (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)` is finite. -/
instance Internal.principalUnitQuotientCarrier_finite
    (F : LocalField.{u, v} K) (n : ℕ) :
    Finite (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := by
  have : Finite
      (F.valuationSubringˣ ⧸
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) (n + 1)) :=
    higherPrincipalUnitGroup.finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
      F.toCompleteDVF (n + 1)
  exact Finite.of_injective
    (principalUnitQuotientCarrierToFull F.toCompleteDVF n)
    (principalUnitQuotientCarrierToFull_injective F.toCompleteDVF n)

/-- The `n`-th first-principal-unit quotient has cardinality `p^(f*n)`. -/
theorem Internal.card_principalUnitQuotientCarrier_eq_residueCharacteristic_pow
    (F : LocalField.{u, v} K) (n : ℕ) :
    Nat.card (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =
      F.residueCharacteristic ^ ((principalUnitResidueDegree F : ℕ) * n) := by
  have hcard :=
    higherPrincipalUnitGroup.card_principalUnitSubquotient_one_eq_residue_pow_of_uniformizer
      F.toCompleteDVF
      (chosenPrincipalUnitPadicUniformizer_isUniformizer F.toCompleteDVF)
      (Nat.le_add_left 1 n)
  rw [show n + 1 - 1 = n by omega] at hcard
  have hcard' :
      Nat.card (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =
        Nat.card F.residueField ^ n := by
    let e :
        Internal.principalUnitQuotientCarrier F.toCompleteDVF n ≃
          (higherPrincipalUnitGroup F.toCompleteDVF 1 ⧸
            (higherPrincipalUnitGroup F.toCompleteDVF (n + 1)).subgroupOf
              (higherPrincipalUnitGroup F.toCompleteDVF 1)) := by
      change
        (higherPrincipalUnitGroup.toPrincipalUnitFiltration
            F.toCompleteDVF).principalUnitSubquotient 1 (n + 1) ≃
          ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
              F.toCompleteDVF).principalUnitSubgroup 1 ⧸
            ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
              F.toCompleteDVF).principalUnitSubgroup (n + 1)).subgroupOf
                ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
                  F.toCompleteDVF).principalUnitSubgroup 1))
      exact
        (AntitoneSubgroupFiltration.principalUnitSubquotientConcreteEquiv
          (higherPrincipalUnitGroup.toPrincipalUnitFiltration F.toCompleteDVF)
          1 (n + 1)).toEquiv
    let : Finite
        (higherPrincipalUnitGroup F.toCompleteDVF 1 ⧸
          (higherPrincipalUnitGroup F.toCompleteDVF (n + 1)).subgroupOf
            (higherPrincipalUnitGroup F.toCompleteDVF 1)) :=
      Finite.of_equiv
        (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)
        e
    calc
      Nat.card (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) =
          Nat.card
            (higherPrincipalUnitGroup F.toCompleteDVF 1 ⧸
              (higherPrincipalUnitGroup F.toCompleteDVF (n + 1)).subgroupOf
                (higherPrincipalUnitGroup F.toCompleteDVF 1)) :=
        Nat.card_congr e
      _ = Nat.card F.residueField ^ n := by
        exact hcard
  rw [hcard',
    (residueCharacteristic_prime_and_card_eq_pow_residueDegree F).2,
    pow_mul]

/-- Lagrange's theorem gives the exact exponent bound needed to reduce a
p-adic scalar modulo `p^(f*n)`. -/
theorem Internal.principalUnitQuotientCarrier_pow_residueCharacteristic_pow_eq_one
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : Internal.principalUnitQuotientCarrier F.toCompleteDVF n) :
    x ^ (F.residueCharacteristic ^
        ((principalUnitResidueDegree F : ℕ) * n)) = 1 := by
  rw [← card_principalUnitQuotientCarrier_eq_residueCharacteristic_pow F n]
  exact pow_card_eq_one'

/--
Establishes the identity `(F.residueCharacteristic ^ ((principalUnitResidueDegree F : ℕ) * n)) • x
= 0`.
-/
theorem Internal.principalUnitQuotientCarrier_nsmul_residueCharacteristic_pow_eq_zero
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :
    (F.residueCharacteristic ^
        ((principalUnitResidueDegree F : ℕ) * n)) • x = 0 := by
  change Additive.ofMul
      ((Additive.toMul x) ^ (F.residueCharacteristic ^
        ((principalUnitResidueDegree F : ℕ) * n))) = Additive.ofMul 1
  rw [principalUnitQuotientCarrier_pow_residueCharacteristic_pow_eq_one]

/-- The canonical `ZMod (p^(f*n))`-module on the `n`-th finite coordinate. -/
@[implicit_reducible]
noncomputable def Internal.principalUnitQuotientCarrierZModModule
    (F : LocalField.{u, v} K) (n : ℕ) :
    Module
      (ZMod (F.residueCharacteristic ^
        ((principalUnitResidueDegree F : ℕ) * n)))
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :=
  AddCommGroup.zmodModule
    (n := F.residueCharacteristic ^
      ((principalUnitResidueDegree F : ℕ) * n))
    (G := Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n))
    (principalUnitQuotientCarrier_nsmul_residueCharacteristic_pow_eq_zero F n)

/-- Restriction of scalars along `Z_p -> ZMod (p^(f*n))`. -/
noncomputable instance Internal.principalUnitQuotientCarrierPadicModule
    (F : LocalField.{u, v} K) (n : ℕ) :
    Module ℤ_[F.residueCharacteristic]
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) := by
  letI := principalUnitQuotientCarrierZModModule F n
  exact Module.compHom _
    (PadicInt.toZModPow ((principalUnitResidueDegree F : ℕ) * n))

/--
Equips the target in `Module ℤ_[F.residueCharacteristic] (DiscretePrincipalUnitQuotient
F.toCompleteDVF n)` with the indicated module structure.
-/
noncomputable instance discretePrincipalUnitQuotientPadicModule
    (F : LocalField.{u, v} K) (n : ℕ) :
    Module ℤ_[F.residueCharacteristic]
      (DiscretePrincipalUnitQuotient F.toCompleteDVF n) :=
  AddEquiv.module
    (β := Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n))
    ℤ_[F.residueCharacteristic]
    (DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n)

/--
Establishes the identity `DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n (a • x) = a •
DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n x`.
-/
@[simp]
theorem DiscretePrincipalUnitQuotient.addEquiv_map_smul
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : ℤ_[F.residueCharacteristic])
    (x : DiscretePrincipalUnitQuotient F.toCompleteDVF n) :
    DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n (a • x) =
      a • DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n x :=
  rfl

/-- The finite-coordinate scalar written explicitly through reduction of a
p-adic integer modulo `p^(f*n)`. -/
noncomputable def Internal.principalUnitQuotientCarrierPadicScalar
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :
    Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := by
  letI := principalUnitQuotientCarrierZModModule F n
  exact PadicInt.toZModPow
    ((principalUnitResidueDegree F : ℕ) * n) a • x

/-- Establishes the identity `principalUnitQuotientCarrierPadicScalar F n a x = a • x`. -/
@[simp] theorem Internal.principalUnitQuotientCarrierPadicScalar_eq_smul
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :
    principalUnitQuotientCarrierPadicScalar F n a x = a • x :=
  rfl

/-- Reduction between finite principal-unit quotients is `Z_p`-linear.  The
key point is compatibility of `toZModPow` with the cast from level `f*n` to
level `f*m`. -/
theorem Internal.principalUnitQuotientCarrierTransitionAdd_map_smul
    (F : LocalField.{u, v} K) {m n : ℕ} (hmn : m ≤ n)
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :
    principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn (a • x) =
      a • principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn x := by
  let f : ℕ := principalUnitResidueDegree F
  let p : ℕ := F.residueCharacteristic
  have hlevels : f * m ≤ f * n := Nat.mul_le_mul_left f hmn
  let sourceModule : Module (ZMod (p ^ (f * n)))
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) := by
    simpa [p, f] using principalUnitQuotientCarrierZModModule F n
  let targetModule : Module (ZMod (p ^ (f * m)))
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF m)) := by
    simpa [p, f] using principalUnitQuotientCarrierZModModule F m
  let targetModuleAtN : Module (ZMod (p ^ (f * n)))
      (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF m)) :=
    Module.compHom _
      (ZMod.castHom (pow_dvd_pow p hlevels) (ZMod (p ^ (f * m))))
  change
    principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn
        (PadicInt.toZModPow (f * n) a • x) =
      PadicInt.toZModPow (f * m) a •
        principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn x
  calc
    principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn
        (PadicInt.toZModPow (f * n) a • x) =
        PadicInt.toZModPow (f * n) a •
          principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn x :=
      ZMod.map_smul
        (principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn)
        _ _
    _ = (PadicInt.toZModPow (f * n) a).cast •
          principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn x := rfl
    _ = PadicInt.toZModPow (f * m) a •
          principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn x := by
      rw [PadicInt.cast_toZModPow (f * m) (f * n) hlevels]

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_ProdiscretePadicModule
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_principalUnitSubquotientEquivClassInQuotient_map _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mapLevelOfMapsFiltrationLevels_apply _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.mem_filtrationPreimageSubgroup_iff _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientMapOfMapsFiltrationLevels_apply_mk' _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_mk_mk _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply
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

/-- Coordinatewise p-adic scalar multiplication on the compatible inverse
limit. -/
noncomputable instance Internal.principalUnitInverseLimitCarrierPadicSMul
    (F : LocalField.{u, v} K) :
    SMul ℤ_[F.residueCharacteristic]
      (Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF)) where
  smul a x := Additive.ofMul
    ⟨fun n => Additive.toMul
        (a • Additive.ofMul ((Additive.toMul x).1 n)), by
      intro m n hmn
      apply Additive.ofMul.injective
      change
        principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn
            (a • Additive.ofMul ((Additive.toMul x).1 n)) =
          a • Additive.ofMul ((Additive.toMul x).1 m)
      rw [principalUnitQuotientCarrierTransitionAdd_map_smul]
      change
        a • Additive.ofMul
            (principalUnitQuotientCarrierTransition F.toCompleteDVF hmn
              ((Additive.toMul x).1 n)) =
          a • Additive.ofMul ((Additive.toMul x).1 m)
      rw [(Additive.toMul x).2 hmn]⟩

/--
The defining evaluation formula for `Internal.principalUnitInverseLimitCarrierPadic_smul` is
`Additive.ofMul (Internal.principalUnitInverseLimitCarrierEval F.toCompleteDVF n (Additive.toMul
(a • x))) = a • Additive.ofMul (Internal.principalUnitInverseLimitCarrierEval F.toCompleteDVF n
(Additive.toMul x))`.
-/
@[simp] theorem Internal.principalUnitInverseLimitCarrierPadic_smul_apply
    (F : LocalField.{u, v} K)
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF))
    (n : ℕ) :
    Additive.ofMul
        (Internal.principalUnitInverseLimitCarrierEval F.toCompleteDVF n
          (Additive.toMul (a • x))) =
      a • Additive.ofMul
        (Internal.principalUnitInverseLimitCarrierEval F.toCompleteDVF n
          (Additive.toMul x)) :=
  rfl

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end


