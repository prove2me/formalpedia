-- Prove2me | Definitions.Def_OAIQ244Duke104
-- name    : OAIQ244Duke104
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T03:52:19.684948+00:00
-- url     : https://prove2.me/theorems/62eb6dfc-3934-4905-b37b-a7a623e4f0e3
-- title:
--   Definitions bundle OAIQ244Duke104 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 18 definitions and 21 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.abelianizedExtensionQuotientAddEquiv_transportBase`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteUnramifiedInclusion`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteUnramifiedInclusionSMul`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldFiniteIdeleGroupGroup`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldFiniteNormResidueGaloisEquiv`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldGlobalNormResidueMonoidHom`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldIdeleClassToAmbientFixedMonoidHom`, `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldIdeleGroupGroup`, `GlobalClassFieldTheory.Reciprocity.ambientFixedGlobalNormResidueAddMonoidHom`, `GlobalClassFieldTheory.Reciprocity.extensionQuotientMulEquivOfEq`, `GlobalClassFieldTheory.Reciprocity.extensionQuotientMulEquiv_transportFiniteGalois`, `GlobalClassFieldTheory.Reciprocity.globalNormResidueEquivOfEmbedding`, `GlobalClassFieldTheory.Reciprocity.globalNormResidueMonoidHomOfEmbedding`, `GlobalClassFieldTheory.Reciprocity.naturalityIdeleClassCommGroup`, `GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_AbstractFixedFieldGlobalNormResidue`, `GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedGeometricRestriction`, `GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedLocalGlobalCompatibility`, `GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedRestriction`, `GlobalClassFieldTheory_Reciprocity_GlobalNormResidueAbelianization`, `GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality`.
--
--   **Imports.** It imports the bundle `OAIQ244Duke121` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke107`, `OAIQ244Duke108` and `OAIQ244Duke109`.
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
import Definitions.Def_OAIQ244Duke121

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_AbstractFixedFieldGlobalNormResidue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.normSubgroupMap_val _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNormQuotientTowerMap_mk _root_.GlobalClassFieldTheory.GlobalClassFields.narrowFiniteConductorRayClassGroupToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.normQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqNormQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientCongr_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientToIdeleClassNormQuotient_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicGalEquivZHat_extensionClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicGalEquivZHat_quotientClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_extensionClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_relativeIdeleNorm_eq_one _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.mem_globalArtinFiniteSupport_iff _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationGlobalArtin_principalIdele _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.fractionalIdeal_finitePrimeIdele _root_.IdeleGroup.idealClass_finitePrimeIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.signToNarrow_mk
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
# Global norm residue on actual fixed fields

An abstract finite abelian subextension of the rational absolute Galois
group determines an actual finite abelian extension between its two
fixed number fields.  This file transports the abstract norm-residue
symbol directly to the ordinary idele-class norm quotient of those
fixed fields.

Keeping this construction in one ambient separable closure is essential
for the norm--restriction diagrams: no independently chosen embedding of
either field is introduced.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

section EmbeddedNumberFieldRealization

attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedIdeleClassGroupIsMulCommutative
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedIdeleClassSubgroupNormal
variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedExtensionSubgroupNormal
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedExtensionQuotientFinite
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbsoluteQuotientFinite
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractFixedFieldFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractRelativeFixedFieldFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractFixedFieldScalarTower
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractRelativeFixedFieldAbsoluteFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractFixedFieldNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractRelativeFixedFieldNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsNumberField
noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsAlgebra_r709b44_1
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Algebra
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      ((abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)).restrictScalars ℚ) :=
  (IntermediateField.inclusion
    (abstractFixedField_le ℚ (SeparableClosure ℚ)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j))).toRingHom.toAlgebra
noncomputable local instance
    numberFieldEmbeddedAbstractRelativeFixedFieldIsGalois_r709b44_1
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedBaseSubgroup K L j))
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    (numberFieldEmbeddedBaseSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup K L j)
    (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
    (numberFieldEmbeddedExtensionSubgroupNormal K L j)
variable [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The abelianized quotient of the explicitly embedded tower is the
actual abelian Galois group. -/
noncomputable def
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Additive
      (Abelianization
        (numberFieldEmbeddedFiniteGaloisSubextension K L j).extensionQuotient) ≃+
      Additive Gal(L / K) :=
  MulEquiv.toAdditive
    ((MulEquiv.abelianizationCongr
      (numberFieldEmbeddedExtensionQuotientEquivGaloisGroup K L j)).trans
        (Abelianization.equivOfComm :
          Gal(L / K) ≃*
            Abelianization Gal(L / K)).symm)

/-- The actual global norm-residue equivalence constructed from an
explicit compatible embedding of a finite abelian number-field
extension into the rational separable closure. -/
noncomputable def globalNormResidueEquivOfEmbedding
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃+
      Additive Gal(L / K) := by
  let eNorm :
      FiniteNormQuotient rationalIdeleClassRepresentation
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j) ≃+
        Additive
          (Abelianization
            (numberFieldEmbeddedFiniteGaloisSubextension K L j).extensionQuotient) :=
    rationalCyclotomicDegreeData.normResidueSymbol
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      (numberFieldEmbeddedFiniteAbstractField K L j)
      (numberFieldEmbeddedFiniteGaloisSubextension K L j)
  exact
    (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
        K L j).symm.trans
      (eNorm.trans
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L j))

/-- The global norm-residue homomorphism obtained from an explicit
compatible embedding. -/
noncomputable def globalNormResidueMonoidHomOfEmbedding
    (j : L →ₐ[ℚ] SeparableClosure ℚ) :
    IdeleClassGroup K →* Gal(L / K) := by
  let e :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃*
        Gal(L / K) :=
    AddEquiv.toMultiplicative
      (globalNormResidueEquivOfEmbedding K L j)
  exact
    e.toMonoidHom.comp
      (QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range)

/-- Evaluation of the explicit-embedding global norm-residue map is
the abstract norm-residue symbol evaluated on the corresponding genuine
fixed-part finite norm class. -/
@[simp]
theorem globalNormResidueMonoidHomOfEmbedding_apply
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K) :
    globalNormResidueMonoidHomOfEmbedding K L j c =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L j
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            (numberFieldEmbeddedFiniteAbstractField K L j)
            (numberFieldEmbeddedFiniteGaloisSubextension K L j)
            (finiteNormClass rationalIdeleClassRepresentation
              (numberFieldEmbeddedBaseSubgroup K L j)
              (numberFieldEmbeddedTopSubgroup K L j)
              (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
              (numberFieldEmbeddedIdeleClassEquivAmbientFixed
                K L j (Additive.ofMul c))))) := by
  have hclass :=
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K L j c
  change
    Additive.toMul
      (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
        K L j
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldEmbeddedFiniteAbstractField K L j)
          (numberFieldEmbeddedFiniteGaloisSubextension K L j)
          ((numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
            K L j).symm
            (Additive.ofMul
              (QuotientGroup.mk'
                (_root_.ideleClassNorm K L).range c))))) =
      _
  rw [← hclass,
    (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
      K L j).symm_apply_apply]

end EmbeddedNumberFieldRealization

variable
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)

local instance abstractFixedFieldBaseQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K.field (le_baseField K.field)) :=
  K.finite

local instance abstractFixedFieldRelativeQuotientFinite :
    Finite
      (K.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup K.field L.field L.below) :=
  L.finite

local instance abstractFixedFieldRelativeQuotientIsMulCommutative_r709b44_1 :
    IsMulCommutative L.extensionQuotient :=
  L.commutative
noncomputable local instance abstractFixedFieldFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K.field K.finite

noncomputable local instance abstractRelativeFixedFieldFiniteDimensional_r709b44_1 :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below K.finite L.finite
local instance abstractFixedFieldRelativeScalarTower_r709b44_1 :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
noncomputable local instance abstractRelativeFixedFieldAbsoluteFiniteDimensional_r709b44_1 :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)
noncomputable local instance abstractFixedFieldNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)

/-- The lower fixed idèle-class group is commutative.  Naming the mixin
before the public quotient declarations avoids delayed normality synthesis
inside their definition bodies. -/
local instance
    abstractFixedFieldIdeleClassGroupIsMulCommutative_r709b44_1 :
    IsMulCommutative
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) K.field)) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
noncomputable local instance abstractRelativeFixedFieldNumberField_r709b44_1 :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)
/-- Use the same explicit Galois witness as the fixed-field quotient
comparison.  Deriving it through `IsAbelianGalois` produces an equivalent
but much larger dependent instance path. -/
noncomputable local instance
    abstractRelativeFixedFieldIsGalois_r709b44_1 :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below L.normal
noncomputable local instance abstractRelativeFixedFieldIsAbelianGalois_r709b44_1 :
    IsAbelianGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois L
/-- Use one opaque normality witness for the actual fixed-field norm range.
This keeps every occurrence of its quotient group on the same instance path. -/
local instance
    abstractFixedFieldIdeleClassNormRangeNormal_r709b44_1 :
    ((_root_.ideleClassNorm
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below)).range).Normal := by
  infer_instance
/-- The abelianized abstract extension quotient is the actual Galois
group of the corresponding pair of fixed fields. -/
noncomputable def
    abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    Additive
        (Abelianization
          (FiniteGaloisSubextension.extensionQuotient
            L.toFiniteGaloisExtension)) ≃+
      Additive (Gal(E / F)) := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let e :
      L.extensionQuotient ≃*
        Gal(E / F) :=
    L.extensionQuotientMulEquiv.trans
      (abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        K.field L.field L.below L.normal)
  exact
    MulEquiv.toAdditive
      ((Abelianization.equivOfComm :
          L.extensionQuotient ≃*
            Abelianization L.extensionQuotient).symm.trans e)

/-- The abstract finite norm-residue equivalence with its dependent source
instance fixed to the public finite norm quotient. -/
noncomputable def abstractFixedFieldFiniteNormResidueGaloisEquiv :
    FiniteNormQuotient rationalIdeleClassRepresentation
        K.field L.field L.below ≃+
      Additive
        (Gal(
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below) /
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field))) := by
  letI : AddCommGroup
      (FiniteNormQuotient rationalIdeleClassRepresentation
        K.field L.field L.below) :=
    finiteNormQuotientAddCommGroup rationalIdeleClassRepresentation
      K.field L.field L.below
  exact
    @AddEquiv.trans
      (FiniteNormQuotient rationalIdeleClassRepresentation
        K.field L.field L.below)
      (Additive
        (Abelianization
          L.toFiniteGaloisExtension.extensionQuotient))
      (Additive
        (Gal(
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below) /
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field))))
      inferInstance inferInstance inferInstance
      (rationalCyclotomicDegreeData.normResidueSymbol
        rationalIdeleClassRepresentation
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        K L.toFiniteGaloisExtension)
      (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup
        K L)

/-- The abstract norm-residue symbol on the fixed part of the rational
absolute idele-class representation, with its value transported to the
actual Galois group of the two fixed fields.  This is the form consumed
directly by the abstract norm--restriction naturality theorem. -/
noncomputable def ambientFixedGlobalNormResidueAddMonoidHom :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field →+
      Additive (Gal(E / F)) := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  exact
    (abstractFixedFieldFiniteNormResidueGaloisEquiv K L).toAddMonoidHom.comp
      (finiteNormClassHom rationalIdeleClassRepresentation
        K.field L.field L.below)

/-- The ordinary idele class group of the lower fixed field, transported
to the fixed part of the rational absolute idele-class representation. -/
noncomputable def abstractFixedFieldIdeleClassToAmbientFixedMonoidHom :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    IdeleClassGroup F →*
      Multiplicative
        (ambientFixedAddSubgroup
          rationalIdeleClassRepresentation K.field) :=
  (rationalAbstractFixedFieldIdeleClassEquivFixed
    K.field).toAddMonoidHom.toMultiplicativeRight

/-- The actual norm-residue homomorphism on the ordinary idele class
group of the lower fixed field, constructed without choosing a second
field embedding. -/
noncomputable def abstractFixedFieldGlobalNormResidueMonoidHom :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    IdeleClassGroup F →* Gal(E / F) :=
  (ambientFixedGlobalNormResidueAddMonoidHom K L).toMultiplicative.comp
    (abstractFixedFieldIdeleClassToAmbientFixedMonoidHom K)

/-- Pointwise form of the transported fixed-field norm-residue homomorphism. -/
theorem abstractFixedFieldGlobalNormResidueMonoidHom_apply :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    ∀ c : IdeleClassGroup F,
      abstractFixedFieldGlobalNormResidueMonoidHom K L c =
        Additive.toMul
          (ambientFixedGlobalNormResidueAddMonoidHom K L
            ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
              (Additive.ofMul c))) := by
  dsimp only
  intro c
  rfl

/-- Transporting an ordinary fixed-field idele class to the ambient
fixed part and applying the abstract norm-residue map gives exactly the
actual fixed-field norm-residue value. -/
@[simp]
theorem abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field) :
    abstractFixedFieldGlobalNormResidueMonoidHom K L
        (Additive.toMul
          ((rationalAbstractFixedFieldIdeleClassEquivFixed
            K.field).symm a)) =
      Additive.toMul
        (ambientFixedGlobalNormResidueAddMonoidHom K L a) := by
  rw [abstractFixedFieldGlobalNormResidueMonoidHom_apply]
  change
    Additive.toMul
        (ambientFixedGlobalNormResidueAddMonoidHom K L
          ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
            ((rationalAbstractFixedFieldIdeleClassEquivFixed
              K.field).symm a))) =
      Additive.toMul
        (ambientFixedGlobalNormResidueAddMonoidHom K L a)
  rw [(rationalAbstractFixedFieldIdeleClassEquivFixed
    K.field).apply_symm_apply]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedRestriction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.normSubgroupMap_val _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Finite restriction of cyclotomic fixed-field reciprocity

For an unramified finite abelian subextension of an abstract fixed
number field, this file constructs the genuine restriction from the
cyclotomic maximal-unramified Galois group to the finite Galois group.
It then identifies the restriction of the chosen-local-factor
cyclotomic Artin map with the actual global norm-residue map.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

/-- The actual fixed field attached to `H` is a number field.  Keeping
this as one file-local instance makes it available while later idele-class
binders are elaborated. -/
noncomputable local instance
    cyclotomicUnramifiedRestriction_abstractFixedFieldNumberField_r709b44_1
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) := by
  let : FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  exact
    NumberField.of_module_finite ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
/-- The abelianized fixed-field quotient comparison sends the class of
an actual finite quotient element to the corresponding automorphism of
the concrete relative fixed field. -/
@[simp]
theorem
    abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup_of
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (q : L.extensionQuotient) :
    abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H L
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul
        ((L.extensionQuotientMulEquiv.trans
          (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
            ℚ (SeparableClosure ℚ)
            H.field L.field L.below L.normal)) q) := by
  let : IsMulCommutative L.extensionQuotient :=
    L.commutative
  apply Additive.toMul.injective
  change
    (L.extensionQuotientMulEquiv.trans
      (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        H.field L.field L.below L.normal))
      ((Abelianization.equivOfComm :
          L.extensionQuotient ≃*
            Abelianization L.extensionQuotient).symm
        (Abelianization.of q)) =
      (L.extensionQuotientMulEquiv.trans
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ)
          H.field L.field L.below L.normal)) q
  exact congrArg
    (L.extensionQuotientMulEquiv.trans
      (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        H.field L.field L.below L.normal))
    ((Abelianization.equivOfComm :
      L.extensionQuotient ≃*
        Abelianization L.extensionQuotient).symm_apply_apply q)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedGeometricRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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

open ClassFormation
open GlobalClassFields
open KummerTheory
open LocalClassFieldTheory

attribute [local instance] GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricRationalSeparableClosureAlgebra
local instance cyclotomicUnramifiedGeometricBaseQuotientFinite_r709b44_1
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H.field (le_baseField H.field)) :=
  H.finite
local instance cyclotomicUnramifiedGeometricRelativeQuotientFinite_r709b44_1
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    Finite
      (H.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          H.field L.field L.below) :=
  L.finite
noncomputable local instance
    cyclotomicUnramifiedGeometricBaseFiniteDimensional_r709b44_1
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) H.field H.finite
noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeFiniteDimensional_r709b44_1
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional L
local instance
    cyclotomicUnramifiedGeometricRelativeScalarTower_r709b44_1
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  IsScalarTower.of_algebraMap_eq' rfl
noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeAbsoluteFiniteDimensional_r709b44_1
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)
noncomputable local instance
    cyclotomicUnramifiedGeometricBaseNumberField_r709b44_1
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeNumberField_r709b44_1
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)
noncomputable local instance
    cyclotomicUnramifiedGeometricRelativeIsAbelianGalois_r709b44_1
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field) :
    IsAbelianGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois L
noncomputable local instance
    cyclotomicUnramifiedGeometricMaximalIsAbelianGalois_r709b44_1
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    IsAbelianGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)) :=
  abstractFixedFieldCyclotomic_isAbelianGalois H
/-- An unramified finite fixed field lies in the cyclotomic
maximal-unramified fixed field. -/
theorem abstractFixedFieldCyclotomicFiniteUnramifiedField_le
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below ≤
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field) := by
  apply abstractFixedField_le
  exact
    (L.toFiniteGaloisExtension.isUnramified_iff_inertia_le
      rationalCyclotomicDegreeData).1 hUnramified

/-- The actual inclusion of an unramified finite fixed field into the
cyclotomic maximal-unramified field, over the common fixed base. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let U :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    E →ₐ[F] U := by
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let U :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let j : E →ₐ[ℚ] U :=
    IntermediateField.inclusion
      (abstractFixedFieldCyclotomicFiniteUnramifiedField_le
        H L hUnramified)
  exact
    { j.toRingHom with
      commutes' := fun _ => by
        apply Subtype.ext
        rfl }

/-- The algebra structure induced by the geometric inclusion of the
finite unramified fixed field into the cyclotomic maximal-unramified
field. -/
@[implicit_reducible]
noncomputable def
    abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let U :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    Algebra E U :=
  (abstractFixedFieldCyclotomicFiniteUnramifiedInclusion
    H L hUnramified).toRingHom.toAlgebra

/-- The scalar action belonging to the inclusion-induced algebra
structure.  Naming it prevents typeclass search from exploring the
unrelated intermediate-field algebra paths. -/
@[implicit_reducible]
noncomputable def
    abstractFixedFieldCyclotomicFiniteUnramifiedInclusionSMul
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData) :
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let U :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)
    SMul E U :=
  Algebra.toSMul
    (self :=
      abstractFixedFieldCyclotomicFiniteUnramifiedInclusionAlgebra
        H L hUnramified)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
attribute [-simp] _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup_of _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicGalEquivZHat_extensionClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicGalEquivZHat_quotientClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_extensionClass _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom _root_.GlobalClassFieldTheory.Reciprocity.infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Naturality of the global norm-residue symbol

This file records the same-base restriction specialization of abstract
norm-residue naturality in the rational absolute class formation.  All
closed subgroups remain in one fixed separable-closure ambient, so the
statement is directly usable by fixed-field overextension arguments.
-/

open scoped IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

universe u

@[instance_reducible]
noncomputable def naturalityIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] : CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] naturalityIdeleClassCommGroup

local instance ideleClassGroupIsMulCommutative_r709b44_1
    {F : Type} [Field F] [NumberField F]
    : IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
local instance ideleClassSubgroupNormal_r709b44_1
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative
/-- Equality of the lower and upper closed subgroups transports the raw
extension quotient without exposing dependent rewrites to clients. -/
def extensionQuotientMulEquivOfEq
    {G : Type u} [Group G] [TopologicalSpace G]
    {H H' J J' : ClosedSubgroup G}
    (hH : H = H') (hJ : J = J')
    (hJH : J.toSubgroup ≤ H.toSubgroup)
    (hJH' : J'.toSubgroup ≤ H'.toSubgroup)
    [(CyclicCohomology.extensionSubgroup H J hJH).Normal]
    [(CyclicCohomology.extensionSubgroup H' J' hJH').Normal] :
    (H.toSubgroup ⧸ CyclicCohomology.extensionSubgroup H J hJH) ≃*
      (H'.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H' J' hJH') := by
  cases hH
  cases hJ
  exact MulEquiv.refl _

/-- The quotient transport sends a quotient representative to the same
ambient group element, rebundled in the equal lower subgroup. -/
@[simp]
theorem extensionQuotientMulEquivOfEq_mk
    {G : Type u} [Group G] [TopologicalSpace G]
    {H H' J J' : ClosedSubgroup G}
    (hH : H = H') (hJ : J = J')
    (hJH : J.toSubgroup ≤ H.toSubgroup)
    (hJH' : J'.toSubgroup ≤ H'.toSubgroup)
    [(CyclicCohomology.extensionSubgroup H J hJH).Normal]
    [(CyclicCohomology.extensionSubgroup H' J' hJH').Normal]
    (σ : H.toSubgroup) :
    extensionQuotientMulEquivOfEq hH hJ hJH hJH'
        (QuotientGroup.mk σ) =
      QuotientGroup.mk
        ((MulEquiv.subgroupCongr
          (congrArg ClosedSubgroup.toSubgroup hH)) σ) := by
  cases hH
  cases hJ
  rfl

/-- Rebase an abelianized extension-quotient equivalence together with its
finite abstract base. -/
def abelianizedExtensionQuotientAddEquiv_transportBase
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {X : Type} [AddGroup X]
    (e : Additive (Abelianization P.extensionQuotient) ≃+ X) :
    Additive
        (Abelianization
          (Eq.mp
            (congrArg
              (fun Y : FiniteAbstractField G =>
                FiniteGaloisSubextension Y.field)
              hAB)
            P).extensionQuotient) ≃+ X := by
  cases hAB
  exact e

/-- The explicit quotient equivalence induced by rebasing a finite Galois
subextension. -/
def extensionQuotientMulEquiv_transportFiniteGalois
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {Q : FiniteGaloisSubextension B.field}
    (hPQ :
      Eq.mp
        (congrArg
          (fun Y : FiniteAbstractField G =>
            FiniteGaloisSubextension Y.field)
          hAB)
        P = Q) :
    Q.extensionQuotient ≃* P.extensionQuotient := by
  cases hAB
  cases hPQ
  exact MulEquiv.refl _

/-- Quotient rebasing sends a canonical representative to the same ambient
group element rebundled in the old base subgroup. -/
@[simp]
theorem extensionQuotientMulEquiv_transportFiniteGalois_mk
    {G : Type u} [Group G] [TopologicalSpace G]
    {A B : FiniteAbstractField G}
    (hAB : A = B)
    (P : FiniteGaloisSubextension A.field)
    {Q : FiniteGaloisSubextension B.field}
    (hPQ :
      Eq.mp
        (congrArg
          (fun Y : FiniteAbstractField G =>
            FiniteGaloisSubextension Y.field)
          hAB)
        P = Q)
    (σ : B.field.toSubgroup) :
    extensionQuotientMulEquiv_transportFiniteGalois hAB P hPQ
        (Q.extensionQuotientMk σ) =
      P.extensionQuotientMk
        ((MulEquiv.subgroupCongr
          (congrArg ClosedSubgroup.toSubgroup
            (congrArg FiniteAbstractField.field hAB).symm)) σ) := by
  cases hAB
  cases hPQ
  rfl

section AbstractFixedFieldInclusion

local instance ideleClassGroupIsMulCommutative_r709b44_2
    {F : Type} [Field F] [NumberField F]
    : IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
local instance ideleClassSubgroupNormal_r709b44_2
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative
variable
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)

local instance naturalityAbstractFixedFieldBaseQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H.field (le_baseField H.field)) :=
  H.finite

local instance naturalityAbstractFixedFieldRelativeQuotientFinite :
    Finite
      (H.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H.field P.field P.below) :=
  P.finite

noncomputable local instance
    naturalityAbstractFixedFieldFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) H.field H.finite

noncomputable local instance
    naturalityAbstractRelativeFixedFieldFiniteDimensional :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    H.field P.field P.below H.finite P.finite

local instance naturalityAbstractFixedFieldRelativeScalarTower :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance
    naturalityAbstractRelativeFixedFieldAbsoluteFiniteDimensional :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below)

noncomputable local instance naturalityAbstractFixedFieldNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) H.field)

noncomputable local instance
    naturalityAbstractRelativeFixedFieldNumberField :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below)

/-- Use the same direct fixed-field Galois witness as the intrinsic
norm-residue construction.  This prevents the dependent Galois-group type
from being synthesized through a second `IsAbelianGalois` instance path. -/
noncomputable local instance
    naturalityAbstractRelativeFixedFieldIsGalois_r709b44_1 :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    H.field P.field P.below P.normal
noncomputable local instance
    naturalityAbstractRelativeFixedFieldIsAbelianGalois :
    IsAbelianGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois P

end AbstractFixedFieldInclusion

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedLocalGlobalCompatibility
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
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

@[reducible]
noncomputable local instance
    abstractFixedFieldFiniteIdeleGroupGroup
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Group
      (FiniteIdeleGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :=
  RestrictedProduct.instGroupCoeOfSubgroupClass
    (fun v : IsDedekindDomain.HeightOneSpectrum
      (𝓞 (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)) =>
      (v.adicCompletion
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))ˣ)

@[reducible]
noncomputable local instance
    abstractFixedFieldIdeleGroupGroup
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Group
      (IdeleGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :=
  Prod.instGroup

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalNormResidueAbelianization
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
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

/-- Idèle classes are commutative.  Keeping the mixin as a named local
instance lets norm-range quotient types elaborate before entering a
declaration body. -/
local instance
    globalNormResidueAbelianization_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The abelianization of the compatible abstract extension quotient is the
abelianization of the actual Galois group. -/
noncomputable def
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization :
    Additive
        (Abelianization
          (ClassFormation.FiniteGaloisSubextension.extensionQuotient
            (numberFieldTowerFiniteGaloisSubextension K L))) ≃+
      Additive (Abelianization (Gal(L / K))) :=
  MulEquiv.toAdditive
    (MulEquiv.abelianizationCongr
      (numberFieldTowerExtensionQuotientEquivGaloisGroup K L))

end Reciprocity
end GlobalClassFieldTheory
end
end


