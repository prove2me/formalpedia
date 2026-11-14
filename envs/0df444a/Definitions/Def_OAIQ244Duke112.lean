-- Prove2me | Definitions.Def_OAIQ244Duke112
-- name    : OAIQ244Duke112
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T04:43:54.099199+00:00
-- url     : https://prove2.me/theorems/16061814-3ada-49c3-963f-2fbb635c8044
-- title:
--   Definitions bundle OAIQ244Duke112 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 8 definitions, 2 instances and 20 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionRebasedAutomorphismApplyVal`, `GlobalClassFieldTheory.Reciprocity.exists_finitePlacePrimaryNormDescent_localGlobalRepresentative`, `GlobalClassFieldTheory.Reciprocity.exists_finitePlacePrimary_cyclicFixedFieldRepresentative`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryAbstractField`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryLocalGlobalRepresentative`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryTopDecompositionGroup_eq_chosen`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicCyclicGaloisSubextension`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedLocalGlobalCompatibility`, `GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_Factorization`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicAuxiliaryField`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke110` and `OAIQ244Duke111` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.DukePrimeDegree.idealCharacter_kernelLaw_of_even_modulus`.
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
import Definitions.Def_OAIQ244Duke110
import Definitions.Def_OAIQ244Duke111

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topRatScalarTower _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal
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

attribute [local instance] naturalityIdeleClassCommGroup

section AbstractFixedFieldInclusion

local instance ideleClassGroupIsMulCommutative_ra15d4d_1
    {F : Type} [Field F] [NumberField F]
    : IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
local instance ideleClassSubgroupNormal_ra15d4d_1
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative
variable
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)

attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractFixedFieldBaseQuotientFinite
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractFixedFieldRelativeQuotientFinite
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractFixedFieldFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractRelativeFixedFieldFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractFixedFieldRelativeScalarTower
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractRelativeFixedFieldAbsoluteFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractFixedFieldNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractRelativeFixedFieldNumberField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractRelativeFixedFieldIsGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.naturalityAbstractRelativeFixedFieldIsAbelianGalois
/-- Ambient action of the representative after rebundling it in the embedded
base subgroup. -/
noncomputable def
    abstractFixedFieldInclusionRebasedAutomorphismApplyVal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) : SeparableClosure ℚ := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  let σEmbedded :
      (numberFieldEmbeddedBaseSubgroup F E j).toSubgroup :=
    (MulEquiv.subgroupCongr
      (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ
  exact σEmbedded.1.1 (x : SeparableClosure ℚ)

/-- The embedded quotient endpoint sends a canonical representative to the
packaged ambient value above. -/
theorem
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue_mk
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup) :
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) =
      abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue H P σ := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  have hTop :
      numberFieldEmbeddedTopSubgroup F E j = P.field :=
    numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion H P
  let hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  let hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  simp only [
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue,
    abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv,
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue,
    MulEquiv.trans_apply,
    FiniteGaloisSubextension.extensionQuotientMk_apply]
  exact congrArg
    (ambientEmbeddedExtensionQuotientEquivGaloisGroup ℚ F E j eSep)
    (extensionQuotientMulEquivOfEq_mk
      hBase.symm hTop.symm P.below
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j) σ)

/-- The packaged ambient endpoint evaluates to the action of the rebundled
representative. -/
theorem
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal_eq_rebased
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal H P σ x =
      abstractFixedFieldInclusionRebasedAutomorphismApplyVal H P σ x := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  let hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  let hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  let σEmbedded :
      (numberFieldEmbeddedBaseSubgroup F E j).toSubgroup :=
    (MulEquiv.subgroupCongr
      (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ
  have hmk :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
      ℚ F E j eSep σEmbedded x
  change
    (ambientEmbeddedExtensionQuotientEquivGaloisGroup
        ℚ F E j eSep (QuotientGroup.mk σEmbedded) x :
        SeparableClosure ℚ) =
      σEmbedded.1.1 (x : SeparableClosure ℚ) at hmk
  simpa only [
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal,
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue,
    abstractFixedFieldInclusionRebasedAutomorphismApplyVal] using hmk

/-- Rebundling the representative does not change its action in the ambient
separable closure. -/
theorem
    abstractFixedFieldInclusionRebasedAutomorphismApplyVal_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionRebasedAutomorphismApplyVal H P σ x =
      σ.1.1 (x : SeparableClosure ℚ) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  let σEmbedded :
      (numberFieldEmbeddedBaseSubgroup F E j).toSubgroup :=
    (MulEquiv.subgroupCongr
      (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ
  have hσEmbedded :
      (σEmbedded.1 : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) = σ.1 :=
    closedSubgroupCongr_apply_val hBase.symm σ
  change σEmbedded.1.1 (x : SeparableClosure ℚ) = _
  rw [hσEmbedded]

/-- The packaged ambient representative acts by the original automorphism on
the underlying separable-closure value. -/
theorem
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal H P σ x =
      σ.1.1 (x : SeparableClosure ℚ) := by
  exact
    (abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal_eq_rebased
      H P σ x).trans
      (abstractFixedFieldInclusionRebasedAutomorphismApplyVal_eq H P σ x)

/-- Evaluation of the embedded quotient endpoint on a canonical quotient
representative, stated only in the ambient separable closure. -/
theorem
    abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv_mk_val
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionEmbeddedExtensionQuotientApplyVal H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) x =
      σ.1.1 (x : SeparableClosure ℚ) := by
  calc
    _ = abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal
        H P σ x := by
      exact congrArg
        (fun g => (g x : SeparableClosure ℚ))
        (abstractFixedFieldInclusionEmbeddedExtensionQuotientValue_mk
          H P σ)
    _ = _ :=
      abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue_apply
        H P σ x

/-- The embedded and canonical quotient endpoints agree on each quotient
class.  This pointwise boundary is intentionally weaker than equality of the
dependent `MulEquiv` structures. -/
theorem
    abstractFixedFieldInclusionExtensionQuotientEquiv_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q =
      abstractFixedFieldInclusionCanonicalExtensionQuotientValue H P q := by
  refine P.toFiniteGaloisExtension.extensionQuotient_inductionOn
    (motive := fun q =>
      abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q =
        abstractFixedFieldInclusionCanonicalExtensionQuotientValue H P q)
    q ?_
  intro σ
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact
    (abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv_mk_val
      H P σ x).trans
      (abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv_mk_val
        H P σ x).symm

/-- Transporting a canonical representative of the embedded finite Galois
package preserves its Galois value. -/
theorem
    abstractFixedFieldInclusionTransportedExtensionQuotientValue_mk
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup) :
    abstractFixedFieldInclusionTransportedExtensionQuotientValue H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) =
      abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  have hTop :
      numberFieldEmbeddedTopSubgroup F E j = P.field :=
    numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion H P
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  let PEmbedded : FiniteGaloisSubextension HEmbedded.field :=
    numberFieldEmbeddedFiniteGaloisSubextension F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  have hPEmbedded :
      Eq.mp
          (congrArg
            (fun X : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension X.field)
            hHEmbedded)
          PEmbedded =
        P.toFiniteGaloisExtension :=
    numberFieldEmbeddedFiniteGaloisSubextension_transport_eq H P
  let hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  let hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  have hFieldEq :
      (congrArg FiniteAbstractField.field hHEmbedded).symm = hBase.symm :=
    Subsingleton.elim _ _
  simp only [
    abstractFixedFieldInclusionTransportedExtensionQuotientValue,
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue,
    abstractFixedFieldInclusionTransportedExtensionQuotientEquiv,
    abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv,
    MulEquiv.trans_apply,
    extensionQuotientMulEquiv_transportFiniteGalois_mk,
    FiniteGaloisSubextension.extensionQuotientMk_apply,
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup]
  rw [hFieldEq]
  change
    ambientEmbeddedExtensionQuotientEquivGaloisGroup ℚ F E j eSep
        (QuotientGroup.mk
          ((MulEquiv.subgroupCongr
            (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ)) = _
  exact
    (congrArg
      (ambientEmbeddedExtensionQuotientEquivGaloisGroup ℚ F E j eSep)
      (extensionQuotientMulEquivOfEq_mk
        hBase.symm hTop.symm P.below
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j) σ)).symm

/-- Transporting the embedded finite Galois package preserves the value of
its extension-quotient comparison. -/
theorem
    abstractFixedFieldInclusionTransportedExtensionQuotientEquiv_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    abstractFixedFieldInclusionTransportedExtensionQuotientValue H P q =
      abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q := by
  refine P.toFiniteGaloisExtension.extensionQuotient_inductionOn
    (motive := fun q =>
      abstractFixedFieldInclusionTransportedExtensionQuotientValue H P q =
        abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q)
    q ?_
  intro σ
  exact abstractFixedFieldInclusionTransportedExtensionQuotientValue_mk
    H P σ

/-- On an abelianization representative, the transported canonical endpoint
is the additive value of the transported quotient endpoint. -/
theorem
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue_of
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue H P
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul
        (abstractFixedFieldInclusionTransportedExtensionQuotientValue
          H P q) := by
  simpa only [
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue,
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv,
    abstractFixedFieldInclusionTransportedExtensionQuotientValue] using
    (abelianizationCongrToComm_apply
      (abstractFixedFieldInclusionTransportedExtensionQuotientEquiv H P) q)

/-- The canonical abelianization comparison built after transport agrees
pointwise with the intrinsic abstract fixed-field comparison. -/
theorem
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue H P z =
      abstractFixedFieldInclusionCanonicalAbelianizedValue H P z := by
  let q : P.toFiniteGaloisExtension.extensionQuotient :=
    Quotient.out z.toMul
  have hz : Additive.ofMul (Abelianization.of q) = z := by
    apply Additive.ext
    exact Quotient.out_eq' z.toMul
  rw [← hz]
  calc
    _ = Additive.ofMul
        (abstractFixedFieldInclusionTransportedExtensionQuotientValue
          H P q) :=
      abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue_of
        H P q
    _ = Additive.ofMul
        (abstractFixedFieldInclusionEmbeddedExtensionQuotientValue
          H P q) :=
      congrArg Additive.ofMul
        (abstractFixedFieldInclusionTransportedExtensionQuotientEquiv_apply
          H P q)
    _ = Additive.ofMul
        (abstractFixedFieldInclusionCanonicalExtensionQuotientValue
          H P q) :=
      congrArg Additive.ofMul
        (abstractFixedFieldInclusionExtensionQuotientEquiv_apply H P q)
    _ = _ :=
      (abstractFixedFieldInclusionCanonicalAbelianizedValue_of H P q).symm

/-- The transported abelianized equivalence agrees pointwise with the
intrinsic abstract fixed-field Galois comparison. -/
theorem
    abstractFixedFieldInclusionTransportedAbelianizedValue_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    abstractFixedFieldInclusionTransportedAbelianizedValue H P z =
      abstractFixedFieldInclusionCanonicalAbelianizedValue H P z :=
  (abstractFixedFieldInclusionTransportedAbelianizedValue_eq_canonical
    H P z).trans
    (abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue_eq
      H P z)

/-- The transported packaged value is the intrinsic canonical packaged value;
only the idele input and the eventual abelianized value are compared. -/
theorem
    abstractFixedFieldInclusionTransportedNormResidueValue_eq_canonical
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    abstractFixedFieldInclusionTransportedNormResidueValue H P c =
      abstractFixedFieldInclusionCanonicalNormResidueValue H P c := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  let eIdeleEmbedded :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j
  let eIdeleOverH :
      Additive (IdeleClassGroup F) ≃+
        ambientFixedAddSubgroup rationalIdeleClassRepresentation H.field :=
    Eq.mp
      (congrArg
        (fun X : FiniteAbstractField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
          Additive (IdeleClassGroup F) ≃+
            ambientFixedAddSubgroup
              rationalIdeleClassRepresentation X.field)
        hHEmbedded)
      eIdeleEmbedded
  simpa only [
    abstractFixedFieldInclusionTransportedNormResidueValue,
    abstractFixedFieldInclusionCanonicalNormResidueValue,
    eIdeleEmbedded,
    eIdeleOverH] using
    (rationalFiniteNormResidueValue_congr_apply
      H P.toFiniteGaloisExtension
      eIdeleOverH
      (rationalAbstractFixedFieldIdeleClassEquivFixed H.field)
      (abstractFixedFieldInclusionTransportedAbelianizedEquiv H P)
      (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P)
      c
      (numberFieldEmbeddedIdeleClassEquivAmbientFixed_transport_apply H P c)
      (fun z => abstractFixedFieldInclusionTransportedAbelianizedValue_eq
        H P z))

/-- The explicitly embedded and intrinsic packaged norm-residue values agree. -/
theorem
    abstractFixedFieldInclusionEmbeddedNormResidueValue_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    abstractFixedFieldInclusionEmbeddedNormResidueValue H P c =
      abstractFixedFieldInclusionCanonicalNormResidueValue H P c :=
  (abstractFixedFieldInclusionEmbeddedNormResidueValue_eq_transported
    H P c).trans
    (abstractFixedFieldInclusionTransportedNormResidueValue_eq_canonical
      H P c)

/-- For the literal fixed fields attached to an abstract finite abelian
extension, the norm-residue map obtained from their canonical inclusion in
the rational separable closure is the intrinsic fixed-field norm-residue
map. -/
theorem
    globalNormResidueMonoidHomOfEmbedding_abstractFixedFieldInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    globalNormResidueMonoidHomOfEmbedding F E j =
      abstractFixedFieldGlobalNormResidueMonoidHom H P := by
  dsimp only
  apply MonoidHom.ext
  intro c
  rw [globalNormResidueMonoidHomOfEmbedding_apply]
  change
    Additive.toMul
        (abstractFixedFieldInclusionEmbeddedNormResidueValue
          H P (Additive.ofMul c)) =
      abstractFixedFieldGlobalNormResidueMonoidHom H P c
  calc
    _ = Additive.toMul
        (abstractFixedFieldInclusionCanonicalNormResidueValue
          H P (Additive.ofMul c)) :=
      congrArg Additive.toMul
        (abstractFixedFieldInclusionEmbeddedNormResidueValue_eq
          H P (Additive.ofMul c))
    _ = _ := by
      simpa only [abstractFixedFieldInclusionCanonicalNormResidueValue] using
        (rationalFiniteNormResidueValue_abstractFixedField_apply
          (H := H) (P := P) c)

end AbstractFixedFieldInclusion

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedLocalGlobalCompatibility
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topRatScalarTower _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
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

attribute [local instance] GlobalClassFieldTheory.Reciprocity.abstractFixedFieldFiniteIdeleGroupGroup
attribute [local instance] GlobalClassFieldTheory.Reciprocity.abstractFixedFieldIdeleGroupGroup
attribute [local instance] GlobalClassFieldTheory.Reciprocity.abstractFixedFieldIdeleClassGroupGroup
/-- The canonical inclusion realization of a finite unramified abstract
fixed-field extension satisfies finite-place local--global compatibility. -/
theorem
    globalNormResidueMonoidHomOfEmbedding_comp_finitePlaceIdeleClass_of_abstractFixedFieldUnramified
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension H.field)
    (hUnramified :
      L.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData)
    (v : IsDedekindDomain.HeightOneSpectrum
      (𝓞 (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field))) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    let E :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    (globalNormResidueMonoidHomOfEmbedding F E j).comp
        (IdeleGroup.finitePlaceIdeleClass v) =
      chosenFinitePlaceArtinMonoidHom
        (K := F) (L := E) v := by
  dsimp only
  rw [
    globalNormResidueMonoidHomOfEmbedding_abstractFixedFieldInclusion
      H L]
  exact
    abstractFixedFieldGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass
      H L hUnramified v

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topAlgebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliary_topRatScalarTower _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.completedMaximalOrderCompactSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal
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
# Finite p-adic cyclic data for local-global Artin compatibility

This module packages the simultaneous finite-quotient and cyclotomic
coordinates and the corresponding abstract auxiliary subextension.
-/

open scoped IsMulCommutative NumberField
open NumberField
open IdeleGroup RelativeIdeleGroup
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology
open KummerTheory ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_7
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionNormal
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePadicTowerExtensionQuotientFinite
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldTowerExtensionQuotientIsMulCommutative
attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldTowerBaseSubgroupCompactSpace
/-- The auxiliary cyclic fixed subgroup as a genuine finite Galois
subextension of the compatible abstract field attached to `K`. -/
noncomputable def
    numberFieldTowerFinitePadicCyclicGaloisSubextension
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    FiniteGaloisSubextension
      (numberFieldTowerBaseSubgroup K L) where
  field :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  below :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
      (K := K) (L := L) p τ
  normal :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup_extension_normal
      (K := K) (L := L) p τ
  finite := by
    rw [
      numberFieldTowerFinitePadicCyclicFixedSubgroup_extensionSubgroup
        (K := K) (L := L) p τ]
    exact
      Subgroup.quotient_finite_of_isOpen
        (numberFieldTowerFinitePadicCyclicPreimage
          (K := K) (L := L) p τ).toSubgroup
        (numberFieldTowerFinitePadicCyclicPreimage_isOpen
          (K := K) (L := L) p τ hτ)

/-- The auxiliary fixed subgroup, with its absolute finite-index
witness, as the finite abstract field used by fixed-field global
reciprocity. -/
noncomputable def numberFieldTowerFinitePadicAuxiliaryAbstractField
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ((numberFieldTowerFinitePadicCyclicGaloisSubextension
      (K := K) (L := L) p τ hτ).toFiniteAbstractFieldExtension
    (K := numberFieldTowerFiniteAbstractField K L)).field

/-- The auxiliary compositum is unramified for the genuine
cyclotomic degree datum.  The proof is the key `p`-primary
intersection: full cyclotomic inertia lies in every `p`-adic
cyclotomic kernel, and the latter intersection already fixes `L`. -/
theorem
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension_isUnramified
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimary :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ).toFiniteGaloisExtension.IsUnramified
      rationalCyclotomicDegreeData := by
  let : Algebra ℚ rationalCyclotomicZHatField :=
    rationalCyclotomicZHatField.algebra'
  let : @Normal ℚ rationalCyclotomicZHatField _ _
      rationalCyclotomicZHatField.algebra' :=
    rationalCyclotomicZHatField_normal
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let T :=
    numberFieldTowerTopSubgroup L
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  apply
    (P.toFiniteGaloisExtension.isUnramified_iff_inertia_le
      rationalCyclotomicDegreeData).2
  intro σ hσ
  change σ ∈ S.toSubgroup ⊓ T.toSubgroup
  refine ⟨hσ.1, ?_⟩
  apply
    numberFieldTowerFinitePadicCyclicFixedSubgroup_inf_absolutePadicKernel_le_topSubgroup
      (K := K) (L := L) p τ n hn hdegree hprimary
  refine ⟨hσ.1, ?_⟩
  change
    rationalSeparableClosurePadicCyclotomicDegree p σ =
      1
  have hdegreeOne :
      rationalCyclotomicZHatFieldGalEquivZHat
          (AlgEquiv.restrictNormalHom
            rationalCyclotomicZHatField σ) =
        1 := by
    exact hσ.2
  apply Multiplicative.toAdd.injective
  change
    zHatToPadicInt p
        (Multiplicative.toAdd
          (rationalCyclotomicZHatFieldGalEquivZHat
            (AlgEquiv.restrictNormalHom
              rationalCyclotomicZHatField σ))) =
      (0 : ℤ_[p.1])
  have hdegreeAdd :=
    congrArg Multiplicative.toAdd hdegreeOne
  change
    Multiplicative.toAdd
        (rationalCyclotomicZHatFieldGalEquivZHat
          (AlgEquiv.restrictNormalHom
            rationalCyclotomicZHatField σ)) =
      0 at hdegreeAdd
  rw [hdegreeAdd]
  exact map_zero (zHatToPadicInt p)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicAuxiliaryField
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional_over_extension _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
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
# The finite p-adic auxiliary field

This module realizes the simultaneous finite/cyclotomic lift as an actual
number field and proves the subgroup and intermediate-field identities
needed by the auxiliary-field argument.
-/

open scoped IsMulCommutative NumberField
open AlgebraicNumberTheory IsDedekindDomain NumberField
open IdeleGroup RelativeIdeleGroup
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology
open KummerTheory ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open GlobalClassFields

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance]
  rationalSeparableClosureAlgebra

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_8
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePadicAuxiliaryExtensionNormal
local instance finitePadicAuxiliaryExtensionQuotientFinite_ra15d4d_1 :
    Finite
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  numberFieldTowerExtensionQuotient_finite K L
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePadicAuxiliaryExtensionQuotientIsMulCommutative
instance
    numberFieldTowerFinitePadicAuxiliary_baseRatScalarTower
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsScalarTower ℚ K
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) := by
  exact
    IsScalarTower.of_algebraMap_eq'
      (numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
        (K := K) (L := L) p τ).comp_algebraMap.symm

instance
    numberFieldTowerFinitePadicAuxiliary_baseTopScalarTower
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsScalarTower K
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ))
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  apply Subtype.ext
  exact
    numberFieldTowerFinitePadicAuxiliaryEmbedding_algebraMap
      (K := K) (L := L) p τ x

/-- The genuine auxiliary fixed field is Galois over the original
base field through the compatible embedding above. -/
theorem numberFieldTowerFinitePadicAuxiliaryBase_isGalois
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsGalois K
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let hSH :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
      (K := K) (L := L) p τ
  let B :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let FB :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hSH
  let auxiliaryBaseAlgebra : Algebra B FB :=
    (LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hSH).algebra
  let auxiliaryBaseGalois : IsGalois B FB :=
    LocalClassFieldTheory.abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) H S hSH
      (numberFieldTowerFinitePadicCyclicFixedSubgroup_extension_normal
        (K := K) (L := L) p τ)
  let eK :=
    numberFieldTowerAbstractBaseFieldEquiv K L
  refine
    @IsGalois.of_equiv_equiv
      B FB _ _ auxiliaryBaseAlgebra
      K F _ _
      (numberFieldTowerFinitePadicAuxiliary_baseAlgebra
        (K := K) (L := L) p τ)
      auxiliaryBaseGalois
      eK.symm.toRingEquiv (RingEquiv.refl F) ?_
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change
    ((eK (eK.symm x) : B) : SeparableClosure ℚ) =
      (x : SeparableClosure ℚ)
  exact
    congrArg Subtype.val (eK.apply_symm_apply x)

/-- Restricting the auxiliary automorphism through the actual
base-change square recovers the finite quotient coordinate of the
distinguished lift. -/
theorem numberFieldTowerFinitePadicAuxiliaryAutomorphism_restriction
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (numberFieldTowerFinitePadicAuxiliaryAutomorphism
          (K := K) (L := L) p τ) =
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
        (numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ) := by
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ).below
  let σE :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
  apply AlgEquiv.ext
  intro x
  apply (numberFieldSeparableClosureEmbedding L).injective
  calc
    numberFieldSeparableClosureEmbedding L
        (((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σE x) =
      ((σE (algebraMap L E x) : E) :
        SeparableClosure ℚ) := by
          exact congrArg Subtype.val
            (AlgEquiv.restrictNormal_commutes
              ((AlgEquiv.restrictScalarsHom K) σE) L x)
    _ = τ.1 (numberFieldSeparableClosureEmbedding L x) := by
      rw [
        numberFieldTowerFinitePadicAuxiliaryAutomorphism_apply_val
          (K := K) (L := L) p τ]
      rfl
    _ =
      numberFieldSeparableClosureEmbedding L
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) x) := by
      exact
        (numberFieldTowerExtensionQuotientEquivGaloisGroup_mk_apply
          (K := K) (L := L) τ x).symm

/-- Restriction of the chosen separable-closure place to the genuine
auxiliary base field.  This is an exact extension of the original
finite place of `K`, not merely an equivalent valuation. -/
noncomputable def
    numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ)
  let wΩ :=
    numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v (chosenFinitePlaceExtension (L := L) v)
  refine
    ⟨wΩ.1.comp (f := F.val.toRingHom) F.val.injective, ?_⟩
  intro x
  change
    wΩ.1 (numberFieldTowerLowerEmbedding K L x) =
      NumberField.HeightOneSpectrum.adicAbv K v x
  exact wΩ.2 x

/-- The centre of the restricted place on the auxiliary compositum
lies above the centre of the same place on the auxiliary base field. -/
theorem
    numberFieldTowerFinitePadicAuxiliaryTopPlace_below
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    let S :=
      numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ
    let P :=
      numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) S
    let E :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    letI hHfinite : Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            S (le_baseField S)) :=
      (numberFieldTowerFinitePadicAuxiliaryAbstractField
        (K := K) (L := L) p τ hτ).finite
    letI hPfinite : Finite
        (S.toSubgroup ⧸
          extensionSubgroup S P.field P.below) :=
      P.finite
    letI _ : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) S hHfinite
    letI _ : FiniteDimensional F E :=
      LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ)
        S P.field P.below hHfinite hPfinite
    letI _ : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI _ : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI _ : NumberField F :=
      NumberField.of_module_finite ℚ F
    letI _ : NumberField E :=
      NumberField.of_module_finite ℚ E
    letI _ : Algebra K F :=
      numberFieldTowerFinitePadicAuxiliary_baseAlgebra
        (K := K) (L := L) p τ
    finitePlaceBelow (K := F)
        (finitePlaceExtensionCentre
          (K := K) (L := E) v
          (numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
            (K := K) (L := L) v p τ)) =
      finitePlaceExtensionCentre
        (K := K) (L := F) v
        (numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
          (K := K) (L := L) v p τ) := by
  dsimp only
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let hHfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          S (le_baseField S)) :=
    (numberFieldTowerFinitePadicAuxiliaryAbstractField
      (K := K) (L := L) p τ hτ).finite
  let hPfinite : Finite
      (S.toSubgroup ⧸
        extensionSubgroup S P.field P.below) :=
    P.finite
  let auxiliaryBaseFiniteDimensional : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) S hHfinite
  let auxiliaryTopFiniteDimensional : FiniteDimensional F E :=
    LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ)
      S P.field P.below hHfinite hPfinite
  let auxiliaryScalarTower : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let auxiliaryAbsoluteFiniteDimensional : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let auxiliaryBaseNumberField : NumberField F :=
    NumberField.of_module_finite ℚ F
  let auxiliaryTopNumberField : NumberField E :=
    NumberField.of_module_finite ℚ E
  let auxiliaryOriginalBaseAlgebra : Algebra K F :=
    numberFieldTowerFinitePadicAuxiliary_baseAlgebra
      (K := K) (L := L) p τ
  let wF :=
    numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
      (K := K) (L := L) v p τ
  let wE :=
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
  apply HeightOneSpectrum.ext
  ext x
  change
    algebraMap (𝓞 F) (𝓞 E) x ∈
        finitePlaceExtensionCentreIdeal
          (K := K) (L := E) v wE ↔
      x ∈
        finitePlaceExtensionCentreIdeal
          (K := K) (L := F) v wF
  rw [
    mem_finitePlaceExtensionCentreIdeal_iff,
    mem_finitePlaceExtensionCentreIdeal_iff]
  rfl

/-- The restricted top-field place and the chosen extension above its centre
have the same decomposition group. -/
opaque numberFieldTowerFinitePadicAuxiliaryTopDecompositionGroup_eq_chosen
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠ 1) :
    let S := numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
    let P := numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
    let F := LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
    let E := LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
    letI hHfinite : Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            S (le_baseField S)) :=
      (numberFieldTowerFinitePadicAuxiliaryAbstractField
        (K := K) (L := L) p τ hτ).finite
    letI hPfinite : Finite
        (S.toSubgroup ⧸ extensionSubgroup S P.field P.below) := P.finite
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) S hHfinite
    letI : FiniteDimensional F E :=
      LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) S P.field P.below hHfinite hPfinite
    letI : IsScalarTower ℚ F E := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    letI : IsAbelianGalois F E :=
      GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois P
    letI : Algebra K F :=
      numberFieldTowerFinitePadicAuxiliary_baseAlgebra
        (K := K) (L := L) p τ
    let wF := numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
      (K := K) (L := L) v p τ
    let wE := numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
    let V := finitePlaceExtensionCentre (K := K) (L := F) v wF
    absoluteValueDecompositionGroup F wE.1 =
      absoluteValueDecompositionGroup F
        (chosenFinitePlaceExtension (L := E) V).1 := by
  dsimp only
  let H :=
    numberFieldTowerFinitePadicAuxiliaryAbstractField
      (K := K) (L := L) p τ hτ
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let hHfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          S (le_baseField S)) :=
    H.finite
  let hPfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S P.field P.below) :=
    P.finite
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) S hHfinite
  let : FiniteDimensional F E :=
    LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) S P.field P.below hHfinite hPfinite
  let : IsScalarTower ℚ F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  let : NumberField F := NumberField.of_module_finite ℚ F
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : IsAbelianGalois F E :=
    GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois P
  let : Algebra K F :=
    numberFieldTowerFinitePadicAuxiliary_baseAlgebra
      (K := K) (L := L) p τ
  let wF :=
    numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
      (K := K) (L := L) v p τ
  let wE :=
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
  let V := finitePlaceExtensionCentre (K := K) (L := F) v wF
  let W := finitePlaceExtensionCentre (K := K) (L := E) v wE
  let Wover :
      {W' : HeightOneSpectrum (𝓞 E) //
        finitePlaceBelow (K := F) W' = V} :=
    ⟨W,
      numberFieldTowerFinitePadicAuxiliaryTopPlace_below
        (K := K) (L := L) v p τ hτ⟩
  let wFE :
      AbsoluteValueExtension
        (NumberField.HeightOneSpectrum.adicAbv F V) E :=
    (finitePlaceExtensionEquivAbove
      (K := F) (L := E) V).symm Wover
  have hwFEcentre :
      finitePlaceExtensionCentre
          (K := F) (L := E) V wFE =
        W := by
    exact
      congrArg Subtype.val
        ((finitePlaceExtensionEquivAbove
          (K := F) (L := E) V).apply_symm_apply Wover)
  have hwEquiv : wE.1.IsEquiv wFE.1 := by
    apply
      finitePlaceExtensions_isEquiv_of_centres_eq
        (F := K) (M := F) v V wE wFE
    exact hwFEcentre.symm
  calc
    absoluteValueDecompositionGroup F wE.1 =
        absoluteValueDecompositionGroup F wFE.1 :=
      absoluteValueDecompositionGroup_eq_of_absoluteValue_isEquiv
        (F := F) wE.1 wFE.1 hwEquiv
    _ =
      absoluteValueDecompositionGroup F
          (chosenFinitePlaceExtension (L := E) V).1 :=
      absoluteValueDecompositionGroup_eq_of_exactExtensions_of_isMulCommutative
        (F := F)
        (NumberField.HeightOneSpectrum.adicAbv F V)
        (RayClass.adicAbv_isNontrivial V)
        wFE
        (chosenFinitePlaceExtension (L := E) V)



/-- The auxiliary-field construction produces a lower local unit
whose chosen local Artin value and global norm-residue value are both
the finite quotient coordinate of the distinguished lift. -/
opaque numberFieldTowerFinitePadicAuxiliaryLocalGlobalRepresentative
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠ 1)
    (hdecomposition :
      letI : Algebra K (SeparableClosure ℚ) :=
        numberFieldTowerSeparableClosureBaseAlgebra K L
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v (chosenFinitePlaceExtension (L := L) v)).1)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimaryQuotient :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    {z : (v.adicCompletion K)ˣ //
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v z =
          numberFieldTowerExtensionQuotientEquivGaloisGroup K L
            (numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ) ∧
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) =
          numberFieldTowerExtensionQuotientEquivGaloisGroup K L
            (numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ)} := by
  let H :=
    numberFieldTowerFinitePadicAuxiliaryAbstractField
      (K := K) (L := L) p τ hτ
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  letI hHfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          S (le_baseField S)) :=
    H.finite
  letI hPfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S P.field P.below) :=
    P.finite
  letI auxiliaryBaseNumberField : NumberField F := by
    let : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) S hHfinite
    exact NumberField.of_module_finite ℚ F
  letI auxiliaryTopNumberField : NumberField E := by
    let : FiniteDimensional F E :=
      LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ)
        S P.field P.below hHfinite hPfinite
    exact NumberField.of_module_finite F E
  letI auxiliaryAbelianGalois : IsAbelianGalois F E :=
    GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois P
  letI auxiliaryOriginalBaseAlgebra : Algebra K F :=
    numberFieldTowerFinitePadicAuxiliary_baseAlgebra
      (K := K) (L := L) p τ
  letI auxiliaryOriginalTopAlgebra : Algebra L E :=
    numberFieldTowerFinitePadicAuxiliary_topAlgebra
      (K := K) (L := L) p τ
  letI auxiliaryOriginalBaseTopAlgebra : Algebra K E :=
    numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra
      (K := K) (L := L) p τ
  letI auxiliaryOriginalTopScalarTower : IsScalarTower K L E :=
    numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower
      (K := K) (L := L) p τ
  letI auxiliaryBaseTopScalarTower : IsScalarTower K F E :=
    numberFieldTowerFinitePadicAuxiliary_baseTopScalarTower
      (K := K) (L := L) p τ
  letI auxiliaryOriginalBaseGalois : IsGalois K F :=
    numberFieldTowerFinitePadicAuxiliaryBase_isGalois
      (K := K) (L := L) p τ
  let auxiliaryOriginalTopAlgHom : L →ₐ[ℚ] E :=
    numberFieldTowerFinitePadicAuxiliaryTopEmbedding
      (K := K) (L := L) p τ
  let wF :=
    numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
      (K := K) (L := L) v p τ
  let wE :=
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
  let V :=
    finitePlaceExtensionCentre
      (K := K) (L := F) v wF
  have hVbelow : finitePlaceBelow (K := K) V = v :=
    finitePlaceBelow_finitePlaceExtensionCentre
      (K := K) (L := F) v wF
  let Vover :
      {V' : HeightOneSpectrum (𝓞 F) //
        finitePlaceBelow (K := K) V' = v} :=
    ⟨V, hVbelow⟩
  letI auxiliaryCompletionAlgebra :
      Algebra (v.adicCompletion K) (V.adicCompletion F) :=
    (finitePlaceAdicCompletionMap K F v Vover).toAlgebra
  let σE : Gal(E / F) :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
  have hσtop :
      σE ∈ absoluteValueDecompositionGroup F wE.1 :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism_mem_topPlaceDecomposition
      (K := K) (L := L) v p τ hdecomposition
  have hgroup :=
    numberFieldTowerFinitePadicAuxiliaryTopDecompositionGroup_eq_chosen
      (K := K) (L := L) v p τ hτ
  have hσchosen :
      σE ∈ absoluteValueDecompositionGroup F
        (chosenFinitePlaceExtension (L := E) V).1 := by
    rw [← hgroup]
    exact hσtop
  have hRange :
      σE ∈ (chosenFinitePlaceArtinMonoidHom
        (K := F) (L := E) V).range := by
    rw [chosenFinitePlaceArtinMonoidHom_range (K := F) (L := E) V]
    exact hσchosen
  let y : (V.adicCompletion F)ˣ := Classical.choose hRange
  have hy :
      chosenFinitePlaceArtinMonoidHom (K := F) (L := E) V y =
        numberFieldTowerFinitePadicAuxiliaryAutomorphism
          (K := K) (L := L) p τ :=
    Classical.choose_spec hRange
  let z : (v.adicCompletion K)ˣ :=
    LocalFieldTheory.normUnits
      (v.adicCompletion K) (V.adicCompletion F) y
  have hz :
      z = LocalFieldTheory.normUnits
        (v.adicCompletion K) (V.adicCompletion F) y := by
    rfl
  let σK : Gal(L / K) :=
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
      (numberFieldTowerFiniteQuotientCoordinate
        (K := K) (L := L) τ)
  let restriction : Gal(E / F) →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  have hrestrict : restriction σE = σK :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism_restriction
      (K := K) (L := L) p τ
  have hlocal :
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v z =
        σK := by
    rw [hz]
    have hnat :=
      DFunLike.congr_fun
        (chosenFinitePlaceArtinMonoidHom_norm_restriction_of_below_eq
          (K := K) (L := L) (K' := F) (L' := E)
          v V hVbelow) y
    calc
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (V.adicCompletion F) y) =
        restriction
          (chosenFinitePlaceArtinMonoidHom (K := F) (L := E) V y) := by
            simpa only [
              MonoidHom.coe_comp, Function.comp_apply, restriction]
              using hnat.symm
      _ = restriction σE := congrArg restriction hy
      _ = σK := hrestrict
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hjLower :
      j.comp auxiliaryOriginalTopAlgHom =
        AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L := by
    apply AlgHom.ext
    intro a
    exact
      numberFieldTowerFinitePadicAuxiliaryTopEmbedding_coe
        (K := K) (L := L) p τ a
  have hPUnramified :
      P.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension_isUnramified
      (K := K) (L := L) p τ n hn hdegree hprimaryQuotient
  have hcompat :
      (globalNormResidueMonoidHomOfEmbedding F E j).comp
          (IdeleGroup.finitePlaceIdeleClass V) =
        chosenFinitePlaceArtinMonoidHom (K := F) (L := E) V :=
    globalNormResidueMonoidHomOfEmbedding_comp_finitePlaceIdeleClass_of_abstractFixedFieldUnramified
      H P hPUnramified V
  have hupper :
      globalNormResidueMonoidHomOfEmbedding F E j
          (IdeleGroup.finitePlaceIdeleClass V y) =
        σE :=
    (congrArg
      (fun φ : (V.adicCompletion F)ˣ →* Gal(E / F) => φ y)
      hcompat).trans hy
  have hnormClass :
      _root_.ideleClassNorm K F
          (IdeleGroup.finitePlaceIdeleClass V y) =
        IdeleGroup.finitePlaceIdeleClass v z := by
    rw [hz]
    simpa only [Vover] using
      (IdeleGroup.ideleClassNorm_finitePlaceIdeleClass_eq_normUnits
        (K := K) (L := F) v Vover y)
  have hglobal :
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) =
        σK := by
    calc
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) =
          globalNormResidueMonoidHom K L
            (_root_.ideleClassNorm K F
              (IdeleGroup.finitePlaceIdeleClass V y)) :=
        congrArg (globalNormResidueMonoidHom K L) hnormClass.symm
      _ = globalNormResidueMonoidHomOfEmbedding K L
          (j.comp auxiliaryOriginalTopAlgHom)
          (_root_.ideleClassNorm K F
            (IdeleGroup.finitePlaceIdeleClass V y)) := by
        rw [hjLower,
          ← globalNormResidueMonoidHom_eq_ofEmbedding_standard]
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
          (globalNormResidueMonoidHomOfEmbedding F E j
            (IdeleGroup.finitePlaceIdeleClass V y)) := by
        apply Eq.symm
        apply
          globalNormResidueMonoidHomOfEmbedding_norm_restriction_apply_p1
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σE :=
        congrArg
          ((AlgEquiv.restrictNormalHom L).comp
            (AlgEquiv.restrictScalarsHom K)) hupper
      _ = restriction σE := rfl
      _ = σK := hrestrict
  exact ⟨z, hlocal, hglobal⟩


end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_Factorization
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldAbsoluteFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsAbelianGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceOverextension_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Factorization of the global Artin map through local Artin maps

This module completes the auxiliary-field argument, factors the global
norm-residue map through each local Artin quotient, and proves the
finite-place local-global compatibility theorem.
-/

open scoped IsMulCommutative NumberField
open NumberField
open AlgebraicNumberTheory.Valuations
open HilbertRamification

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open CyclicCohomology
open KummerTheory

attribute [local instance]
  finitePadicAuxiliaryExtensionQuotientIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The cyclotomic auxiliary-field construction supplies a local
representative on which the local and global Artin values agree. -/
theorem exists_finitePlacePrimary_localGlobalRepresentative
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1)
    (hgenerate :
      Subgroup.closure
          ({σ.1} : Set (Gal(L / K))) =
        ⊤)
    (hprimary :
      σ.1 ∈
        CommGroup.primaryComponent
          (Gal(L / K)) p.1) :
    ∃ z : (v.adicCompletion K)ˣ,
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v z = σ.1 ∧
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) = σ.1 := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseScalarTower K L
  let := numberFieldTowerExtensionSubgroup_normal K L
  obtain
      ⟨τ, hτσ, hτdecomposition, hτdegree,
        _hfinite, _hbase, _hintersection, _hcontainment,
        n, hn, hdegree⟩ :=
    exists_finitePlacePrimaryCyclotomicAuxiliaryFixedField
      (K := K) (L := L) v p σ hgenerate hprimary
  have hprimaryQuotient :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1 :=
    numberFieldTowerFiniteQuotientCoordinate_mem_primary
      (K := K) (L := L) p τ σ.1 hτσ hprimary
  let data :=
    numberFieldTowerFinitePadicAuxiliaryLocalGlobalRepresentative
      (K := K) (L := L) v p τ hτdegree hτdecomposition
      n hn hdegree hprimaryQuotient
  exact ⟨data.1, data.2.1.trans hτσ, data.2.2.trans hτσ⟩

/-- A primary generator at an explicit upper place can first be realized
by the auxiliary construction and then normed through an explicit base
change.  This short bridge keeps the auxiliary witness out of the
cyclic-fixed-field construction. -/
opaque exists_finitePlacePrimaryNormDescent_localGlobalRepresentative
    {M : Type}
    [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    [Algebra M L] [FiniteDimensional M L] [IsAbelianGalois M L]
    [IsScalarTower K M L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (W : IsDedekindDomain.HeightOneSpectrum (𝓞 M))
    (hWbelow : finitePlaceBelow (K := K) W = v)
    (p : Nat.Primes)
    (δM :
      absoluteValueDecompositionGroup M
        (chosenFinitePlaceExtension (L := L) W).1)
    (hgenerate :
      Subgroup.closure ({δM.1} : Set (Gal(L / M))) = ⊤)
    (hprimary :
      δM.1 ∈ CommGroup.primaryComponent (Gal(L / M)) p.1)
    (σG : Gal(L / K))
    (hrestrict :
      ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) δM.1 = σG) :
    ∃ z : (v.adicCompletion K)ˣ,
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v z = σG ∧
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) = σG := by
  obtain ⟨y, hy, hglobalM⟩ :=
    exists_finitePlacePrimary_localGlobalRepresentative
      (K := M) (L := L) W p δM hgenerate hprimary
  exact
    exists_finitePlaceNormDescent_localGlobalRepresentative
      (K := K) (L := L) v W hWbelow
      δM.1 σG hrestrict y hy hglobalM

/-- Cyclic fixed-field descent turns a primary decomposition
automorphism into a lower representative without exposing the constructed
field tower in the declaration type. -/
opaque exists_finitePlacePrimary_cyclicFixedFieldRepresentative
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (δ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1)
    (hprimary :
      δ.1 ∈ CommGroup.primaryComponent (Gal(L / K)) p.1) :
    ∃ z : (v.adicCompletion K)ˣ,
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v z = δ.1 ∧
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) = δ.1 := by
  let σG : Gal(L / K) := δ.1
  let M := automorphismCyclicFixedField σG
  let : NumberField M := NumberField.of_module_finite K M
  let W := automorphismCyclicFixedPlace v σG
  let σM : Gal(L / M) := automorphismOverCyclicFixedField σG
  have hσMdecomposition :
      σM ∈
        absoluteValueDecompositionGroup M
          (chosenFinitePlaceExtension (L := L) W).1 := by
    exact
      automorphismOverCyclicFixedField_mem_chosenFinitePlaceDecompositionGroup
        (K := K) (L := L) v δ
  let δM :
      absoluteValueDecompositionGroup M
        (chosenFinitePlaceExtension (L := L) W).1 :=
    ⟨σM, hσMdecomposition⟩
  have hσMrestrict : σM.restrictScalars K = σG :=
    automorphismOverCyclicFixedField_restrictScalars σG
  have hσMprimary :
      σM ∈ CommGroup.primaryComponent (Gal(L / M)) p.1 := by
    obtain ⟨n, hn⟩ := hprimary
    have hnG : σG ^ (p.1 ^ n) = 1 := hn
    refine ⟨n, ?_⟩
    apply AlgEquiv.restrictScalars_injective K
    change
      (AlgEquiv.restrictScalarsHom K) (σM ^ (p.1 ^ n)) =
        (AlgEquiv.restrictScalarsHom K) (1 : Gal(L / M))
    rw [
      map_pow,
      AlgEquiv.restrictScalarsHom_apply,
      hσMrestrict,
      hnG,
      map_one
    ]
  have hWbelow : finitePlaceBelow (K := K) W = v :=
    finitePlaceBelow_automorphismCyclicFixedPlace
      (K := K) (L := L) v σG
  have hrestrictσM :
      ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σM =
        σG := by
    simpa only [
      MonoidHom.coe_comp,
      Function.comp_apply,
      AlgEquiv.restrictNormalHom_id,
      MonoidHom.id_apply,
      AlgEquiv.restrictScalarsHom_apply
    ] using hσMrestrict
  exact
    exists_finitePlacePrimaryNormDescent_localGlobalRepresentative
      (K := K) (L := L) v W hWbelow p δM
      (automorphismOverCyclicFixedField_generates σG)
      hσMprimary σG hrestrictσM

end Reciprocity
end GlobalClassFieldTheory
end
end


