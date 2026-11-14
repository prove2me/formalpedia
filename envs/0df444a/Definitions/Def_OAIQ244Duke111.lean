-- Prove2me | Definitions.Def_OAIQ244Duke111
-- name    : OAIQ244Duke111
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T04:40:01.138233+00:00
-- url     : https://prove2.me/theorems/39e56a05-f174-441b-bfe4-5bf3040e6444
-- title:
--   Definitions bundle OAIQ244Duke111 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 7 definitions, 4 instances and 14 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.abstractFixedFieldInclusionTransportedExtensionQuotientValue`, `GlobalClassFieldTheory.Reciprocity.exists_finitePlaceNormDescent_localGlobalRepresentative`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryAutomorphism`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryAutomorphism_mem_topPlaceDecomposition`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliarySubgroupLift`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension`, `GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryTopPlace_automorphism_apply`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_AbstractFixedFieldGlobalNormResidue`, `GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_Factorization`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicAuxiliaryField`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke107`, `OAIQ244Duke108` and `OAIQ244Duke109` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke112`; the proof of `OAI.DukePrimeDegree.hasCyclicRayRealizations_unconditional`.
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
import Definitions.Def_OAIQ244Duke107
import Definitions.Def_OAIQ244Duke108
import Definitions.Def_OAIQ244Duke109

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_AbstractFixedFieldGlobalNormResidue
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal
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
    numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsAlgebra_r1f6fd8_1
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
    numberFieldEmbeddedAbstractRelativeFixedFieldIsGalois_r1f6fd8_1
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

attribute [local instance] GlobalClassFieldTheory.Reciprocity.numberFieldStandardExtensionQuotientFinite
/-- The existing global norm-residue map is the explicit-embedding
construction for the standard chosen embedding of the top field. -/
theorem globalNormResidueMonoidHom_eq_ofEmbedding_standard :
    globalNormResidueMonoidHom K L =
      globalNormResidueMonoidHomOfEmbedding K L
        (numberFieldSeparableClosureEmbedding L) := by
  apply MonoidHom.ext
  intro c
  apply Additive.toMul.injective
  change
    globalNormResidueEquiv K L
        (Additive.ofMul
          (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c)) =
      globalNormResidueEquivOfEmbedding K L
        (numberFieldSeparableClosureEmbedding L)
        (Additive.ofMul
          (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c))
  exact congrArg
    (fun e :
      Additive
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) ≃+
        Additive (Gal(L / K)) =>
      e (Additive.ofMul
        (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c)))
    (globalNormResidueEquiv_eq_ofEmbedding_standard K L)

end EmbeddedNumberFieldRealization

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicCompositum_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseModule _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerSMul _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower _root_.GlobalClassFieldTheory.Reciprocity.abstractFixedFieldCyclotomicFiniteLayer_numberField _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.narrowClassGroup_finite _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal
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

local instance ideleClassGroupIsMulCommutative_r1f6fd8_1
    {F : Type} [Field F] [NumberField F]
    : IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
local instance ideleClassSubgroupNormal_r1f6fd8_1
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
/-- The packaged value at the literal fixed-field realization is the ambient
fixed-part norm-residue homomorphism evaluated at the same idele class. -/
theorem rationalFiniteNormResidueValue_abstractFixedField_eq_ambient
    (c : IdeleClassGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :
    rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
        (rationalAbstractFixedFieldIdeleClassEquivFixed H.field)
        (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P)
        (Additive.ofMul c) =
      ambientFixedGlobalNormResidueAddMonoidHom H P
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          H.field (Additive.ofMul c)) := by
  let eRec :=
    rationalCyclotomicDegreeData.normResidueSymbol
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      H P.toFiniteGaloisExtension
  let eGal :=
    abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P
  change
    eGal
        (eRec
          (finiteNormClass rationalIdeleClassRepresentation
            H.field P.field P.below
            (rationalAbstractFixedFieldIdeleClassEquivFixed
              H.field (Additive.ofMul c)))) =
      eGal
        (eRec
          (finiteNormClass rationalIdeleClassRepresentation
            H.field P.field P.below
            (rationalAbstractFixedFieldIdeleClassEquivFixed
              H.field (Additive.ofMul c))))
  rfl

/-- The packaged norm-residue value for the literal fixed-field realization
is the intrinsic abstract fixed-field norm-residue value. -/
theorem rationalFiniteNormResidueValue_abstractFixedField_apply
    (c : IdeleClassGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :
    Additive.toMul
        (rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
          (rationalAbstractFixedFieldIdeleClassEquivFixed H.field)
          (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup
            H P)
          (Additive.ofMul c)) =
      abstractFixedFieldGlobalNormResidueMonoidHom H P c := by
  let a :=
    rationalAbstractFixedFieldIdeleClassEquivFixed
      H.field (Additive.ofMul c)
  have hAbstract :=
    abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply H P a
  calc
    _ = Additive.toMul
        (ambientFixedGlobalNormResidueAddMonoidHom H P
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            H.field (Additive.ofMul c))) := by
      exact congrArg Additive.toMul
        (rationalFiniteNormResidueValue_abstractFixedField_eq_ambient
          (H := H) (P := P) c)
    _ = _ := by
      simpa only [a, AddEquiv.symm_apply_apply, toMul_ofMul] using
        hAbstract.symm

/-- Pointwise specification of the idele-class comparison after transporting
the explicitly embedded abstract field to the canonical packaged field.  The
transport is kept at the value boundary, so clients never compare the two
dependent additive equivalences themselves. -/
theorem
    numberFieldEmbeddedIdeleClassEquivAmbientFixed_transport_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    let HEmbedded :=
      numberFieldEmbeddedFiniteAbstractField F E j
    let hHEmbedded : HEmbedded = H :=
      numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
    Eq.mp
        (congrArg
          (fun X : FiniteAbstractField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
            Additive (IdeleClassGroup F) ≃+
              ambientFixedAddSubgroup
                rationalIdeleClassRepresentation X.field)
          hHEmbedded)
        (numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j) c =
      rationalAbstractFixedFieldIdeleClassEquivFixed H.field c := by
  dsimp only
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
  have hHEmbedded :
      numberFieldEmbeddedFiniteAbstractField F E j = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  have hFixedBase :
      abstractFixedField ℚ (SeparableClosure ℚ)
          (numberFieldEmbeddedBaseSubgroup F E j) = F :=
    congrArg
      (abstractFixedField ℚ (SeparableClosure ℚ)) hBase
  let eBase : F ≃ₐ[ℚ] F :=
    (numberFieldEmbeddedAbstractBaseFieldEquiv F E j).trans
      (IntermediateField.equivOfEq hFixedBase)
  have heBase :
      eBase = (AlgEquiv.refl : F ≃ₐ[ℚ] F) := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change x.1 = x.1
    rfl
  let hEmbeddedQuotientFinite :=
    numberFieldEmbeddedAbsoluteQuotientFinite F E j
  let hEmbeddedFixedFiniteDimensional :=
    numberFieldEmbeddedAbstractFixedFieldFiniteDimensional F E j
  apply Subtype.ext
  rw [rationalAmbientFixedAddEquiv_transport_apply_val
    hHEmbedded
    (numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j) c]
  dsimp only [numberFieldEmbeddedIdeleClassEquivAmbientFixed]
  simp only [AddEquiv.trans_apply]
  change
    ((rationalIdeleClassEquivFixed
        (abstractFixedField ℚ (SeparableClosure ℚ)
          (numberFieldEmbeddedBaseSubgroup F E j)))
      (MulEquiv.toAdditive
        (ideleClassCongr
          (numberFieldEmbeddedAbstractBaseFieldEquiv F E j)) c)).1 =
      ((rationalIdeleClassEquivFixed F) c).1
  exact rationalIdeleClassEquivFixed_congr_apply_val
    hFixedBase
    (numberFieldEmbeddedAbstractBaseFieldEquiv F E j)
    heBase c

/-- Pointwise opaque endpoint of the transported quotient equivalence. -/
noncomputable def
    abstractFixedFieldInclusionTransportedExtensionQuotientValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :=
  abstractFixedFieldInclusionTransportedExtensionQuotientEquiv H P q

/-- A packaged finite norm-residue value depends only on the value of its
idele comparison at the chosen input and the value of its Galois comparison
at the resulting norm class. -/
theorem rationalFiniteNormResidueValue_congr_apply
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteGaloisSubextension K.field)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele eIdele' : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation K.field)
    (eGalois eGalois' :
      Additive (Abelianization L.extensionQuotient) ≃+ X)
    (c : C)
    (heIdele : eIdele c = eIdele' c)
    (heGalois : ∀ z, eGalois z = eGalois' z) :
    rationalFiniteNormResidueValue K L eIdele eGalois c =
      rationalFiniteNormResidueValue K L eIdele' eGalois' c := by
  unfold rationalFiniteNormResidueValue
  rw [heIdele]
  exact heGalois _

end AbstractFixedFieldInclusion

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.cyclotomicUnramifiedGeometricMaxExtensionNormal
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
/-- The simultaneous finite/cyclotomic coordinate has abelian image,
so the inverse image of the closed cyclic subgroup generated by one
coordinate is normal in the compatible absolute Galois group of `K`.

Consequently, the auxiliary fixed field constructed below is Galois
over the embedded copy of `K`, as in the field diagram of the
finite-place reduction. -/
theorem numberFieldTowerFinitePadicCyclicPreimage_normal
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    (numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ).toSubgroup.Normal := by
  let P :=
    numberFieldTowerFinitePadicImage
      (K := K) (L := L) p
  let rangeRestriction :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p
  let γ : P.toSubgroup :=
    rangeRestriction τ
  let Γ :=
    ClassFormation.padicCyclicClosure γ
  change
    (Γ.toSubgroup.comap
      rangeRestriction.toMonoidHom).Normal
  exact
    Γ.toSubgroup.normal_of_isMulCommutative.comap
      rangeRestriction.toMonoidHom

/-- The distinguished simultaneous finite/cyclotomic lift itself lies
in the auxiliary subgroup whose fixed field is used for descent. -/
theorem numberFieldTowerFinitePadicCyclicFixedSubgroup_generator_mem
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    (τ : Gal(SeparableClosure ℚ / ℚ)) ∈
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ).toSubgroup := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let rangeRestriction :=
    numberFieldTowerFinitePadicRangeRestriction
      (K := K) (L := L) p
  let γ :=
    rangeRestriction τ
  let Γ :=
    ClassFormation.padicCyclicClosure γ
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  change
    (τ : Gal(SeparableClosure ℚ / ℚ)) ∈
      U.toSubgroup.map H.toSubgroup.subtype
  refine ⟨τ, ?_, rfl⟩
  change rangeRestriction τ ∈ Γ.toSubgroup
  exact
    (ClassFormation.padicCyclicClosureGenerator γ).2

/-- The auxiliary fixed field is Galois over the compatible embedded
copy of `K`.  On subgroup coordinates this is normality of the
embedded cyclic-preimage subgroup inside the base fixing subgroup. -/
theorem
    numberFieldTowerFinitePadicCyclicFixedSubgroup_extension_normal
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    (extensionSubgroup
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ)
      (numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
        (K := K) (L := L) p τ)).Normal := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let hSH :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
      (K := K) (L := L) p τ
  have hU : U.toSubgroup.Normal :=
    numberFieldTowerFinitePadicCyclicPreimage_normal
      (K := K) (L := L) p τ
  have hext :
      extensionSubgroup H S hSH =
        U.toSubgroup := by
    ext u
    rw [mem_extensionSubgroup_iff]
    change
      u.1 ∈ U.toSubgroup.map H.toSubgroup.subtype ↔
        u ∈ U.toSubgroup
    constructor
    · rintro ⟨z, hz, hzu⟩
      have hzu' : z = u :=
        Subtype.ext hzu
      exact hzu' ▸ hz
    · intro hu
      exact ⟨u, hu, rfl⟩
  exact hext.symm ▸ hU

/-- The relative subgroup defined by the ambient auxiliary fixed
subgroup is exactly the original cyclic preimage inside the compatible
absolute Galois group of `K`. -/
theorem
    numberFieldTowerFinitePadicCyclicFixedSubgroup_extensionSubgroup
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    extensionSubgroup
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup_le_baseSubgroup
          (K := K) (L := L) p τ) =
      (numberFieldTowerFinitePadicCyclicPreimage
        (K := K) (L := L) p τ).toSubgroup := by
  let H :=
    numberFieldTowerBaseSubgroup K L
  let U :=
    numberFieldTowerFinitePadicCyclicPreimage
      (K := K) (L := L) p τ
  ext u
  rw [mem_extensionSubgroup_iff]
  change
    u.1 ∈ U.toSubgroup.map H.toSubgroup.subtype ↔
      u ∈ U.toSubgroup
  constructor
  · rintro ⟨z, hz, hzu⟩
    have hzu' : z = u :=
      Subtype.ext hzu
    exact hzu' ▸ hz
  · intro hu
    exact ⟨u, hu, rfl⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicAuxiliaryField
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.ramifiedInfinitePlaceRealFixedField_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexification_infinitePlaceOverfield_smul _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
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
local instance finitePadicAuxiliaryExtensionQuotientFinite_r1f6fd8_1 :
    Finite
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  numberFieldTowerExtensionQuotient_finite K L
attribute [local instance] GlobalClassFieldTheory.Reciprocity.finitePadicAuxiliaryExtensionQuotientIsMulCommutative
/-- The compatible base and top embeddings form the actual
base-change square inside the rational separable closure. -/
theorem numberFieldTowerFinitePadicAuxiliaryEmbedding_algebraMap
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (x : K) :
    ((numberFieldTowerFinitePadicAuxiliaryTopEmbedding
        (K := K) (L := L) p τ (algebraMap K L x) :
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) :
      SeparableClosure ℚ) =
    ((numberFieldTowerFinitePadicAuxiliaryBaseEmbedding
        (K := K) (L := L) p τ x :
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) :
      SeparableClosure ℚ) := by
  rfl

noncomputable instance
    numberFieldTowerFinitePadicAuxiliary_topAlgebra
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    Algebra L
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  exact
    (numberFieldTowerFinitePadicAuxiliaryTopEmbedding
      (K := K) (L := L) p τ).toRingHom.toAlgebra

instance
    numberFieldTowerFinitePadicAuxiliary_topRatScalarTower
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsScalarTower ℚ L
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  exact
    IsScalarTower.of_algebraMap_eq'
      (numberFieldTowerFinitePadicAuxiliaryTopEmbedding
        (K := K) (L := L) p τ).comp_algebraMap.symm

noncomputable instance
    numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    Algebra K
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  exact
    ((numberFieldTowerFinitePadicAuxiliaryTopEmbedding
        (K := K) (L := L) p τ).comp
      (IsScalarTower.toAlgHom ℚ K L)).toRingHom.toAlgebra

instance
    numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    IsScalarTower K L
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The distinguished absolute lift, regarded as an element of the
auxiliary base subgroup. -/
noncomputable def numberFieldTowerFinitePadicAuxiliarySubgroupLift
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ).toSubgroup :=
  ⟨τ.1,
    numberFieldTowerFinitePadicCyclicFixedSubgroup_generator_mem
      (K := K) (L := L) p τ⟩

/-- The actual automorphism of the auxiliary compositum induced by
the distinguished simultaneous finite/cyclotomic lift. -/
noncomputable def numberFieldTowerFinitePadicAuxiliaryAutomorphism
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    let P :=
      numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ
    let S :=
      numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ
    Gal(
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below /
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) S) := by
  dsimp only
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let σS :=
    numberFieldTowerFinitePadicAuxiliarySubgroupLift
      (K := K) (L := L) p τ
  exact
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ)
      S P.field P.below
      P.toFiniteGaloisExtension.normal
      (QuotientGroup.mk'
        (extensionSubgroup
          S P.field P.below)
        σS)

/-- On the common separable closure, the auxiliary automorphism acts
by the original distinguished ambient lift. -/
theorem numberFieldTowerFinitePadicAuxiliaryAutomorphism_apply_val
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (x :
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) :
    ((numberFieldTowerFinitePadicAuxiliaryAutomorphism
        (K := K) (L := L) p τ x :
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) :
      SeparableClosure ℚ) =
        τ.1 (x : SeparableClosure ℚ) := by
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let σS :=
    numberFieldTowerFinitePadicAuxiliarySubgroupLift
      (K := K) (L := L) p τ
  exact
    (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
        ℚ (SeparableClosure ℚ)
        S P.field P.below
        P.toFiniteGaloisExtension.normal σS x).symm

/-- Restriction of the same separable-closure place to the genuine
auxiliary compositum.  Its restriction to `K` agrees exactly with the
original normalized finite absolute value. -/
noncomputable def
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ).below
  let wΩ :=
    numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v (chosenFinitePlaceExtension (L := L) v)
  refine
    ⟨wΩ.1.comp (f := E.val.toRingHom) E.val.injective, ?_⟩
  intro x
  change
    wΩ.1 (numberFieldTowerLowerEmbedding K L x) =
      NumberField.HeightOneSpectrum.adicAbv K v x
  exact wΩ.2 x

/-- Evaluation of the distinguished auxiliary automorphism through the
restricted top-field place.  Isolating this coercion calculation prevents the
whole decomposition-group proof from normalizing the fixed-field tower. -/
opaque
    numberFieldTowerFinitePadicAuxiliaryTopPlace_automorphism_apply
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    let P := numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
    let E := LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
    let wE := numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
    let σE := numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
    ∀ x : E,
      wE.1 (σE x) =
        (numberFieldTowerFinitePlaceExtensionToSeparableClosure
          K L v (chosenFinitePlaceExtension (L := L) v)).1
            (τ.1 (x : SeparableClosure ℚ)) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  dsimp only
  intro x
  change
    (numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v (chosenFinitePlaceExtension (L := L) v)).1
        ((numberFieldTowerFinitePadicAuxiliaryAutomorphism
          (K := K) (L := L) p τ x :
            LocalClassFieldTheory.abstractRelativeFixedField
              ℚ (SeparableClosure ℚ)
              (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
                (K := K) (L := L) p τ).below) : SeparableClosure ℚ) = _
  rw [
    numberFieldTowerFinitePadicAuxiliaryAutomorphism_apply_val
      (K := K) (L := L) p τ]

/-- The distinguished auxiliary automorphism preserves the top-field place
obtained by restricting the original separable-closure place. -/
opaque numberFieldTowerFinitePadicAuxiliaryAutomorphism_mem_topPlaceDecomposition
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hdecomposition :
      letI : Algebra K (SeparableClosure ℚ) :=
        numberFieldTowerSeparableClosureBaseAlgebra K L
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v (chosenFinitePlaceExtension (L := L) v)).1) :
    let S := numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
    let F := LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
    let wE := numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
    let σE := numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
    σE ∈ absoluteValueDecompositionGroup F wE.1 := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  dsimp only at hdecomposition ⊢
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let wE :=
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
  let σE :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
  intro x
  change
    wE.1 (σE x) < 1 ↔
      wE.1 x < 1
  rw [
    numberFieldTowerFinitePadicAuxiliaryTopPlace_automorphism_apply
      (K := K) (L := L) v p τ x,
    show
      wE.1 x =
        (numberFieldTowerFinitePlaceExtensionToSeparableClosure
          K L v
          (chosenFinitePlaceExtension (L := L) v)).1
            (x : SeparableClosure ℚ) from rfl]
  exact hdecomposition (x : SeparableClosure ℚ)

/-- Pointwise form of norm/restriction naturality.  Keeping the function
equality and its coercion normalization in this small declaration prevents
the auxiliary-field witness construction below from repeatedly elaborating
the full pair of composite homomorphisms. -/
theorem globalNormResidueMonoidHomOfEmbedding_norm_restriction_apply_p1
    (K K' L L' : Type)
    [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Field L] [NumberField L]
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K') :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
          (globalNormResidueMonoidHomOfEmbedding K' L' j c) =
      globalNormResidueMonoidHomOfEmbedding K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))
        (_root_.ideleClassNorm K K' c) := by
  exact
    DFunLike.congr_fun
      (globalNormResidueMonoidHomOfEmbedding_norm_restriction
        (K := K) (L := L) (K' := K') (L' := L') j) c



end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_Factorization
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldIsGaloisOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldScalarTowerOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormAmbientNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsCyclotomicExtension _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormCyclotomicFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormExponentNeZero _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldAlgebraOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldFiniteDimensionalOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldModuleOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldSMulOverBase _root_.GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexNormKummerFieldScalarTower _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldBaseNumberField _root_.GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldExtensionIsGalois _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldBaseAlgebraOverOriginal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormQuotient_finite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertNormSubgroup_finiteIndex
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

/-- The finite quotient coordinate remains primary after transport to
the relative Galois group. -/
theorem numberFieldTowerFiniteQuotientCoordinate_mem_primary
    (p : Nat.Primes) (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (σ' : Gal(L / K))
    (hτσ :
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) = σ')
    (hprimary :
      σ' ∈ CommGroup.primaryComponent (Gal(L / K)) p.1) :
    numberFieldTowerFiniteQuotientCoordinate
        (K := K) (L := L) τ ∈
      CommGroup.primaryComponent
        ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
          extensionSubgroup
            (numberFieldTowerBaseSubgroup K L)
            (numberFieldTowerTopSubgroup L)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
        p.1 := by
  obtain ⟨m, hm⟩ := hprimary
  refine ⟨m, ?_⟩
  apply (numberFieldTowerExtensionQuotientEquivGaloisGroup K L).injective
  calc
    (numberFieldTowerExtensionQuotientEquivGaloisGroup K L)
        (numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ^ (p.1 ^ m)) =
      (numberFieldTowerExtensionQuotientEquivGaloisGroup K L
        (numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ)) ^ (p.1 ^ m) := map_pow _ _ _
    _ = σ' ^ (p.1 ^ m) :=
      congrArg (fun g => g ^ (p.1 ^ m)) hτσ
    _ = 1 := hm
    _ = numberFieldTowerExtensionQuotientEquivGaloisGroup K L 1 :=
      (map_one _).symm

/-- Pointwise norm/restriction naturality, with the coercion from the
homomorphism equality normalized once outside the descent construction. -/
theorem globalNormResidueMonoidHomOfEmbedding_norm_restriction_apply_p0
    (K K' L L' : Type)
    [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Field L] [NumberField L]
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K') :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
          (globalNormResidueMonoidHomOfEmbedding K' L' j c) =
      globalNormResidueMonoidHomOfEmbedding K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))
        (_root_.ideleClassNorm K K' c) := by
  exact
    DFunLike.congr_fun
      (globalNormResidueMonoidHomOfEmbedding_norm_restriction
        (K := K) (L := L) (K' := K') (L' := L') j) c

/-- Norming one upper representative down a finite Galois base-change
transports both its chosen local Artin value and its global norm-residue
value.  All fields and places are explicit here, so no constructed
fixed-field tower occurs in the declaration type. -/
opaque exists_finitePlaceNormDescent_localGlobalRepresentative
    {M : Type}
    [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    [Algebra M L] [FiniteDimensional M L] [IsAbelianGalois M L]
    [IsScalarTower K M L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (W : IsDedekindDomain.HeightOneSpectrum (𝓞 M))
    (hWbelow : finitePlaceBelow (K := K) W = v)
    (σM : Gal(L / M)) (σG : Gal(L / K))
    (hrestrict :
      ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σM = σG)
    (y : (W.adicCompletion M)ˣ)
    (hy :
      chosenFinitePlaceArtinMonoidHom
          (K := M) (L := L) W y = σM)
    (hglobalM :
      globalNormResidueMonoidHom M L
          (IdeleGroup.finitePlaceIdeleClass W y) = σM) :
    ∃ z : (v.adicCompletion K)ˣ,
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v z = σG ∧
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) = σG := by
  let Wover :
      {W' : IsDedekindDomain.HeightOneSpectrum (𝓞 M) //
        finitePlaceBelow (K := K) W' = v} :=
    ⟨W, hWbelow⟩
  let :
      Algebra (v.adicCompletion K) (W.adicCompletion M) :=
    (finitePlaceAdicCompletionMap K M v Wover).toAlgebra
  let z : (v.adicCompletion K)ˣ :=
    LocalFieldTheory.normUnits
      (v.adicCompletion K) (W.adicCompletion M) y
  have hlocalNorm :
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v z =
        σG := by
    have hnat :=
      DFunLike.congr_fun
        (chosenFinitePlaceArtinMonoidHom_norm_restriction_of_below_eq
          (K := K) (L := L) (K' := M) (L' := L)
          v W hWbelow) y
    change
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.adicCompletion M) y) =
        σG
    calc
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.adicCompletion M) y) =
        ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
            (chosenFinitePlaceArtinMonoidHom
              (K := M) (L := L) W y) := by
                simpa only [MonoidHom.coe_comp, Function.comp_apply]
                  using hnat.symm
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σM :=
        congrArg
          (((AlgEquiv.restrictNormalHom L).comp
            (AlgEquiv.restrictScalarsHom K)) : Gal(L / M) →* Gal(L / K)) hy
      _ = σG := hrestrict
  let j : L →ₐ[ℚ] SeparableClosure ℚ :=
    AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L
  have hjLower :
      j.comp (IsScalarTower.toAlgHom ℚ L L) =
        AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L := by
    apply AlgHom.ext
    intro a
    rfl
  have hnormClass :
      _root_.ideleClassNorm K M
          (IdeleGroup.finitePlaceIdeleClass W y) =
        IdeleGroup.finitePlaceIdeleClass v z := by
    simpa only [Wover, z] using
      (IdeleGroup.ideleClassNorm_finitePlaceIdeleClass_eq_normUnits
        (K := K) (L := M) v Wover y)
  have hglobalNorm :
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) =
        σG := by
    calc
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) =
          globalNormResidueMonoidHom K L
            (_root_.ideleClassNorm K M
              (IdeleGroup.finitePlaceIdeleClass W y)) :=
        congrArg (globalNormResidueMonoidHom K L) hnormClass.symm
      _ = globalNormResidueMonoidHomOfEmbedding K L
          (j.comp (IsScalarTower.toAlgHom ℚ L L))
          (_root_.ideleClassNorm K M
            (IdeleGroup.finitePlaceIdeleClass W y)) := by
        rw [hjLower,
          ← globalNormResidueMonoidHom_eq_ofEmbedding_standard]
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
          (globalNormResidueMonoidHomOfEmbedding M L j
            (IdeleGroup.finitePlaceIdeleClass W y)) := by
        apply Eq.symm
        apply
          globalNormResidueMonoidHomOfEmbedding_norm_restriction_apply_p0
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
          (globalNormResidueMonoidHom M L
            (IdeleGroup.finitePlaceIdeleClass W y)) := by
        exact congrArg
          ((AlgEquiv.restrictNormalHom L).comp
            (AlgEquiv.restrictScalarsHom K))
          (DFunLike.congr_fun
            (globalNormResidueMonoidHom_eq_ofEmbedding_standard
              (K := M) (L := L))
            (IdeleGroup.finitePlaceIdeleClass W y)).symm
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σM :=
        congrArg
          ((AlgEquiv.restrictNormalHom L).comp
            (AlgEquiv.restrictScalarsHom K)) hglobalM
      _ = σG := hrestrict
  exact ⟨z, hlocalNorm, hglobalNorm⟩

end Reciprocity
end GlobalClassFieldTheory
end
end


