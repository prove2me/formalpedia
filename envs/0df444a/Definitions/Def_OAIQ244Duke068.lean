-- Prove2me | Definitions.Def_OAIQ244Duke068
-- name    : OAIQ244Duke068
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:24:32.815332+00:00
-- url     : https://prove2.me/theorems/162878fc-4309-4afb-b7a5-7f145b152ef5
-- title:
--   Definitions bundle OAIQ244Duke068 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 46 declarations of OpenAI's Lean: 12 definitions, 1 instance and 33 theorems. The definitions and types are `GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap`, `IdeleGroup.finitePlaceBaseUnitExtension`, `IdeleGroup.finitePlaceCompletionDegree`, `IdeleGroup.infinitePlaceBaseUnitExtension`, `IdeleGroup.infinitePlaceCompletionDegree`, `RayClass.fractionalIdealNorm`, `RayClass.idealNormExponentMap`, `RayClass.idealNormLiftedModulus`, `RayClass.idealNormLiftedModulusExponent`, `RayClass.idealNormLiftedSupport`, `RayClass.primeToModulusIdealNorm`, `chosenFinitePlaceTargetIntegralUniformizer`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Completion_UnramifiedComparison_CompletionToIdeal`, `AlgebraicNumberTheory_Idele_ClassGroup_AlgEquiv`, `AlgebraicNumberTheory_Idele_Extension_IdealClass`, `AlgebraicNumberTheory_Idele_Extension_InfiniteOnePlaceBaseNorm`, `AlgebraicNumberTheory_Idele_Extension_OnePlaceBaseNorm`, `AlgebraicNumberTheory_RayClass_IdealNorm`, `GlobalClassFieldTheory_GlobalClassFields_SmallHilbertClassField`, `GlobalClassFieldTheory_GlobalClassFields_SmallHilbertNormCharacterization`, `GlobalClassFieldTheory_IdealClassFieldTheory_PrincipalIdealTheorem`, `GlobalClassFieldTheory_Reciprocity_OnePlaceNormKernel`, `LubinTate_FiniteLevel_FiniteParameters`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke054`, `OAIQ244Duke055`, `OAIQ244Duke056`, `OAIQ244Duke058`, `OAIQ244Duke059`, `OAIQ244Duke060` and `OAIQ244Duke061` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke072` and `OAIQ244Duke073`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finsupp.Basic
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
import Mathlib.Algebra.Polynomial.Monic
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
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.FormalGroup.Basic
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
import Mathlib.RingTheory.MvPowerSeries.Expand
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
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Substitution
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
import Definitions.Def_OAIQ244Duke054
import Definitions.Def_OAIQ244Duke055
import Definitions.Def_OAIQ244Duke056
import Definitions.Def_OAIQ244Duke058
import Definitions.Def_OAIQ244Duke059
import Definitions.Def_OAIQ244Duke060
import Definitions.Def_OAIQ244Duke061

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_UnramifiedComparison_CompletionToIdeal
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_apply _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk _root_.LocalClassFieldTheory.principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply _root_.LocalClassFieldTheory.principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk _root_.LocalClassFieldTheory.principalUnitsSuccQuotTraceOfUnramifiedValuation_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius _root_.LocalFieldTheory.galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius_zpow _root_.LocalFieldTheory.galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.padicValuationSubringToCompletedUnramifiedWittRing_uniformizer _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.infinitePlaceAboveEquivExtension_apply_val _root_.infinitePlaceTensorRingEquivAbove_apply _root_.infinitePlaceTensorUnitsEquivAbove_apply _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# From completed to ideal-theoretic unramifiedness

This file recovers ideal-theoretic unramifiedness from the actual chosen
localized completion and propagates it to every place above the base place in
a finite Galois extension.
-/

open scoped NumberField Classical NNReal ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual image of the chosen global integral uniformizer in the
integer ring of the chosen localized completion. -/
noncomputable def chosenFinitePlaceTargetIntegralUniformizer
    (v : HeightOneSpectrum (𝓞 K)) :
    𝒪[ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v] :=
  algebraMap
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]
      𝒪[ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v]
    (chosenFinitePlaceCompletionIntegralUniformizer v).completionInteger

omit [NumberField L] in
/-- In an unramified chosen localized completion, the canonical global
integral uniformizer remains a uniformizer after scalar extension. -/
theorem chosenFinitePlace_integralUniformizer_map_isUniformizer
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    (ValuativeRel.valuation
      (ChosenFinitePlaceLocalizedCompletion
        (K := K) (L := L) v)).IsUniformizer
      ((chosenFinitePlaceTargetIntegralUniformizer
          (K := K) (L := L) v :
        𝒪[ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) v]) :
        ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) v) := by
  let vK := HeightOneSpectrum.adicAbv K v
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v
  let :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        vK.Completion E := by
    simpa [ChosenFinitePlaceIsUnramified] using hunram
  let πData :=
    chosenFinitePlaceCompletionIntegralUniformizer v
  let baseDVF :
      ValuationTheory.DiscreteValuationField.DVF
        vK.Completion :=
    { ValueGroup := ValuativeRel.ValueGroupWithZero vK.Completion
      valuation := ValuativeRel.valuation vK.Completion }
  have hpiBaseMaximalIdeal :
      (𝓂[vK.Completion] :
          Ideal 𝒪[vK.Completion]) =
        Ideal.span ({πData.completionInteger} :
          Set 𝒪[vK.Completion]) :=
    baseDVF.maximalIdeal_eq_span_uniformizer
      πData.completionInteger_isUniformizer
  let integerMap :
      𝒪[vK.Completion] →+* 𝒪[E] :=
    algebraMap 𝒪[vK.Completion] 𝒪[E]
  let πTarget : 𝒪[E] :=
    integerMap πData.completionInteger
  have hpiTargetMaximalIdeal :
      (𝓂[E] : Ideal 𝒪[E]) =
        Ideal.span ({πTarget} : Set 𝒪[E]) := by
    calc
      (𝓂[E] : Ideal 𝒪[E]) =
          Ideal.map
            integerMap
            (𝓂[vK.Completion] :
              Ideal 𝒪[vK.Completion]) :=
        (maximalIdeal_map_eq_maximalIdeal_of_unramifiedValuation
          vK.Completion E).symm
      _ =
          Ideal.map
            integerMap
            (Ideal.span ({πData.completionInteger} :
              Set 𝒪[vK.Completion])) := by
        exact congrArg
          (Ideal.map integerMap)
          hpiBaseMaximalIdeal
      _ = Ideal.span ({πTarget} : Set 𝒪[E]) := by
        rw [Ideal.map_span, Set.image_singleton]
  let targetDVF :
      ValuationTheory.DiscreteValuationField.DVF E :=
    { ValueGroup := ValuativeRel.ValueGroupWithZero E
      valuation := ValuativeRel.valuation E }
  change
    targetDVF.valuation.IsUniformizer
      (πTarget : E)
  exact
    Valuation.isUniformizer_of_maximalIdeal_eq_span
      (v := targetDVF.valuation) hpiTargetMaximalIdeal

/-- Completed unramifiedness forces ramification index one at the actual
global centre of the chosen finite-place extension. -/
theorem
    finitePlaceExtensionCentre_ramificationIdx'_eq_one_of_chosenFinitePlaceIsUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    v.asIdeal.ramificationIdx'
        (finitePlaceExtensionCentre
          (K := K) (L := L) v
          (chosenFinitePlaceExtension (L := L) v)).asIdeal =
      1 := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let E :=
    ChosenFinitePlaceLocalizedCompletion
      (K := K) (L := L) v
  let πData :=
    chosenFinitePlaceCompletionIntegralUniformizer v
  let πTarget : 𝒪[E] :=
    chosenFinitePlaceTargetIntegralUniformizer
      (K := K) (L := L) v
  let eTarget :
      𝒪[E] ≃+* W.adicCompletionIntegers L :=
    chosenFinitePlaceLocalizedIntegerRingEquiv
      (K := K) (L := L) v
  have hpiTargetConcreteIrreducible :
      Irreducible (eTarget πTarget) := by
    apply (MulEquiv.irreducible_iff eTarget.toMulEquiv).2
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    let targetIntrinsicDVF :
        ValuationTheory.DiscreteValuationField.DVF E :=
      { ValueGroup := ValuativeRel.ValueGroupWithZero E
        valuation := ValuativeRel.valuation E }
    exact
      targetIntrinsicDVF.maximalIdeal_eq_span_uniformizer
        (by
          simpa only [πTarget] using
            chosenFinitePlace_integralUniformizer_map_isUniformizer
              (K := K) (L := L) v hunram)
  let targetDVF :
      ValuationTheory.DiscreteValuationField.DVF
        (W.adicCompletion L) :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      valuation := Valued.v }
  have hpiTargetConcreteUniformizer :
      targetDVF.valuation.IsUniformizer
        ((eTarget πTarget :
          W.adicCompletionIntegers L) :
          W.adicCompletion L) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span
      (v := targetDVF.valuation)
      hpiTargetConcreteIrreducible.maximalIdeal_eq
  have hpiTargetConcreteValuation :
      targetDVF.valuation
          ((eTarget πTarget :
            W.adicCompletionIntegers L) :
            W.adicCompletion L) =
        WithZero.exp (-1 : ℤ) := by
    have h := hpiTargetConcreteUniformizer
    rw [Valuation.IsUniformizer.iff,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (W.valuedAdicCompletion_surjective L)] at h
    exact h
  have hpiTargetField :
      (eTarget πTarget : W.adicCompletion L) =
        algebraMap L (W.adicCompletion L)
          (algebraMap K L (πData.integer : K)) := by
    change
      finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w
            (localizedCompletionEquivCompletion
              vK (RayClass.adicAbv_isNontrivial v) w
              (algebraMap vK.Completion E
                (πData.completionInteger :
                  vK.Completion))) =
        _
    rw [(localizedCompletionEquivCompletion
      vK (RayClass.adicAbv_isNontrivial v) w).commutes,
      πData.coe_completionInteger]
    change
      finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) v w
            (AbsoluteValue.completionMap
              vK w.1 w.2
              (algebraMap K vK.Completion
                (πData.integer : K))) =
        _
    rw [AbsoluteValue.completionMap_coe,
      finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]
    rfl
  have hmapPi :
      finitePlaceExtensionAdicCompletionMap K L v w
          (algebraMap K (v.adicCompletion K)
            (πData.integer : K)) =
        (eTarget πTarget : W.adicCompletion L) := by
    rw [hpiTargetField]
    change
      finitePlaceExtensionAdicCompletionMap K L v w
          ((πData.integer : K) : v.adicCompletion K) =
        ((algebraMap K L (πData.integer : K) : L) :
          W.adicCompletion L)
    exact
      finitePlaceExtensionAdicCompletionMap_coe
        K L v w (πData.integer : K)
  have hpiConcreteValuation :
      Valued.v
          (algebraMap K (v.adicCompletion K)
            (πData.integer : K)) =
        WithZero.exp (-1 : ℤ) := by
    change
      Valued.v
          (πData.integer : v.adicCompletion K) =
        WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap,
      πData.intValuation_eq_exp_neg_one]
  let eGlobal : ℕ :=
    v.asIdeal.ramificationIdx' W.asIdeal
  have hvalued :
      WithZero.exp (-1 : ℤ) =
        WithZero.exp (-1 : ℤ) ^ eGlobal := by
    calc
      WithZero.exp (-1 : ℤ) =
          Valued.v
            (eTarget πTarget :
              W.adicCompletion L) :=
        hpiTargetConcreteValuation.symm
      _ =
          Valued.v
            (finitePlaceExtensionAdicCompletionMap
              K L v w
              (algebraMap K (v.adicCompletion K)
                (πData.integer : K))) := by
        exact congrArg
          (fun x : W.adicCompletion L => Valued.v x)
          hmapPi.symm
      _ =
          Valued.v
              (algebraMap K (v.adicCompletion K)
                (πData.integer : K)) ^
            eGlobal := by
        exact
          finitePlaceExtensionAdicCompletionMap_valued
              K L v w
              (algebraMap K (v.adicCompletion K)
                (πData.integer : K))
      _ = WithZero.exp (-1 : ℤ) ^ eGlobal := by
        exact congrArg (fun z => z ^ eGlobal)
          hpiConcreteValuation
  have hexp :
      WithZero.exp (-1 : ℤ) =
        WithZero.exp (-(eGlobal : ℤ)) := by
    calc
      WithZero.exp (-1 : ℤ) =
          WithZero.exp (-1 : ℤ) ^ eGlobal :=
        hvalued
      _ =
          WithZero.exp (eGlobal • (-1 : ℤ)) :=
        (WithZero.exp_nsmul _ _).symm
      _ =
          WithZero.exp (-(eGlobal : ℤ)) := by
        congr 1
        simp
  have hint :
      (-1 : ℤ) = -(eGlobal : ℤ) :=
    WithZero.exp_injective hexp
  have heGlobal : eGlobal = 1 := by
    have heInt : (1 : ℤ) = (eGlobal : ℤ) :=
      neg_injective hint
    exact_mod_cast heInt.symm
  exact heGlobal

/-- Unramifiedness of the actual chosen localized completion forces
ideal-theoretic unramifiedness at its global centre. -/
theorem isUnramifiedAt_of_chosenFinitePlaceIsUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    Algebra.IsUnramifiedAt (𝓞 K)
      (finitePlaceExtensionCentre
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v)).asIdeal := by
  let w := chosenFinitePlaceExtension (L := L) v
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) v w
  have hBasePrime :
      W.asIdeal.under (𝓞 K) ≠ ⊥ := by
    rw [← W.asIdeal.over_def v.asIdeal]
    exact v.ne_bot
  let : Finite ((𝓞 K) ⧸ W.asIdeal.under (𝓞 K)) :=
    Ring.HasFiniteQuotients.finiteQuotient hBasePrime
  let :
      PerfectField
        (W.asIdeal.under (𝓞 K)).ResidueField :=
    PerfectField.ofFinite
  apply Ideal.ramificationIdx_eq_one_iff.mp
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx
    v.asIdeal W.asIdeal v.ne_bot]
  exact
    finitePlaceExtensionCentre_ramificationIdx'_eq_one_of_chosenFinitePlaceIsUnramified
      (K := K) (L := L) v hunram

/-- In a finite Galois number-field extension, completed unramifiedness at
the chosen place implies ideal-theoretic unramifiedness at every finite place
above the same base place. -/
theorem
    isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 L))
    (hP : finitePlaceBelow (K := K) P = v)
    (hunram :
      ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal := by
  let w := chosenFinitePlaceExtension (L := L) v
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let : Finite (L ≃ₐ[K] L) :=
    IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let :
      IsGaloisGroup
        (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  let : P.asIdeal.LiesOver v.asIdeal := by
    constructor
    have h := congrArg HeightOneSpectrum.asIdeal hP
    simpa only [finitePlaceBelow_asIdeal] using h.symm
  let : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) v w
  have hChosen :
      Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal :=
    isUnramifiedAt_of_chosenFinitePlaceIsUnramified
      (K := K) (L := L) v hunram
  have hChosenRamification :
      W.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    let : Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal :=
      hChosen
    exact Ideal.ramificationIdx_eq_one W.asIdeal (𝓞 K)
  have hRamification :
      P.asIdeal.ramificationIdx (𝓞 K) =
        W.asIdeal.ramificationIdx (𝓞 K) :=
    HilbertRamification.Dedekind.dedekindRamification_ramificationIdx_eq
      v.asIdeal P.asIdeal W.asIdeal (L ≃ₐ[K] L)
  have hWBasePrime :
      W.asIdeal.under (𝓞 K) ≠ ⊥ := by
    rw [← W.asIdeal.over_def v.asIdeal]
    exact v.ne_bot
  let : Finite ((𝓞 K) ⧸ W.asIdeal.under (𝓞 K)) :=
    Ring.HasFiniteQuotients.finiteQuotient hWBasePrime
  let :
      PerfectField
        (W.asIdeal.under (𝓞 K)).ResidueField :=
    PerfectField.ofFinite
  have hPBasePrime :
      P.asIdeal.under (𝓞 K) ≠ ⊥ := by
    rw [← P.asIdeal.over_def v.asIdeal]
    exact v.ne_bot
  let : Finite ((𝓞 K) ⧸ P.asIdeal.under (𝓞 K)) :=
    Ring.HasFiniteQuotients.finiteQuotient hPBasePrime
  let :
      PerfectField
        (P.asIdeal.under (𝓞 K)).ResidueField :=
    PerfectField.ofFinite
  apply Ideal.ramificationIdx_eq_one_iff.mp
  exact hRamification.trans hChosenRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_IdealClass
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
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

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Local orders under the canonical completion map are multiplied by
the ramification index. -/
theorem localOrder_finitePlaceAdicCompletionMap
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : (w.adicCompletion K)ˣ) :
    (FiniteIdeleGroup.localOrder W.1
      (Units.map
        (finitePlaceAdicCompletionMap K L w W).toMonoidHom
        x)).toAdd =
      (w.asIdeal.ramificationIdx' W.1.asIdeal : ℤ) *
        (FiniteIdeleGroup.localOrder w x).toAdd := by
  rw [FiniteIdeleGroup.localOrder_apply,
    FiniteIdeleGroup.localOrder_apply]
  simp only [Units.coe_map]
  change
    -WithZero.log
        (Valued.v
          (finitePlaceAdicCompletionMap K L w W
            (x : w.adicCompletion K))) =
      (w.asIdeal.ramificationIdx' W.1.asIdeal : ℤ) *
        -WithZero.log (Valued.v (x : w.adicCompletion K))
  rw [finitePlaceAdicCompletionMap_valued, WithZero.log_pow]
  simp

namespace IdeleGroup

omit [IsGalois K L] in
/-- The local order of an extended idele is multiplied by the
ramification index at the chosen place above. -/
theorem extension_localOrder
    (a : IdeleGroup K)
    (W : HeightOneSpectrum (𝓞 L)) :
    (FiniteIdeleGroup.localOrder W
      (finiteComponent W (extension K L a))).toAdd =
      ((_root_.finitePlaceBelow
          (K := K) W).asIdeal.ramificationIdx' W.asIdeal : ℤ) *
        (FiniteIdeleGroup.localOrder
          (_root_.finitePlaceBelow (K := K) W)
          (finiteComponent
            (_root_.finitePlaceBelow (K := K) W) a)).toAdd := by
  rw [extension_finiteComponent]
  exact
    _root_.localOrder_finitePlaceAdicCompletionMap K L
      (_root_.finitePlaceBelow (K := K) W) ⟨W, rfl⟩
      (finiteComponent
        (_root_.finitePlaceBelow (K := K) W) a)

omit [IsGalois K L] in
/-- The fractional ideal attached to an extended idele is the extension
of the fractional ideal attached to the original idele. -/
theorem fractionalIdeal_extension
    (a : IdeleGroup K) :
    fractionalIdeal (extension K L a) =
      FractionalIdealGroup.extension K L
        (fractionalIdeal a) := by
  apply FractionalIdealGroup.ext_count
  intro W
  rw [FractionalIdealGroup.count_extension]
  change
    FractionalIdeal.count L W
        (((FractionalIdealGroup.factorization (K := L))
          (FiniteIdeleGroup.valuationVector
            (extension K L a).2) : FractionalIdealGroup L) :
          FractionalIdeal
            (nonZeroDivisors (𝓞 L)) L) =
      ((_root_.finitePlaceBelow
          (K := K) W).asIdeal.ramificationIdx' W.asIdeal : ℤ) *
        FractionalIdeal.count K
          (_root_.finitePlaceBelow (K := K) W)
          (((FractionalIdealGroup.factorization (K := K))
            (FiniteIdeleGroup.valuationVector a.2) :
              FractionalIdealGroup K) :
            FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K)
  rw [FractionalIdealGroup.count_factorization,
    FractionalIdealGroup.count_factorization]
  exact extension_localOrder K L a W

omit [IsGalois K L] in
/-- The ideal class attached to an extended idele is the extension of
the ideal class attached to the original idele. -/
theorem idealClass_extension
    (a : IdeleGroup K) :
    idealClass (extension K L a) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (idealClass a) := by
  change
    ClassGroup.mk L
        (fractionalIdeal (extension K L a)) =
      ClassGroup.extendedHom (𝓞 K) (𝓞 L)
        (ClassGroup.mk K (fractionalIdeal a))
  rw [fractionalIdeal_extension,
    FractionalIdealGroup.classGroup_mk_extension]

omit [IsGalois K L] in
/-- Extension sends the subgroup defining the ordinary ideal class
quotient into the corresponding subgroup over the extension field. -/
theorem extension_mem_ordinaryIdealClassSubgroup
    {a : IdeleGroup K}
    (ha : a ∈
      integralAtFinitePlaces (K := K) ⊔
        principalSubgroup K) :
    extension K L a ∈
      integralAtFinitePlaces (K := L) ⊔
        principalSubgroup L := by
  change a ∈ ordinaryIdealClassSubgroup at ha
  change extension K L a ∈ ordinaryIdealClassSubgroup
  rw [ordinaryIdealClassSubgroup_eq_ker,
    MonoidHom.mem_ker] at ha ⊢
  rw [idealClass_extension, ha, map_one]

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_AlgEquiv
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Relative idele classes under an isomorphic realization

If two finite extensions of a number field are isomorphic over the base,
their tensor-product presentations of the relative adeles are canonically
isomorphic.  This file descends that canonical isomorphism to relative
ideles and idele classes and records compatibility with the determinant
norm.

The construction is the direct tensor-product congruence

`𝔸_K ⊗[K] L ≃ 𝔸_K ⊗[K] M`

induced by an algebra equivalence `L ≃ₐ[K] M`.  In particular, no second
model of relative adeles or of the idele-class norm is introduced.
-/

open scoped NumberField TensorProduct
open NumberField
open IsDedekindDomain

noncomputable section

open RelativeIdeleGroup.Cohomology


universe u v w

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [Field M] [Algebra K M]

section Absolute

variable
    {K : Type u} {M : Type w}
    [Field K] [NumberField K] [Algebra ℚ K]
    [Field M] [NumberField M] [Algebra ℚ M]

omit [NumberField K] in
theorem finitePlaceCongr_ramificationIdx
    (e : K ≃ₐ[ℚ] M)
    (W : HeightOneSpectrum (𝓞 M)) :
    letI : Algebra K M := e.toRingHom.toAlgebra
    ((finitePlaceCongr e).symm W).asIdeal.ramificationIdx'
        W.asIdeal = 1 := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let w : HeightOneSpectrum (𝓞 K) :=
    (finitePlaceCongr e).symm W
  have hmap :
      w.asIdeal.map (algebraMap (𝓞 K) (𝓞 M)) =
        W.asIdeal := by
    change
      w.asIdeal.map
          (NumberField.RingOfIntegers.mapRingEquiv
            e.toRingEquiv) =
        W.asIdeal
    rw [← finitePlaceCongr_asIdeal e w]
    simp [w]
  rw [← hmap]
  exact
    Ideal.ramificationIdx'_map_self_eq_one
      (p := w.asIdeal)
      (by rw [hmap]; exact W.isPrime.ne_top)
      (by rw [hmap]; exact W.ne_bot)

/-- Normalized local orders are unchanged by transport along a
number-field equivalence. -/
theorem ideleCongr_localOrder
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K)
    (W : HeightOneSpectrum (𝓞 M)) :
    (FiniteIdeleGroup.localOrder W
        (IdeleGroup.finiteComponent W
          (ideleCongr e a))).toAdd =
      (FiniteIdeleGroup.localOrder
        ((finitePlaceCongr e).symm W)
        (IdeleGroup.finiteComponent
          ((finitePlaceCongr e).symm W) a)).toAdd := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let w : HeightOneSpectrum (𝓞 K) :=
    (finitePlaceCongr e).symm W
  have hW :
      finitePlaceBelow (K := K) W = w :=
    finitePlaceBelow_eq_finitePlaceCongr_symm e W
  rw [ideleCongr_finiteComponent]
  have hr :
      w.asIdeal.ramificationIdx' W.asIdeal = 1 :=
    finitePlaceCongr_ramificationIdx e W
  change
    (FiniteIdeleGroup.localOrder W
      (Units.map
        (finitePlaceAdicCompletionMap K M w ⟨W, hW⟩).toMonoidHom
        (IdeleGroup.finiteComponent w a))).toAdd =
      (FiniteIdeleGroup.localOrder w
        (IdeleGroup.finiteComponent w a)).toAdd
  simpa only [hr, Nat.cast_one, one_mul] using
    localOrder_finitePlaceAdicCompletionMap K M w
      ⟨W, hW⟩
      (IdeleGroup.finiteComponent w a)

/-- An idele is integral at every finite place exactly when its transport
along a number-field equivalence is. -/
theorem ideleCongr_mem_integralAtFinitePlaces_iff
    (e : K ≃ₐ[ℚ] M)
    (a : IdeleGroup K) :
    ideleCongr e a ∈
        IdeleGroup.integralAtFinitePlaces (K := M) ↔
      a ∈ IdeleGroup.integralAtFinitePlaces (K := K) := by
  change
    (∀ W : HeightOneSpectrum (𝓞 M),
        IdeleGroup.finiteComponent W (ideleCongr e a) ∈
          (W.adicCompletionIntegers M).units) ↔
      ∀ w : HeightOneSpectrum (𝓞 K),
        IdeleGroup.finiteComponent w a ∈
          (w.adicCompletionIntegers K).units
  constructor
  · intro h w
    let W : HeightOneSpectrum (𝓞 M) :=
      finitePlaceCongr e w
    apply
      (FiniteIdeleGroup.localOrder_eq_zero_iff w
        (IdeleGroup.finiteComponent w a)).1
    have horder := ideleCongr_localOrder e a W
    rw [show (finitePlaceCongr e).symm W = w by
      simp [W]] at horder
    rw [← horder]
    exact
      (FiniteIdeleGroup.localOrder_eq_zero_iff W
        (IdeleGroup.finiteComponent W
          (ideleCongr e a))).2 (h W)
  · intro h W
    apply
      (FiniteIdeleGroup.localOrder_eq_zero_iff W
        (IdeleGroup.finiteComponent W
          (ideleCongr e a))).1
    rw [ideleCongr_localOrder]
    exact
      (FiniteIdeleGroup.localOrder_eq_zero_iff
        ((finitePlaceCongr e).symm W)
        (IdeleGroup.finiteComponent
          ((finitePlaceCongr e).symm W) a)).2
        (h ((finitePlaceCongr e).symm W))

/-- Transport along a number-field equivalence identifies the subgroups
of ideles integral at every finite place. -/
theorem ideleIntegralAtFinitePlaces_map_congr
    (e : K ≃ₐ[ℚ] M) :
    (IdeleGroup.integralAtFinitePlaces (K := K)).map
        (ideleCongr e).toMonoidHom =
      IdeleGroup.integralAtFinitePlaces (K := M) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact
      (ideleCongr_mem_integralAtFinitePlaces_iff
        e a).2 ha
  · intro hb
    let a : IdeleGroup K := (ideleCongr e).symm b
    refine ⟨a, ?_, ?_⟩
    · exact
        (ideleCongr_mem_integralAtFinitePlaces_iff
          e a).1 (by simpa [a] using hb)
    · exact (ideleCongr e).apply_symm_apply b

/-- Transport along a number-field equivalence identifies the subgroups
defining the ordinary ideal-class quotients. -/
theorem ordinaryIdealClassSubgroup_map_congr
    (e : K ≃ₐ[ℚ] M) :
    (IdeleGroup.ordinaryIdealClassSubgroup (K := K)).map
        (ideleCongr e).toMonoidHom =
      IdeleGroup.ordinaryIdealClassSubgroup (K := M) := by
  rw [IdeleGroup.ordinaryIdealClassSubgroup,
    IdeleGroup.ordinaryIdealClassSubgroup,
    Subgroup.map_sup,
    ideleIntegralAtFinitePlaces_map_congr]
  apply congrArg
    (fun H =>
      IdeleGroup.integralAtFinitePlaces (K := M) ⊔ H)
  change
    (IdeleGroup.principalSubgroup K).map
        (ideleCongr e) =
      IdeleGroup.principalSubgroup M
  exact idelePrincipalSubgroup_map_congr e

/-- On idele class groups, transport identifies the images of the
ordinary ideal-class subgroups.  This is the subgroup-level naturality
used by the small Hilbert class field. -/
theorem ordinaryIdealClassSubgroup_image_map_ideleClassCongr
    (e : K ≃ₐ[ℚ] M) :
    (Subgroup.map
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K))
        (IdeleGroup.ordinaryIdealClassSubgroup (K := K))).map
          (ideleClassCongr e).toMonoidHom =
      Subgroup.map
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup M))
        (IdeleGroup.ordinaryIdealClassSubgroup (K := M)) := by
  have hcomp :
      (ideleClassCongr e).toMonoidHom.comp
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup K)) =
        (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup M)).comp
          (ideleCongr e).toMonoidHom := by
    ext a
    exact ideleClassCongr_mk e a
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
    ordinaryIdealClassSubgroup_map_congr]
end Absolute
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_InfiniteOnePlaceBaseNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms of base units supported at one infinite place

For an infinite place `W` of an extension field, a unit of the
completion at the place below `W` can be extended to `W` and inserted
as a one-place idele.  Its ordinary idele norm remains supported at the
place below `W`; the surviving component is the corresponding local
degree power.
-/

open scoped BigOperators NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- Extend a unit of the completion below `W` to the completion at
`W`. -/
noncomputable def infinitePlaceBaseUnitExtension
    (W : InfinitePlace L) :
    ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ →*
      W.Completionˣ := by
  letI : W.1.LiesOver
      (_root_.infinitePlaceBelow (K := K) W).1 :=
    ⟨rfl⟩
  exact
    Units.map
      (NumberField.LiesOver.completionMap
        (v := _root_.infinitePlaceBelow (K := K) W)
        (w := W)).toMonoidHom

/-- The actual completion map carries negative one to negative one. -/
@[simp]
theorem infinitePlaceBaseUnitExtension_neg_one
    (W : InfinitePlace L) :
    infinitePlaceBaseUnitExtension
        (K := K) (L := L) W
        (-1 :
          ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ) =
      (-1 : W.Completionˣ) := by
  let : W.1.LiesOver
      (_root_.infinitePlaceBelow (K := K) W).1 :=
    ⟨rfl⟩
  apply Units.ext
  simp [infinitePlaceBaseUnitExtension]

/-- The degree of the completed extension at `W` over the completion
at the place below it. -/
noncomputable def infinitePlaceCompletionDegree
    (W : InfinitePlace L) : ℕ := by
  let v := _root_.infinitePlaceBelow (K := K) W
  letI : W.1.LiesOver v.1 := ⟨rfl⟩
  letI : Algebra v.Completion W.Completion :=
    (NumberField.LiesOver.completionMap (v := v) (w := W)).toAlgebra
  exact Module.finrank v.Completion W.Completion

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_OnePlaceBaseNorm
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms of base units supported at one finite place

For a finite place `v` of an extension field, embed a unit of the
completion at the place below `v` into the completion at `v`, and
support it only at `v`.  Its ordinary idele norm is supported only at
the place below `v`; the surviving component is the corresponding
local-degree power.
-/

open scoped BigOperators NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/-- The map from units of the completion below `v` to units of the
completion at `v`, using the actual finite-place completion map. -/
noncomputable def finitePlaceBaseUnitExtension
    (v : HeightOneSpectrum (𝓞 L)) :
    ((_root_.finitePlaceBelow (K := K) v).adicCompletion K)ˣ →*
      (v.adicCompletion L)ˣ :=
  Units.map
    (finitePlaceAdicCompletionMap
      K L
      (_root_.finitePlaceBelow (K := K) v)
      ⟨v, rfl⟩).toMonoidHom

/-- The degree of the actual completed extension at `v` over the
completion at the place below `v`. -/
noncomputable def finitePlaceCompletionDegree
    (v : HeightOneSpectrum (𝓞 L)) : ℕ := by
  let q := _root_.finitePlaceBelow (K := K) v
  let W :
      {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = q} :=
    ⟨v, rfl⟩
  letI : Algebra (q.adicCompletion K) (v.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L q W).toAlgebra
  letI : Module.Finite (q.adicCompletion K) (v.adicCompletion L) :=
    finitePlaceAdicCompletionMap_moduleFinite K L q W
  exact Module.finrank (q.adicCompletion K) (v.adicCompletion L)

/-- The completed local degree at an actual finite place is positive. -/
theorem finitePlaceCompletionDegree_pos
    (v : HeightOneSpectrum (𝓞 L)) :
    0 <
      finitePlaceCompletionDegree
        (K := K) (L := L) v := by
  let q := _root_.finitePlaceBelow (K := K) v
  let W :
      {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = q} :=
    ⟨v, rfl⟩
  let : Algebra (q.adicCompletion K) (v.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L q W).toAlgebra
  let : Module.Finite (q.adicCompletion K) (v.adicCompletion L) :=
    finitePlaceAdicCompletionMap_moduleFinite K L q W
  change
    0 <
      Module.finrank
        (q.adicCompletion K) (v.adicCompletion L)
  exact Module.finrank_pos

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_IdealNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.standardLubinTateLevelValuationSubring_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra
attribute [-simp] _root_.FractionalIdealGroup.classGroup_mk_extension _root_.FractionalIdealGroup.classGroup_mk_extension_prime _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductor_apply _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.positiveRationalIdealGeneratorUnit_one _root_.RayClass.positiveRationalIdealGeneratorUnit_val _root_.RayClass.positiveRationalIdealGenerator_one _root_.RayClass.primeToIdealResidueHom_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.rationalFiniteModulus_apply _root_.RayClass.rationalModulus_finitePart_apply _root_.RayClass.signToNarrow_mk _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_mk _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms of ideals prime to a modulus

For a finite extension `L / K`, the norm of a prime of `L`
above `v` is `v` raised to the inertia degree.  Extending this rule
multiplicatively gives the genuine norm on nonzero fractional ideals.

If `m` is a modulus of `K`, a modulus upstairs is chosen deeply enough
at every prime above `m` that local norms preserve the prescribed
higher-unit conditions.  The norm therefore restricts to the groups of
fractional ideals prime to these moduli.  Its image, together with the
principal ray ideals, is the norm-defined ideal group
`N_{L/K} J_L^m P_K^m`.
-/

open scoped BigOperators Classical NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace RayClass

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- At a prime `W` above `v`, a sufficiently deep higher-unit group
has norm contained in the higher-unit group prescribed by `m` at `v`.
This is the source of the lifted modulus used for ideal norms. -/
theorem exists_localHigherUnitGroup_le_norm_preimage
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) :
    let v := _root_.finitePlaceBelow (K := K) W
    letI : Algebra (v.adicCompletion K) (W.adicCompletion L) :=
      (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩).toAlgebra
    ∃ n : ℕ,
      localHigherUnitGroup W n ≤
        (localHigherUnitGroup v (m.finitePart v)).comap
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.adicCompletion L)) := by
  classical
  let v := _root_.finitePlaceBelow (K := K) W
  let : Algebra (v.adicCompletion K) (W.adicCompletion L) :=
    (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩).toAlgebra
  let : IsScalarTower
      K (v.adicCompletion K) (W.adicCompletion L) :=
    _root_.finitePlaceAdicCompletionMap_isScalarTower K L v ⟨W, rfl⟩
  let : ContinuousSMul
      (v.adicCompletion K) (W.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (by
      change Continuous
        (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩)
      exact
        _root_.finitePlaceAdicCompletionMap_continuous
          K L v ⟨W, rfl⟩)
  let : FiniteDimensional
      (v.adicCompletion K) (W.adicCompletion L) :=
    inferInstance
  let : NontriviallyNormedField (v.adicCompletion K) :=
    NontriviallyNormedField.ofNormNeOne (by
      obtain ⟨ϖ, hϖ⟩ :=
        IsDiscreteValuationRing.exists_irreducible
          (v.adicCompletionIntegers K)
      refine ⟨(ϖ : v.adicCompletion K), ?_, ?_⟩
      · intro h
        exact hϖ.ne_zero (Subtype.ext h)
      · exact ne_of_lt (local_irreducible_norm_lt_one v hϖ))
  let U : Set (W.adicCompletion L)ˣ :=
    (LocalFieldTheory.normUnits
      (v.adicCompletion K) (W.adicCompletion L)) ⁻¹'
        (localHigherUnitGroup v (m.finitePart v) :
          Set (v.adicCompletion K)ˣ)
  have hTarget :
      (localHigherUnitGroup v (m.finitePart v) :
          Set (v.adicCompletion K)ˣ) ∈
        𝓝 (1 : (v.adicCompletion K)ˣ) :=
    (isOpen_localHigherUnitGroup v (m.finitePart v)).mem_nhds
      (localHigherUnitGroup v (m.finitePart v)).one_mem
  have hU : U ∈ 𝓝 (1 : (W.adicCompletion L)ˣ) := by
    have hcont :=
      LocalFieldTheory.normUnits_continuous_of_finiteDimensional
        (v.adicCompletion K) (W.adicCompletion L)
    have hTarget' :
        (localHigherUnitGroup v (m.finitePart v) :
          Set (v.adicCompletion K)ˣ) ∈
          𝓝 (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.adicCompletion L) 1) := by
      simpa using hTarget
    simpa [U] using hcont.continuousAt hTarget'
  obtain ⟨n, hn⟩ :=
    exists_localHigherUnitGroup_subset W hU
  refine ⟨n, ?_⟩
  intro x hx
  exact hn hx

omit [FiniteDimensional K L] in
/-- The positive local depth used at `W` in the lifted modulus.  It is
zero precisely away from the inverse image of the support of `m`. -/
noncomputable def idealNormLiftedModulusExponent
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) : ℕ :=
  if _ :
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support then
    Nat.find
        (exists_localHigherUnitGroup_le_norm_preimage
          (K := K) (L := L) m W) + 1
  else
    0

omit [FiniteDimensional K L] in
/-- Away from the pulled-back support, the lifted exponent is zero. -/
@[simp]
theorem idealNormLiftedModulusExponent_eq_zero_of_not_mem
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L))
    (hW :
      _root_.finitePlaceBelow (K := K) W ∉ m.finitePart.support) :
    idealNormLiftedModulusExponent (K := K) (L := L) m W = 0 := by
  rw [idealNormLiftedModulusExponent, dite_eq_right hW]

omit [FiniteDimensional K L] in
/-- The finite set of primes upstairs lying over the support of `m`. -/
def idealNormLiftedSupport (m : Modulus K) :
    Set (HeightOneSpectrum (𝓞 L)) :=
  {W |
    _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support}

omit [FiniteDimensional K L] in
/-- The inverse image of the finite support of a modulus is finite. -/
theorem idealNormLiftedSupport_finite (m : Modulus K) :
    (idealNormLiftedSupport (K := K) (L := L) m).Finite := by
  exact
    _root_.Set.Finite.preimage_finitePlaceBelow
      (K := K) (L := L) m.finitePart.support.finite_toSet

/-- A modulus upstairs whose local higher-unit conditions are carried
by the field norm into the conditions of `m`. -/
noncomputable def idealNormLiftedModulus
    (m : Modulus K) : Modulus L :=
  Modulus.ofFinite <|
    Finsupp.onFinset
      (idealNormLiftedSupport_finite
        (K := K) (L := L) m).toFinset
      (idealNormLiftedModulusExponent
        (K := K) (L := L) m)
      (by
        intro W hW
        rw [Set.Finite.mem_toFinset]
        by_contra hbelow
        apply hW
        rw [idealNormLiftedModulusExponent, dite_eq_right]
        exact hbelow)

omit [FiniteDimensional K L] in
@[simp]
theorem idealNormLiftedModulus_apply
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) :
    (idealNormLiftedModulus (K := K) (L := L) m).finitePart W =
      idealNormLiftedModulusExponent
        (K := K) (L := L) m W :=
  rfl

omit [FiniteDimensional K L] in
@[simp]
theorem mem_idealNormLiftedModulus_support_iff
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) :
    W ∈ (idealNormLiftedModulus
        (K := K) (L := L) m).finitePart.support ↔
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support := by
  rw [Finsupp.mem_support_iff, idealNormLiftedModulus_apply]
  by_cases hW :
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support
  · rw [idealNormLiftedModulusExponent, dite_eq_left hW]
    exact ⟨fun _ => hW, fun _ => Nat.succ_ne_zero _⟩
  · simp [idealNormLiftedModulusExponent, hW]

/-- Pushforward of the prime-exponent vector under ideal norm.  A
prime `W` contributes its exponent multiplied by the inertia degree
to the prime below it. -/
noncomputable def idealNormExponentMap :
    (HeightOneSpectrum (𝓞 L) →₀ ℤ) →+
      (HeightOneSpectrum (𝓞 K) →₀ ℤ) :=
  Finsupp.liftAddHom fun W =>
    (Finsupp.singleAddHom
      (_root_.finitePlaceBelow (K := K) W)).comp
        (AddMonoidHom.mulLeft
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ))

omit [FiniteDimensional K L] in
@[simp]
theorem idealNormExponentMap_apply
    (e : HeightOneSpectrum (𝓞 L) →₀ ℤ)
    (v : HeightOneSpectrum (𝓞 K)) :
    idealNormExponentMap (K := K) (L := L) e v =
      e.sum fun W n =>
        if _root_.finitePlaceBelow (K := K) W = v then
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n
        else
          0 := by
  classical
  simp [idealNormExponentMap, Finsupp.single_apply, eq_comm]
  refine Finsupp.sum_congr fun W _ => ?_
  split_ifs <;> rfl

/-- The genuine relative norm on nonzero fractional ideals. -/
noncomputable def fractionalIdealNorm :
    FractionalIdealGroup L →* FractionalIdealGroup K :=
  (FractionalIdealGroup.factorizationEquiv
      (K := K)).toMonoidHom.comp
    ((idealNormExponentMap
        (K := K) (L := L)).toMultiplicative.comp
      (FractionalIdealGroup.factorizationEquiv
        (K := L)).symm.toMonoidHom)

omit [FiniteDimensional K L] in
/-- The exponent of the norm at `v` is the inertia-degree weighted
pushforward of the upstairs prime exponents. -/
theorem count_fractionalIdealNorm
    (I : FractionalIdealGroup L)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        (fractionalIdealNorm (K := K) (L := L) I :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      idealNormExponentMap (K := K) (L := L)
        (FractionalIdealGroup.countVector I) v := by
  change
    FractionalIdeal.count K v
        ((FractionalIdealGroup.factorization
          ((idealNormExponentMap
            (K := K) (L := L)).toMultiplicative
            ((FractionalIdealGroup.factorizationEquiv
              (K := L)).symm I)) : FractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      _
  rw [FractionalIdealGroup.count_factorization]
  change
    idealNormExponentMap (K := K) (L := L)
        ((FractionalIdealGroup.factorizationEquiv
          (K := L)).symm I).toAdd v =
      _
  rw [factorizationEquiv_symm_toAdd]

/-- The exponent of the fractional ideal attached to an idèle is its
finite local order. -/
@[simp]
theorem _root_.IdeleGroup.count_fractionalIdeal
    (a : IdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        (IdeleGroup.fractionalIdeal a :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (FiniteIdeleGroup.localOrder v
        (IdeleGroup.finiteComponent v a)).toAdd := by
  change
    FractionalIdeal.count K v
        (((FractionalIdealGroup.factorization (K := K))
          (FiniteIdeleGroup.valuationVector a.2) :
            FractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      _
  rw [FractionalIdealGroup.count_factorization]
  rfl

omit [FiniteDimensional K L] in
/-- The fractional ideal norm preserves coprimality with a modulus
after passing to the lifted modulus upstairs. -/
theorem fractionalIdealNorm_mem_primeToModulusIdeals
    (m : Modulus K)
    (I : primeToModulusIdeals
      (idealNormLiftedModulus (K := K) (L := L) m)) :
    fractionalIdealNorm (K := K) (L := L)
        (I : FractionalIdealGroup L) ∈
      primeToModulusIdeals m := by
  intro v hv
  rw [count_fractionalIdealNorm,
    idealNormExponentMap_apply]
  classical
  simp only [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro W hW
  by_cases hbelow :
      _root_.finitePlaceBelow (K := K) W = v
  · rw [ite_eq_left hbelow]
    have hLifted :
        W ∈ (idealNormLiftedModulus
          (K := K) (L := L) m).finitePart.support := by
      rw [mem_idealNormLiftedModulus_support_iff, hbelow]
      exact hv
    rw [FractionalIdealGroup.countVector_apply, I.property W hLifted]
    simp
  · rw [ite_eq_right hbelow]

/-- The ideal norm restricted to fractional ideals prime to the
corresponding moduli. -/
noncomputable def primeToModulusIdealNorm
    (m : Modulus K) :
    primeToModulusIdeals
        (idealNormLiftedModulus (K := K) (L := L) m) →*
      primeToModulusIdeals m where
  toFun I :=
    ⟨fractionalIdealNorm (K := K) (L := L)
        (I : FractionalIdealGroup L),
      fractionalIdealNorm_mem_primeToModulusIdeals
        (K := K) (L := L) m I⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' I J := by
    apply Subtype.ext
    exact map_mul _ _ _

omit [FiniteDimensional K L] in
@[simp]
theorem primeToModulusIdealNorm_coe
    (m : Modulus K)
    (I : primeToModulusIdeals
      (idealNormLiftedModulus (K := K) (L := L) m)) :
    (primeToModulusIdealNorm
        (K := K) (L := L) m I :
      FractionalIdealGroup K) =
        fractionalIdealNorm (K := K) (L := L)
          (I : FractionalIdealGroup L) :=
  rfl

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SmallHilbertClassField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The small Hilbert class field

The small Hilbert class field corresponds to the image in the idele class
group of the ideles integral at every finite place.  Its reciprocity
quotient is canonically the ordinary ideal class group; consequently its
order is the class number.
-/

open scoped NumberField IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable {K : Type*} [Field K] [NumberField K]

attribute [local instance] GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldIdeleClassGroupIsMulCommutative
/-- The small-Hilbert norm subgroup is open. -/
theorem smallHilbertClassFieldNormSubgroup_isOpen :
    IsOpen
      ((smallHilbertClassFieldNormSubgroup (K := K) :
        Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) := by
  have hzero :
      (0 : RayClass.Modulus K).ideleCongruenceSubgroup ≤
        IdeleGroup.integralAtFinitePlaces (K := K) :=
    by
      intro a ha
      change a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K)
      rw [← RayClass.finiteCongruenceSubgroup_zero (K := K)]
      exact ha.2
  have hden :
      (0 : RayClass.Modulus K).ideleCongruenceSubgroup ≤
        IdeleGroup.integralAtFinitePlaces (K := K) ⊔
          IdeleGroup.principalSubgroup K :=
    hzero.trans le_sup_left
  have hopen :
      IsOpen
        (((IdeleGroup.integralAtFinitePlaces (K := K) ⊔
          IdeleGroup.principalSubgroup K) :
          Subgroup (IdeleGroup K)) :
          Set (IdeleGroup K)) :=
    Subgroup.isOpen_mono hden
      (RayClass.isOpen_ideleCongruenceSubgroup 0)
  rw [smallHilbertClassFieldNormSubgroup, Subgroup.coe_map]
  exact QuotientGroup.isOpenMap_coe _ hopen

/-- The small-Hilbert norm subgroup is closed. -/
theorem smallHilbertClassFieldNormSubgroup_isClosed :
    IsClosed
      ((smallHilbertClassFieldNormSubgroup (K := K) :
        Subgroup (IdeleClassGroup K)) :
        Set (IdeleClassGroup K)) :=
  (smallHilbertClassFieldNormSubgroup (K := K)).isClosed_of_isOpen
    smallHilbertClassFieldNormSubgroup_isOpen

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_OnePlaceNormKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The one-place norm kernel

At the source level, the key calculation is that an idele supported at one
finite place is a global relative-idele norm exactly when its local component
is a norm from the corresponding local tensor algebra.  The determinant-norm
comparison then identifies this image with the norm group of any chosen
completion above the place.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] [IsGalois K L] in
/-- A relative idele supported at `v` has norm equal to the one-place
idele of its local determinant norm. -/
theorem norm_relativeFinitePlaceIdele
    (v : HeightOneSpectrum (𝓞 K))
    (z : (v.adicCompletion K ⊗[K] L)ˣ) :
    RelativeIdeleGroup.norm K L
        (relativeFinitePlaceIdele (K := K) (L := L) v z) =
      finitePlaceIdele v
        (localTensorNorm (K := K) (L := L) v z) := by
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change
      IdeleGroup.infiniteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeFinitePlaceIdele
              (K := K) (L := L) v z)) =
        IdeleGroup.infiniteComponent w
          (finitePlaceIdele v
            (localTensorNorm (K := K) (L := L) v z))
    rw [RelativeIdeleGroup.infiniteComponent_norm,
      relativeFinitePlaceIdele_infiniteComponent,
      map_one, finitePlaceIdele_infiniteComponent]
  · apply RestrictedProduct.ext
    intro w
    change
      IdeleGroup.finiteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeFinitePlaceIdele
              (K := K) (L := L) v z)) =
        IdeleGroup.finiteComponent w
          (finitePlaceIdele v
            (localTensorNorm (K := K) (L := L) v z))
    by_cases hw : w = v
    · subst w
      rw [RelativeIdeleGroup.finiteComponent_norm,
        relativeFinitePlaceIdele_finiteComponent_same,
        finitePlaceIdele_finiteComponent_same]
    · rw [RelativeIdeleGroup.finiteComponent_norm,
        relativeFinitePlaceIdele_finiteComponent_of_ne v w z hw,
        map_one,
        finitePlaceIdele_finiteComponent_of_ne v w
          (localTensorNorm (K := K) (L := L) v z) hw]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SmallHilbertNormCharacterization
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Small Hilbert norm subgroups and everywhere-unramified extensions

For a finite Galois extension which is unramified at both finite and
infinite places, every idele integral at all finite places is an actual
relative-idele norm.  It follows that the actual idele-class norm range
contains the small-Hilbert norm subgroup.

This realizes the maximality of the small Hilbert class field on the
norm-subgroup side.  The resulting quotient transition gives a canonical
surjection from the ordinary class group, its exact kernel
factorization, and the divisibility of the extension norm quotient order
by the class number.
-/

open scoped IsMulCommutative NumberField NumberField.LiesOver

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Keep norm-range quotient normality out of exported declaration types. -/
local instance
    smallHilbertNormCharacterization_ideleClassGroupIsMulCommutative_r2c0e72_1 :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
omit [FiniteDimensional K L] in
/-- At an extension unramified at all infinite places, the determinant
norm image of every infinite tensor factor is the whole local
multiplicative group. -/
theorem
    infiniteTensorNormSubgroup_eq_top_of_isUnramifiedAtInfinitePlaces
    [_root_.IsUnramifiedAtInfinitePlaces K L]
    (v : InfinitePlace K) :
    _root_.infiniteTensorNormSubgroup
        (K := K) (L := L) v = ⊤ := by
  obtain ⟨w, hw⟩ :=
    InfinitePlace.comap_surjective
      (K := L) v
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  rw [
    _root_.infiniteTensorNormSubgroup_eq_localNormSubgroup
      (K := K) (L := L) v w hw]
  apply top_unique
  intro x _
  refine
    ⟨Units.map
        (algebraMap
          v.Completion w.Completion).toMonoidHom x,
      ?_⟩
  apply Units.ext
  change
    Algebra.norm v.Completion
        (algebraMap v.Completion w.Completion
          (x : v.Completion)) =
      (x : v.Completion)
  rw [
    Algebra.norm_algebraMap,
    InfinitePlace.IsUnramified.finrank_eq_one
      v (w.isUnramified K),
    pow_one]

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_IdealClassFieldTheory_PrincipalIdealTheorem
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.norm_principalIdele _root_.IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_mk _root_.ideleClassNorm_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The principal ideal theorem

This file descends genuine idele extension to the reciprocity quotients
defining the two small Hilbert class fields and proves that the resulting
map forms the naturality square with the existing ideal-class extension
`ClassGroup.extendedHom`.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField

/-- Canonical class-group commutativity supplies normality for the quotient. -/
theorem principalIdealTheoremClassGroupIsMulCommutative
    (F : Type*) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] principalIdealTheoremClassGroupIsMulCommutative

section SmallHilbertIdeleExtension

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [IsGalois K L] in
/-- The map on small-Hilbert reciprocity quotients induced by the
concrete extension map on ideles. -/
noncomputable def smallHilbertClassFieldIdeleExtensionMap :
    (IdeleClassGroup K ⧸
        GlobalClassFields.smallHilbertClassFieldNormSubgroup) →*
      (IdeleClassGroup L ⧸
        GlobalClassFields.smallHilbertClassFieldNormSubgroup) :=
  QuotientGroup.map
    GlobalClassFields.smallHilbertClassFieldNormSubgroup
    GlobalClassFields.smallHilbertClassFieldNormSubgroup
    (ideleClassExtension K L)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change
        ideleClassExtension K L
            (QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K) a) ∈
          GlobalClassFields.smallHilbertClassFieldNormSubgroup
      rw [ideleClassExtension_mk]
      exact
        ⟨IdeleGroup.extension K L a,
          IdeleGroup.extension_mem_ordinaryIdealClassSubgroup
            K L ha,
          rfl⟩)

omit [IsGalois K L] in
/-- Evaluation of the small-Hilbert idele-extension map on a quotient
representative. -/
@[simp]
theorem smallHilbertClassFieldIdeleExtensionMap_mk'
    (c : IdeleClassGroup K) :
    smallHilbertClassFieldIdeleExtensionMap K L
        (QuotientGroup.mk'
          (GlobalClassFields.smallHilbertClassFieldNormSubgroup (K := K)) c) =
      QuotientGroup.mk'
        (GlobalClassFields.smallHilbertClassFieldNormSubgroup (K := L))
        (ideleClassExtension K L c) := by
  rfl

end SmallHilbertIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FiniteLevel_FiniteParameters
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite unit parameters for standard Lubin--Tate levels

For a local field `F`, the unit parameters visible at primitive level `n + 1`
are the valuation-ring units modulo the higher principal-unit subgroup
`U^(n + 1)`.  This file records that quotient, chooses representatives, and
computes its cardinality as

`(q - 1) * q ^ n`,

where `q` is the residue-field cardinality.  The final declarations descend
the standard Lubin--Tate action on the chosen primitive point to this finite
parameter quotient.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF

variable {K : Type u} [Field K]

/-- The finite-level unit parameter space is finite. -/
noncomputable instance standardLubinTateUnitParameter_finite
    (F : LocalField.{u, v} K) (n : ℕ) :
    Finite (standardLubinTateUnitParameter F n) := by
  change Finite
    (F.valuationSubringˣ ⧸
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1))
  exact
    higherPrincipalUnitGroup.finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
      F.toCompleteDVF (n + 1)

end LubinTate

end
end


