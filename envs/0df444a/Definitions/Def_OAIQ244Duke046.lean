-- Prove2me | Definitions.Def_OAIQ244Duke046
-- name    : OAIQ244Duke046
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:59:19.014906+00:00
-- url     : https://prove2.me/theorems/e3fa3d2e-8516-4d25-b0ad-f55578e3aa81
-- title:
--   Definitions bundle OAIQ244Duke046 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 141 declarations of OpenAI's Lean: 48 definitions and 93 theorems. The definitions and types are `CyclicCohomology.H0TateUnitsIsoNormQuotient`, `GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient`, `GlobalClassFieldTheory.ClassFieldAxiom.ideleClassPowerLocalUnitSubgroup`, `GlobalClassFieldTheory.Reciprocity.finitePlaceConcreteNormUnits`, `RelativeFiniteIdeleData.toLocalData`, `RelativeFiniteSPlaceFactors`, `RelativeIdeleSPlaceFactors`, `RelativeLocalTensorDecompositionIntegralAt`, `RelativeLocalTensorDecompositionIntegralUnitAt`, `finiteAdeleRelativeTensorFamily`, `finitePlaceAbovePiMulEquiv`, `finitePlaceAbovePiRingEquiv`, `finitePlaceAdicCompletionMap`, `finitePlaceExtensionAdicCompletionMap`, `finitePlaceExtensionAdicCompletionRingEquiv`, `finitePlaceExtensionCentre`, `finitePlaceExtensionCentreIdeal`, `finitePlaceExtensionCentreInFibre`, `finitePlaceExtensionCompletionRingEquiv`, `finitePlaceExtensionEquivAbove`, `finitePlaceExtensionExponent`, `finitePlaceExtensionValuationSubring`, `finitePlaceExtensionWithAbsRingEquiv`, `finitePlaceTensorRingEquivAboveAdic`, `finitePlaceTensorUnitsEquivAboveAdic`, `infiniteCompletionProductEquivAbove`, `infiniteCompletionProductReindexAbove`, `infiniteCompletionRingProductReindexAbove`, `infinitePlaceAboveEquivExtension`, `infinitePlaceAbovePiMulEquiv`, `infinitePlaceAboveToExtension`, `infinitePlaceTensorRingEquivAbove`, `infinitePlaceTensorUnitsEquivAbove`, `integralTensorBadPlaces`, `integralTensorComparisonBadPlaces`, `principalLocalNormQuotientMap`, `relativeFiniteTensorPiMulEquiv`, `relativeFiniteTensorPiRingEquiv`, `relativeIdeleLocalTensorDecompositionSupport`, `relativeIdeleLocalTensorDecompositionSupportedSubgroup` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_AdeleBaseChange`, `AlgebraicNumberTheory_Adele_FiniteRestrictedProductBaseChange`, `AlgebraicNumberTheory_Adele_IntegralLocalFactor`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_IdeleSupport`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_LocalTensorDecomposition`, `AlgebraicNumberTheory_Completion_AdicCompletionComparison`, `AlgebraicNumberTheory_Completion_AdicCompletionMap`, `AlgebraicNumberTheory_Completion_Comparison`, `AlgebraicNumberTheory_Completion_ExtensionIndex`, `AlgebraicNumberTheory_Idele_BaseChange`, `AlgebraicNumberTheory_Idele_Extension_NormLocalOrder`, `AlgebraicNumberTheory_Idele_NormApproximation_FinitePlaces`, `AlgebraicNumberTheory_Idele_Relative_SPlaces`, `Cyclic_TateH0_Main`, `Cyclic_TateH0_NormImage`, `GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_ArchimedeanPowerIndex`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke037`, `OAIQ244Duke038` and `OAIQ244Duke039` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke053`, `OAIQ244Duke054`, `OAIQ244Duke055`, `OAIQ244Duke056`, `OAIQ244Duke057`, `OAIQ244Duke058`, `OAIQ244Duke059` and `OAIQ244Duke060`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.ModEq
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
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
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
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation
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
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
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
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
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
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Definitions.Def_OAIQ244Duke037
import Definitions.Def_OAIQ244Duke038
import Definitions.Def_OAIQ244Duke039

section
-- module Solutions.OAIQ244_DUKE.Cyclic_TateH0_NormImage
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `CyclicCohomology.TateH0.NormImage` Lean module. -/

namespace CyclicCohomology

open LocalFieldTheory
open CategoryTheory

noncomputable section

universe u

/-- The additive norm subgroup is the kernel of the norm-quotient map. -/
lemma additiveNormSubgroup_eq_ker_quotient_map (K L : Type u)
    [Field K] [Field L] [Algebra K L] :
    additiveNormSubgroup K L =
      (MonoidHom.toAdditive (normClass K L)).ker := by
  ext x
  change Additive.toMul x ∈ localNormSubgroup K L ↔
    Additive.ofMul (normClass K L (Additive.toMul x)) = 0
  constructor
  · intro hx
    exact congrArg Additive.ofMul
      ((normClass_eq_one_iff K L (Additive.toMul x)).mpr
        (MonoidHom.mem_range.mp hx))
  · intro hx
    exact MonoidHom.mem_range.mpr
      ((normClass_eq_one_iff K L (Additive.toMul x)).mp
        (Additive.ofMul.injective hx))

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_TateH0_Main
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Degree-zero Tate cohomology and the norm quotient

This module identifies degree-zero Tate cohomology of the multiplicative group
of a finite Galois extension with the corresponding field norm quotient.
-/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

/-- The canonical comparison between mathlib's degree-zero Tate cohomology of
`Lˣ` and the field norm quotient `Kˣ / N_{L/K}(Lˣ)` for a finite Galois
extension. -/
def H0TateUnitsIsoNormQuotient (K L : Type)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    CategoryTheory.Iso (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0)
      (ModuleCat.of Int (Additive (NormQuotient K L))) := by
  letI := AlgEquiv.fintype K L
  let eInv :
      (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) ≃ₗ[Int]
        (Additive Kˣ ⧸ (additiveNormSubgroup K L).toIntSubmodule) :=
    Submodule.Quotient.equiv
      (unitsTateH0NormSubmodule K L)
      ((additiveNormSubgroup K L).toIntSubmodule)
      (invariantsUnitsEquivBaseUnits K L)
      (invariantsUnitsEquivBaseUnits_map_tateNormSubmodule K L)
  let eNorm :
      (Additive Kˣ ⧸ (additiveNormSubgroup K L).toIntSubmodule) ≃+
        Additive (NormQuotient K L) :=
    (QuotientAddGroup.quotientAddEquivOfEq
        (additiveNormSubgroup_eq_ker_quotient_map K L)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (MonoidHom.toAdditive (normClass K L)) (by
          change Function.Surjective
            (QuotientGroup.mk' (localNormSubgroup K L))
          exact QuotientGroup.mk'_surjective _))
  exact tateUnitsH0IsoInvariantsQuotient K L ≪≫
    eInv.toModuleIso ≪≫ eNorm.toIntLinearEquiv.toModuleIso

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormApproximation_FinitePlaces
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Weak approximation for actual local norm quotients

For a finite Galois extension `L / K` and a finite set `S` of finite
places of `K`, this file chooses an actual extension of every `v ∈ S`,
forms the corresponding algebraic localization `L_w / K_v`, and
transports its local norm subgroup to mathlib's concrete adic
completion.  These transported norm subgroups are open.  Multiplicative
weak approximation therefore gives a surjection

`Kˣ → ∏ v ∈ S, K_vˣ / N(L_wˣ)`.

All choices are made from the extension theorem for absolute values;
none of the local conclusions is included as input data.
-/

open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain

noncomputable section

open LocalClassFieldTheory


open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The diagonal map from global units to the chosen finite family of
actual local norm quotients. -/
noncomputable def principalLocalNormQuotientMap
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Kˣ →*
      (∀ v : ↥S,
        ChosenFinitePlaceNormQuotient
          (K := K) (L := L) v.1) :=
  IdeleGroup.principalLocalQuotientMap S
    (fun v ↦ chosenFinitePlaceLocalNormSubgroup
      (K := K) (L := L) v.1)

omit [FiniteDimensional K L] in
@[simp]
theorem principalLocalNormQuotientMap_apply
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : Kˣ) (v : ↥S) :
    principalLocalNormQuotientMap
        (K := K) (L := L) S x v =
      QuotientGroup.mk'
        (chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v.1)
        ((IdeleGroup.principalIdele K x).2 v.1) :=
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceLocalTensorDecompositionComponentRingHom_apply _root_.finitePlaceLocalTensorDecompositionComponent_add _root_.finitePlaceLocalTensorDecompositionComponent_tmul _root_.finitePlaceLocalTensorDecompositionComponent_zero _root_.finitePlaceLocalTensorDecompositionUnitsComponent_coe _root_.finitePlaceLocalTensorDecompositionUnitsEquiv_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.relativeAdeleCoefficientLinearEquiv_apply _root_.relativeAdeleCoefficient_ofCoefficients _root_.relativeAdeleFiniteComponent_basis_repr _root_.relativeAdeleInfiniteComponent_basis_repr _root_.relativeLocalAdeleCoefficient_finite _root_.relativeLocalAdeleCoefficient_infinite _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.scaledRelativeBasisDiscriminantInteger_coe
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

/-- The tensor control element is nonzero. -/
theorem integralTensorControlElement_ne_zero :
    integralTensorControlElement
      (K := K) (L := L) ≠ 0 :=
  mul_ne_zero
    (relativeBasisIntegralScaleInRingOfIntegers_ne_zero
      (K := K) (L := L))
    (scaledRelativeIntegerLatticeAnnihilator_ne_zero
      (K := K) (L := L))

/-- The tensor control ideal is nontrivial. -/
theorem integralTensorControlIdeal_ne_bot :
    integralTensorControlIdeal
      (K := K) (L := L) ≠ ⊥ := by
  rw [integralTensorControlIdeal,
    ne_eq, Ideal.span_singleton_eq_bot]
  exact integralTensorControlElement_ne_zero
    (K := K) (L := L)

/-- The actual finite set of primes at which either the basis scaling
or the lattice index can fail to be invertible. -/
noncomputable def integralTensorBadPlaces :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors
    (integralTensorControlIdeal_ne_bot
      (K := K) (L := L))).toFinset

/-- Membership in the finite bad-place set is ideal membership. -/

@[simp]
theorem mem_integralTensorBadPlaces_iff
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ integralTensorBadPlaces
        (K := K) (L := L) ↔
      w.asIdeal ∣
        integralTensorControlIdeal
          (K := K) (L := L) :=
  Set.Finite.mem_toFinset
    (Ideal.finite_factors
      (integralTensorControlIdeal_ne_bot
        (K := K) (L := L)))

/-- Outside the bad set the common control element is not in the
corresponding height-one prime. -/
theorem integralTensorControlElement_not_mem_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L)) :
    integralTensorControlElement
        (K := K) (L := L) ∉ w.asIdeal := by
  intro hmem
  apply hw
  rw [mem_integralTensorBadPlaces_iff,
    integralTensorControlIdeal,
    Ideal.dvd_span_singleton]
  exact hmem

/-- The initial integer scale is also invertible away from the bad
set. -/
theorem relativeBasisIntegralScale_not_mem_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L)) :
    relativeBasisIntegralScaleInRingOfIntegers
        (K := K) (L := L) ∉ w.asIdeal := by
  intro hmem
  exact
    integralTensorControlElement_not_mem_of_notMem
      (K := K) (L := L) w hw
      (w.asIdeal.mul_mem_right
        (scaledRelativeIntegerLatticeAnnihilator
          (K := K) (L := L)) hmem)

/-- Away from the bad set, the original (unscaled) relative basis is
integral for every extension of the corresponding finite absolute
value to `L`. -/
theorem relativeExtensionBasis_absoluteValue_le_one_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    wL.1
      (relativeExtensionBasis
        (K := K) (L := L) i) ≤ 1 := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K w
  have hdnot :
      relativeBasisIntegralScaleInRingOfIntegers
          (K := K) (L := L) ∉ w.asIdeal :=
    relativeBasisIntegralScale_not_mem_of_notMem
      (K := K) (L := L) w hw
  have hnorm :
      ‖FinitePlace.embedding w
        (algebraMap (𝓞 K) K
          (relativeBasisIntegralScaleInRingOfIntegers
            (K := K) (L := L)))‖ = 1 :=
    (FinitePlace.norm_eq_one_iff_notMem
      (R := 𝓞 K) K w
      (relativeBasisIntegralScaleInRingOfIntegers
        (K := K) (L := L))).2 hdnot
  have hvscaleInteger :
      vK
        (algebraMap (𝓞 K) K
          (relativeBasisIntegralScaleInRingOfIntegers
            (K := K) (L := L))) = 1 := by
    simpa [vK, FinitePlace.norm_embedding] using hnorm
  have hscaleField :
      relativeBasisIntegralScaleInK
          (K := K) (L := L) =
        algebraMap (𝓞 K) K
          (relativeBasisIntegralScaleInRingOfIntegers
            (K := K) (L := L)) := by
    simp [relativeBasisIntegralScaleInK,
      relativeBasisIntegralScaleInRingOfIntegers]
  have hvscale :
      vK
        (relativeBasisIntegralScaleInK
          (K := K) (L := L)) = 1 := by
    rw [hscaleField]
    exact hvscaleInteger
  have hwscale :
      wL.1
        (algebraMap K L
          (relativeBasisIntegralScaleInK
            (K := K) (L := L))) = 1 := by
    rw [wL.2]
    exact hvscale
  have hscaled :=
    scaledRelativeExtensionBasis_absoluteValue_le_one
      (K := K) (L := L) vK
      (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
        K w) wL i
  rw [scaledRelativeExtensionBasis_apply,
    Algebra.smul_def, map_mul, hwscale, one_mul] at hscaled
  exact hscaled
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_LocalTensorDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceLocalTensorDecompositionComponentRingHom_apply _root_.finitePlaceLocalTensorDecompositionComponent_add _root_.finitePlaceLocalTensorDecompositionComponent_zero _root_.finitePlaceLocalTensorDecompositionUnitsComponent_coe _root_.finitePlaceLocalTensorDecompositionUnitsEquiv_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.relativeAdeleCoefficientLinearEquiv_apply _root_.relativeAdeleCoefficient_ofCoefficients _root_.relativeAdeleFiniteComponent_basis_repr _root_.relativeAdeleInfiniteComponent_basis_repr _root_.relativeLocalAdeleCoefficient_finite _root_.relativeLocalAdeleCoefficient_infinite _root_.restrictAbsoluteValueExtensionToIntermediate_apply
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

/-- Integrality in the actual product of completion valuation rings
on the local tensor-product side. -/
def RelativeLocalTensorDecompositionIntegralAt
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L) : Prop :=
  ∀ wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L,
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL x ∈
      absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          (NumberField.HeightOneSpectrum.adicAbv K w)
          (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
            K w) wL)

/-- A tensor unit is valuation-integral when every completion
component of it and of its inverse is in the corresponding valuation
ring. -/
def RelativeLocalTensorDecompositionIntegralUnitAt
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ) : Prop :=
  RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w
      (x : w.adicCompletion K ⊗[K] L) ∧
    RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w
      ((x⁻¹ : (w.adicCompletion K ⊗[K] L)ˣ) :
        w.adicCompletion K ⊗[K] L)

/-- The finite set controlling both the integral lattice and the
inverse discriminant needed for the Cramer-rule converse. -/
noncomputable def integralTensorComparisonBadPlaces :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact
    integralTensorBadPlaces (K := K) (L := L) ∪
      scaledRelativeBasisDiscriminantBadPlaces
        (K := K) (L := L)

/-- Membership in the combined comparison bad-place set is componentwise. -/

@[simp]
theorem mem_integralTensorComparisonBadPlaces_iff
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ integralTensorComparisonBadPlaces
        (K := K) (L := L) ↔
      w ∈ integralTensorBadPlaces (K := K) (L := L) ∨
        w ∈ scaledRelativeBasisDiscriminantBadPlaces
          (K := K) (L := L) := by
  simp [integralTensorComparisonBadPlaces]

omit [NumberField L] [FiniteDimensional K L] in
/-- A coefficient in the concrete base valuation ring maps to the
valuation ring of every completion above it. -/
theorem finitePlaceLocalTensorDecomposition_coefficient_mem_integers
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L)
    (c : w.adicCompletionIntegers K) :
    AbsoluteValue.completionMap
        (NumberField.HeightOneSpectrum.adicAbv K w)
        wL.1 wL.2
        ((relativeFinitePlaceCompletionAlgEquiv w).symm
          (c : w.adicCompletion K)) ∈
      absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          (NumberField.HeightOneSpectrum.adicAbv K w)
          (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
            K w) wL) := by
  rw [mem_absoluteValueCompletionIntegers_iff]
  calc
    ‖AbsoluteValue.completionMap
        (NumberField.HeightOneSpectrum.adicAbv K w)
        wL.1 wL.2
        ((relativeFinitePlaceCompletionAlgEquiv w).symm
          (c : w.adicCompletion K))‖ =
      ‖(relativeFinitePlaceCompletionAlgEquiv w).symm
          (c : w.adicCompletion K)‖ :=
        (AbsoluteValue.completionMap_isometry
          (NumberField.HeightOneSpectrum.adicAbv K w)
          wL.1 wL.2).norm_map_of_map_zero
            (map_zero
              (AbsoluteValue.completionMap
                (NumberField.HeightOneSpectrum.adicAbv K w)
                wL.1 wL.2)) _
    _ = ‖(c : w.adicCompletion K)‖ :=
      relativeFinitePlaceCompletionAlgEquiv_symm_norm
        (K := K) w (c : w.adicCompletion K)
    _ ≤ 1 :=
      norm_le_one_of_mem_adicCompletionIntegers
        (K := K) w c.property

/-- Away from the bad set, every chosen relative basis vector maps to
the valuation ring in each local completion factor. -/
theorem finitePlaceLocalTensorDecomposition_basis_mem_integers_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorBadPlaces
      (K := K) (L := L))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K w) L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    AbsoluteValue.toCompletion wL.1
        (relativeExtensionBasis
          (K := K) (L := L) i) ∈
      absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          (NumberField.HeightOneSpectrum.adicAbv K w)
          (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv
            K w) wL) := by
  rw [mem_absoluteValueCompletionIntegers_iff]
  simpa [AbsoluteValue.toCompletion_apply,
    WithAbs.norm_eq_apply_ofAbs] using
      relativeExtensionBasis_absoluteValue_le_one_of_notMem
        (K := K) (L := L) w hw wL i

/-- Local tensor integrality forces the coordinates in the
base-changed scaled basis to be integral.  The proof takes traces
componentwise and recovers the coordinates by Cramer's rule. -/
theorem scaledRelativeTensorCoordinates_isIntegral_of_localTensorDecompositionIntegral
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ scaledRelativeBasisDiscriminantBadPlaces
      (K := K) (L := L))
    {x : w.adicCompletion K ⊗[K] L}
    (hx : RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w x) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K w
    let xA :=
      (relativeFinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) w).symm x
    let bA :=
      Algebra.TensorProduct.basis vK.Completion
        (scaledRelativeExtensionBasis (K := K) (L := L))
    ∀ i, IsIntegral (absoluteValueCompletionIntegers vK
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K w))
      (bA.equivFun xA i) := by
  classical
  let vK := NumberField.HeightOneSpectrum.adicAbv K w
  let hvK : IsNonarchimedean (vK : K → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K w
  let hvK0 : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  let : Fintype (AbsoluteValueExtension vK L) :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK0
  let : ∀ wL : AbsoluteValueExtension vK L,
      Algebra vK.Completion wL.1.Completion :=
    fun wL => AbsoluteValue.completionAlgebra vK wL.1 wL.2
  let : ∀ wL : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion wL.1.Completion :=
    fun wL => completionModuleFinite vK hvK0 wL
  let : ∀ wL : AbsoluteValueExtension vK L,
      Module.Free vK.Completion wL.1.Completion :=
    fun wL => Module.Free.of_divisionRing
      vK.Completion wL.1.Completion
  let xA : vK.Completion ⊗[K] L :=
    (relativeFinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w).symm x
  let bA :=
    Algebra.TensorProduct.basis vK.Completion
      (scaledRelativeExtensionBasis (K := K) (L := L))
  have hxA :
      ∀ wL : AbsoluteValueExtension vK L,
        completionTensorDecomposition_left
            (K := K) (L := L) vK hvK0 xA wL ∈
          absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean vK hvK wL) := by
    intro wL
    simpa [xA, vK, hvK, hvK0,
      finitePlaceLocalTensorDecompositionComponent] using hx wL
  have hbA :
      ∀ (i : RelativeAdeleBasisIndex (K := K) (L := L))
        (wL : AbsoluteValueExtension vK L),
        completionTensorDecomposition_left
            (K := K) (L := L) vK hvK0 (bA i) wL ∈
          absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean vK hvK wL) := by
    intro i wL
    have hbAi :
        bA i =
          1 ⊗ₜ[K]
            scaledRelativeExtensionBasis (K := K) (L := L) i := by
      simp [bA, Algebra.TensorProduct.basis_apply]
    rw [hbAi]
    rw [completionTensorDecomposition_left_tmul_apply]
    simp only [map_one, one_mul]
    rw [mem_absoluteValueCompletionIntegers_iff]
    simpa [AbsoluteValue.toCompletionAlgHom,
      AbsoluteValue.toCompletion_apply,
      WithAbs.norm_eq_apply_ofAbs] using
        scaledRelativeExtensionBasis_absoluteValue_le_one
          (K := K) (L := L) vK hvK wL i
  have hM :
      ∀ i j : RelativeAdeleBasisIndex (K := K) (L := L),
        IsIntegral (absoluteValueCompletionIntegers vK hvK)
          (Algebra.trace vK.Completion
            (vK.Completion ⊗[K] L) (bA i * bA j)) := by
    intro i j
    apply isIntegral_trace_tensor_of_components
      (K := K) (L := L) vK hvK hvK0
    intro wL
    rw [map_mul, Pi.mul_apply]
    change _ ∈
      (absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          vK hvK wL)).toSubring
    exact
      (absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          vK hvK wL)).toSubring.mul_mem (hbA i wL) (hbA j wL)
  have ht :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        IsIntegral (absoluteValueCompletionIntegers vK hvK)
          (Algebra.trace vK.Completion
            (vK.Completion ⊗[K] L) (xA * bA i)) := by
    intro i
    apply isIntegral_trace_tensor_of_components
      (K := K) (L := L) vK hvK hvK0
    intro wL
    rw [map_mul, Pi.mul_apply]
    change _ ∈
      (absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          vK hvK wL)).toSubring
    exact
      (absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          vK hvK wL)).toSubring.mul_mem (hxA wL) (hbA i wL)
  have hdiscInv :
      IsIntegral (absoluteValueCompletionIntegers vK hvK)
        (Algebra.discr vK.Completion bA)⁻¹ := by
    rw [discr_tensorProduct_basis]
    apply (IsIntegrallyClosedIn.isIntegral_iff).2
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [mem_absoluteValueCompletionIntegers_iff]
    have hdabs :=
      adicAbv_scaledRelativeBasisDiscriminant_eq_one_of_notMem
        (K := K) (L := L) w hw
    have hdnorm :
        ‖algebraMap K vK.Completion
          (Algebra.discr K
            (scaledRelativeExtensionBasis (K := K) (L := L)))‖ = 1 := by
      calc
        ‖algebraMap K vK.Completion
            (Algebra.discr K
              (scaledRelativeExtensionBasis (K := K) (L := L)))‖ =
            vK (Algebra.discr K
              (scaledRelativeExtensionBasis (K := K) (L := L))) := by
              exact AbsoluteValue.completionAbsoluteValue_coe _ _
        _ = 1 := hdabs
    change AbsoluteValue.completionAbsoluteValue vK
      ((algebraMap K vK.Completion
        (Algebra.discr K
          (scaledRelativeExtensionBasis (K := K) (L := L))))⁻¹) ≤ 1
    rw [map_inv₀]
    change
      ‖algebraMap K vK.Completion
        (Algebra.discr K
          (scaledRelativeExtensionBasis (K := K) (L := L)))‖⁻¹ ≤ 1
    rw [hdnorm, inv_one]
  have hdiscne :
      Algebra.discr vK.Completion bA ≠ 0 := by
    rw [discr_tensorProduct_basis]
    exact (algebraMap K vK.Completion).injective.ne
      (Algebra.discr_not_zero_of_basis K
        (scaledRelativeExtensionBasis (K := K) (L := L)))
  change ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
    IsIntegral (absoluteValueCompletionIntegers vK hvK)
      (bA.equivFun xA i)
  intro i
  exact basis_coord_isIntegral_of_integral_traces
    bA hM ht hdiscInv hdiscne i

/-- The concrete tensor comparison sends a scaled-basis summand to
the corresponding original-basis summand, with the global scale
absorbed into its coefficient. -/
theorem relativeFinitePlaceLocalTensorAlgEquiv_scaled_basis_smul
    (w : HeightOneSpectrum (𝓞 K))
    (a :
      (NumberField.HeightOneSpectrum.adicAbv K w).Completion)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    relativeFinitePlaceLocalTensorAlgEquiv
        (K := K) (L := L) w
        (a •
          Algebra.TensorProduct.basis
            (NumberField.HeightOneSpectrum.adicAbv K w).Completion
            (scaledRelativeExtensionBasis (K := K) (L := L)) i) =
      relativeFinitePlaceCompletionAlgEquiv w
          (a * algebraMap K
            (NumberField.HeightOneSpectrum.adicAbv K w).Completion
            (relativeBasisIntegralScaleInK
              (K := K) (L := L))) ⊗ₜ[K]
        relativeExtensionBasis (K := K) (L := L) i := by
  simp [relativeFinitePlaceLocalTensorAlgEquiv,
    Algebra.TensorProduct.basis_apply,
    scaledRelativeExtensionBasis_apply,
    Algebra.smul_def, mul_comm]
  simpa [Algebra.smul_def] using
    (TensorProduct.smul_tmul
      (relativeBasisIntegralScaleInK (K := K) (L := L))
      (relativeFinitePlaceCompletionAlgEquiv w a)
      (relativeExtensionBasis (K := K) (L := L) i)).symm

/-- Outside the lattice and discriminant bad places, integrality of
all local tensor components implies integrality in the original
relative basis. -/
theorem localTensorDecompositionIntegral_imp_relativeBasisIntegralAt_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorComparisonBadPlaces
      (K := K) (L := L))
    {x : w.adicCompletion K ⊗[K] L}
    (hx : RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w x) :
    RelativeBasisIntegralAt (K := K) (L := L) w x := by
  classical
  have hwdisc :
      w ∉ scaledRelativeBasisDiscriminantBadPlaces
        (K := K) (L := L) := by
    intro hw'
    exact hw (by
      simp [integralTensorComparisonBadPlaces, hw'])
  let vK := NumberField.HeightOneSpectrum.adicAbv K w
  let hvK : IsNonarchimedean (vK : K → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K w
  let xA : vK.Completion ⊗[K] L :=
    (relativeFinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w).symm x
  let bA :=
    Algebra.TensorProduct.basis vK.Completion
      (scaledRelativeExtensionBasis (K := K) (L := L))
  have hscaled :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        IsIntegral (absoluteValueCompletionIntegers vK hvK)
          (bA.equivFun xA i) := by
    simpa [vK, hvK, xA, bA] using
      scaledRelativeTensorCoordinates_isIntegral_of_localTensorDecompositionIntegral
        (K := K) (L := L) w hwdisc hx
  have hscaledNorm :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        ‖bA.equivFun xA i‖ ≤ 1 := by
    intro i
    obtain ⟨ci, hci⟩ :=
      (IsIntegrallyClosedIn.isIntegral_iff).1 (hscaled i)
    rw [← hci]
    exact ci.property
  have hscaleIntegral :
      IsIntegral ℤ
        (relativeBasisIntegralScaleInK
          (K := K) (L := L)) := by
    change IsIntegral ℤ
      (algebraMap ℤ K
        (chosenRelativeBasisIntegralScale (K := K) (L := L)))
    exact isIntegral_algebraMap
  have hscaleAbs :
      vK (relativeBasisIntegralScaleInK
        (K := K) (L := L)) ≤ 1 :=
    absoluteValue_le_one_of_isIntegral vK hvK hscaleIntegral
  have hscaleNorm :
      ‖algebraMap K vK.Completion
        (relativeBasisIntegralScaleInK
          (K := K) (L := L))‖ ≤ 1 := by
    calc
      ‖algebraMap K vK.Completion
          (relativeBasisIntegralScaleInK
            (K := K) (L := L))‖ =
          vK (relativeBasisIntegralScaleInK
            (K := K) (L := L)) :=
        AbsoluteValue.completionAbsoluteValue_coe _ _
      _ ≤ 1 := hscaleAbs
  let cA :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        vK.Completion :=
    fun i =>
      bA.equivFun xA i *
        algebraMap K vK.Completion
          (relativeBasisIntegralScaleInK
            (K := K) (L := L))
  have hcANorm :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        ‖cA i‖ ≤ 1 := by
    intro i
    change ‖bA.equivFun xA i *
      algebraMap K vK.Completion
        (relativeBasisIntegralScaleInK
          (K := K) (L := L))‖ ≤ 1
    rw [norm_mul]
    calc
      ‖bA.equivFun xA i‖ *
          ‖algebraMap K vK.Completion
            (relativeBasisIntegralScaleInK
              (K := K) (L := L))‖ ≤
          1 * 1 :=
        mul_le_mul (hscaledNorm i) hscaleNorm
          (norm_nonneg _) (by positivity)
      _ = 1 := one_mul 1
  have hmapNorm (y : vK.Completion) :
      ‖relativeFinitePlaceCompletionAlgEquiv w y‖ = ‖y‖ := by
    change ‖relativeFinitePlaceCompletionRingHom w y‖ = ‖y‖
    exact
      (relativeFinitePlaceCompletionRingHom_isometry w).norm_map_of_map_zero
        (map_zero (relativeFinitePlaceCompletionRingHom w)) y
  let c :
      RelativeAdeleBasisIndex (K := K) (L := L) →
        w.adicCompletionIntegers K :=
    fun i =>
      ⟨relativeFinitePlaceCompletionAlgEquiv w (cA i),
        mem_adicCompletionIntegers_of_norm_le_one w
          (by rw [hmapNorm]; exact hcANorm i)⟩
  refine ⟨c, ?_⟩
  let e :=
    relativeFinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w
  calc
    x = e xA := (e.apply_symm_apply x).symm
    _ = e (∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (bA.equivFun xA i) • bA i) :=
      congrArg e (bA.sum_repr xA).symm
    _ = ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        e ((bA.equivFun xA i) • bA i) := by
      rw [map_sum]
    _ = ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        ((c i : w.adicCompletionIntegers K) :
            w.adicCompletion K) ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [relativeFinitePlaceLocalTensorAlgEquiv_scaled_basis_smul]

/-- The same converse for tensor units, applied to the unit and its
inverse. -/
theorem localTensorDecompositionIntegralUnit_imp_relativeBasisIntegralUnitAt_of_notMem
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ integralTensorComparisonBadPlaces
      (K := K) (L := L))
    {x : (w.adicCompletion K ⊗[K] L)ˣ}
    (hx : RelativeLocalTensorDecompositionIntegralUnitAt
      (K := K) (L := L) w x) :
    RelativeBasisIntegralUnitAt (K := K) (L := L) w x :=
  ⟨localTensorDecompositionIntegral_imp_relativeBasisIntegralAt_of_notMem
      (K := K) (L := L) w hw hx.1,
    localTensorDecompositionIntegral_imp_relativeBasisIntegralAt_of_notMem
      (K := K) (L := L) w hw hx.2⟩

end LocalTensorDecompositionIntegralComparison
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_IdeleSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul _root_.relativeAdeleCoefficientLinearEquiv_apply _root_.relativeAdeleCoefficient_ofCoefficients _root_.relativeAdeleFiniteComponent_basis_repr _root_.relativeAdeleInfiniteComponent_basis_repr _root_.relativeAdeleOfCoefficients_coefficients _root_.relativeAdeleOfLocalData_finiteComponent _root_.relativeAdeleOfLocalData_infiniteComponent _root_.relativeIdeleLocalComponents_finite _root_.relativeIdeleLocalComponents_infinite _root_.relativeIdeleMulEquivLocalData_apply _root_.relativeIdeleOfLocalData_finiteComponent _root_.relativeIdeleOfLocalData_infiniteComponent _root_.relativeIdeleOfLocalData_toLocalData _root_.relativeLocalAdeleCoefficient_finite _root_.relativeLocalAdeleCoefficient_infinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite support for integral relative ideles

This module combines coefficient support with the exceptional places of the
local tensor decomposition, producing one finite set that controls integrality
of a relative idele and its inverse.
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

/-- The single finite support controlling both coefficient integrality
of a relative idele and the integral compatibility of the local tensor decomposition. -/
noncomputable def relativeIdeleLocalTensorDecompositionSupport
    (z : RelativeIdeleGroup K L) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact
    relativeIdeleCoefficientSupport
        (K := K) (L := L) z ∪
      integralTensorBadPlaces
        (K := K) (L := L)

/-- The support is exposed through this membership characterization. -/

@[simp]
theorem mem_relativeIdeleLocalTensorDecompositionSupport_iff
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ relativeIdeleLocalTensorDecompositionSupport
        (K := K) (L := L) z ↔
      w ∈ relativeIdeleCoefficientSupport
          (K := K) (L := L) z ∨
        w ∈ integralTensorBadPlaces
          (K := K) (L := L) := by
  simp [relativeIdeleLocalTensorDecompositionSupport]
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralLocalFactor
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.infinitePlace_mult_smul _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Integral finite local factors of the relative idele group

For a finite place `w` of the base field, the canonical local tensor decomposition identifies
`K_w ⊗_K L` with the product of the completions of `L` above `w`.
This file packages each projection as an actual ring homomorphism and
defines the subgroup of tensor units whose value and inverse are integral
in every completion factor.  Thus the integrality predicate used for the
restricted product is closed under all group operations for structural,
rather than coordinate-dependent, reasons.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
/-- The completion equivalence induced by conjugation preserves the
norm exactly. -/
theorem conjugateExtensionCompletionRingEquiv_norm_eq
    (vK : AbsoluteValue K ℝ)
    (wL : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (x :
      (absoluteValueExtensionConjugate
        vK wL σ).1.Completion) :
    ‖conjugateExtensionCompletionRingEquiv vK wL σ x‖ =
      ‖x‖ := by
  change ‖conjugateCompletionRingEquiv wL.1 σ x‖ = ‖x‖
  let f := (conjugateWithAbsRingEquiv wL.1 σ).toRingHom
  let h := conjugateWithAbsRingEquiv_isometry wL.1 σ
  change
    ‖UniformSpace.Completion.mapRingHom f h.continuous x‖ = ‖x‖
  exact
    (Isometry.isometry_mapRingHom h).norm_map_of_map_zero
      (map_zero (UniformSpace.Completion.mapRingHom f h.continuous)) x

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
/-- The conjugate-completion equivalence identifies the two valuation
rings. -/
theorem
    conjugateExtensionCompletionRingEquiv_mem_integers_iff
    (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ))
    (wL : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (x :
      (absoluteValueExtensionConjugate
        vK wL σ).1.Completion) :
    conjugateExtensionCompletionRingEquiv vK wL σ x ∈
        absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            vK hvK wL) ↔
      x ∈
        absoluteValueCompletionIntegers
          (absoluteValueExtensionConjugate
            vK wL σ).1
          (absoluteValueExtension_isNonarchimedean
            vK hvK
            (absoluteValueExtensionConjugate
              vK wL σ)) := by
  rw [mem_absoluteValueCompletionIntegers_iff,
    mem_absoluteValueCompletionIntegers_iff,
    conjugateExtensionCompletionRingEquiv_norm_eq]

omit [NumberField L] in
/-- Galois conjugation sends the component at `wL` to the component at
the conjugate extension, transported by the canonical completion
isometry. -/
theorem finitePlaceLocalTensorDecompositionComponent_scalarTensorConjugation
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (σ : L ≃ₐ[K] L)
    (x : w.adicCompletion K ⊗[K] L) :
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL
        (scalarTensorConjugation
          (K := K) (L := L)
          (A := w.adicCompletion K) σ x) =
      conjugateExtensionCompletionRingEquiv
        (HeightOneSpectrum.adicAbv K w) wL σ
        (finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w
          (absoluteValueExtensionConjugate
            (HeightOneSpectrum.adicAbv K w) wL σ) x) := by
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  let : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  induction x using OAI.tensorInductionOn with
  | add x y hx hy =>
      rw [map_add, finitePlaceLocalTensorDecompositionComponent_add,
        finitePlaceLocalTensorDecompositionComponent_add, map_add, hx, hy]
  | tmul a b =>
      rw [scalarTensorConjugation_tmul,
        finitePlaceLocalTensorDecompositionComponent_tmul,
        finitePlaceLocalTensorDecompositionComponent_tmul,
        map_mul]
      change
        algebraMap vK.Completion wL.1.Completion
              ((relativeFinitePlaceCompletionAlgEquiv
                (K := K) w).symm a) *
            AbsoluteValue.toCompletion wL.1 (σ b) =
          conjugateExtensionCompletionRingEquiv vK wL σ
                (algebraMap vK.Completion
                  (absoluteValueExtensionConjugate
                    vK wL σ).1.Completion
                  ((relativeFinitePlaceCompletionAlgEquiv
                    (K := K) w).symm a)) *
            conjugateExtensionCompletionRingEquiv vK wL σ
              (AbsoluteValue.toCompletion
                (absoluteValueExtensionConjugate
                  vK wL σ).1 b)
      rw [conjugateExtensionCompletionRingEquiv_algebraMap,
        conjugateExtensionCompletionRingEquiv_toCompletion]

omit [NumberField L] in
/-- Valuation-ring integrality of a tensor element is preserved by
Galois conjugation. -/
theorem relativeLocalTensorDecompositionIntegralAt_scalarTensorConjugation
    (w : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    {x : w.adicCompletion K ⊗[K] L}
    (hx : RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w x) :
    RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w
      (scalarTensorConjugation
        (K := K) (L := L)
        (A := w.adicCompletion K) σ x) := by
  intro wL
  rw [finitePlaceLocalTensorDecompositionComponent_scalarTensorConjugation]
  exact
    (conjugateExtensionCompletionRingEquiv_mem_integers_iff
      (K := K) (L := L)
      (vK := HeightOneSpectrum.adicAbv K w)
      (hvK :=
        HeightOneSpectrum.isNonarchimedean_adicAbv K w)
      (wL := wL) (σ := σ) _).2
      (hx
        (absoluteValueExtensionConjugate
          (HeightOneSpectrum.adicAbv K w) wL σ))

omit [NumberField L] in
/-- The integral tensor-unit condition is stable under the natural
Galois action. -/
theorem relativeLocalTensorDecompositionIntegralUnitAt_smul
    (w : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (x : (w.adicCompletion K ⊗[K] L)ˣ)
    (hx : RelativeLocalTensorDecompositionIntegralUnitAt
      (K := K) (L := L) w x) :
    letI := scalarTensorUnitsAction
      (K := K) (L := L)
      (A := w.adicCompletion K)
    RelativeLocalTensorDecompositionIntegralUnitAt
      (K := K) (L := L) w (σ • x) := by
  let := scalarTensorUnitsAction
    (K := K) (L := L)
    (A := w.adicCompletion K)
  constructor
  · change
      RelativeLocalTensorDecompositionIntegralAt
        (K := K) (L := L) w
        (↑(σ • x) :
          w.adicCompletion K ⊗[K] L)
    rw [scalarTensorUnitsAction_coe]
    exact
      relativeLocalTensorDecompositionIntegralAt_scalarTensorConjugation
        (K := K) (L := L) w σ hx.1
  · change
      RelativeLocalTensorDecompositionIntegralAt
        (K := K) (L := L) w
        (↑((σ • x)⁻¹) :
          w.adicCompletion K ⊗[K] L)
    rw [← smul_inv', scalarTensorUnitsAction_coe]
    exact
      relativeLocalTensorDecompositionIntegralAt_scalarTensorConjugation
        (K := K) (L := L) w σ hx.2

omit [NumberField L] in
/-- Integrality of a tensor unit is exactly membership of every
relative-tensor component in the unit subgroup of its valuation ring. -/
theorem relativeLocalTensorDecompositionIntegralUnitAt_iff
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ) :
    RelativeLocalTensorDecompositionIntegralUnitAt
        (K := K) (L := L) w x ↔
      ∀ wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L,
        finitePlaceLocalTensorDecompositionUnitsComponent
            (K := K) (L := L) w wL x ∈
          (absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean
              (HeightOneSpectrum.adicAbv K w)
              (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
              wL)).units := by
  constructor
  · rintro ⟨hx, hxinv⟩ wL
    exact ⟨hx wL, by
      change
        finitePlaceLocalTensorDecompositionComponent
            (K := K) (L := L) w wL
            (↑(x⁻¹) :
              w.adicCompletion K ⊗[K] L) ∈
          absoluteValueCompletionIntegers wL.1
            (absoluteValueExtension_isNonarchimedean
              (HeightOneSpectrum.adicAbv K w)
              (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
              wL)
      exact hxinv wL⟩
  · intro hx
    constructor
    · intro wL
      exact (hx wL).1
    · intro wL
      exact (hx wL).2

/-- The actual integral-unit subgroup in a finite local tensor factor. -/
noncomputable def relativeLocalTensorDecompositionIntegralUnitSubgroup
    (w : HeightOneSpectrum (𝓞 K)) :
    Subgroup (w.adicCompletion K ⊗[K] L)ˣ :=
  Subgroup.comap
    (MonoidHom.pi
      (fun wL : AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L =>
        finitePlaceLocalTensorDecompositionUnitsComponent
          (K := K) (L := L) w wL))
    (Subgroup.pi Set.univ fun wL =>
      (absoluteValueCompletionIntegers wL.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K w)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K w)
          wL)).units)

omit [NumberField L] in
/-- Membership in the integral tensor-unit subgroup is exactly the
pointwise valuation-ring integrality condition. -/
@[simp]
theorem mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ) :
    x ∈ relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w ↔
      RelativeLocalTensorDecompositionIntegralUnitAt
        (K := K) (L := L) w x := by
  rw [relativeLocalTensorDecompositionIntegralUnitAt_iff]
  simp only [relativeLocalTensorDecompositionIntegralUnitSubgroup,
    Subgroup.mem_comap, MonoidHom.pi_apply, Subgroup.mem_pi,
    Set.mem_univ, forall_const]

/-- The restricted Galois action on the integral tensor-unit
subgroup. -/
@[implicit_reducible]
noncomputable def
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction
    (w : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w) := by
  letI := scalarTensorUnitsAction
    (K := K) (L := L)
    (A := w.adicCompletion K)
  exact
    { smul := fun σ x =>
        ⟨σ • (x :
            (w.adicCompletion K ⊗[K] L)ˣ),
          by
            rw [mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff]
            have hx :
                RelativeLocalTensorDecompositionIntegralUnitAt
                  (K := K) (L := L) w
                  (x : (w.adicCompletion K ⊗[K] L)ˣ) :=
              (mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
                (K := K) (L := L) w x).1 x.property
            exact
              relativeLocalTensorDecompositionIntegralUnitAt_smul
                (K := K) (L := L) w σ x hx⟩
      one_smul := by
        intro x
        apply Subtype.ext
        change
          (1 : L ≃ₐ[K] L) •
              (x : (w.adicCompletion K ⊗[K] L)ˣ) =
            (x : (w.adicCompletion K ⊗[K] L)ˣ)
        exact one_smul (L ≃ₐ[K] L) _
      mul_smul := by
        intro σ τ x
        apply Subtype.ext
        exact mul_smul σ τ
          (x : (w.adicCompletion K ⊗[K] L)ˣ)
      smul_one := by
        intro σ
        apply Subtype.ext
        change
          σ • (1 : (w.adicCompletion K ⊗[K] L)ˣ) = 1
        exact smul_one σ
      smul_mul := by
        intro σ x y
        apply Subtype.ext
        exact smul_mul' σ
          (x : (w.adicCompletion K ⊗[K] L)ˣ)
          (y : (w.adicCompletion K ⊗[K] L)ˣ) }

omit [NumberField L] in
@[simp]
theorem
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction_coe
    (w : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (x : relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) w) :
    letI :=
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w
    ((σ • x :
        relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w) :
      (w.adicCompletion K ⊗[K] L)ˣ) =
      letI := scalarTensorUnitsAction
        (K := K) (L := L)
        (A := w.adicCompletion K)
      σ •
        (x : (w.adicCompletion K ⊗[K] L)ˣ) :=
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_ExtensionIndex
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
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

open AlgebraicNumberTheory.Valuations

universe u v w

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

section Centre

variable [FiniteDimensional K L]

omit [NumberField L] [FiniteDimensional K L] in
/-- Nonarchimedeanness of an exact extension of a finite
absolute value. -/
theorem finitePlaceExtension_nonarchimedean
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1 :=
  (AbsoluteValue.isNonarchimedean_iff_bounded_nat w.1).1
    (absoluteValueExtension_isNonarchimedean
      (HeightOneSpectrum.adicAbv K v)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v) w)

/-- The valuation subring of `L` cut out by an exact extension of the
normalized absolute value at `v`. -/
noncomputable def finitePlaceExtensionValuationSubring
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    ValuationSubring L :=
  absoluteValueValuationSubring w.1
    (finitePlaceExtension_nonarchimedean
      (K := K) (L := L) v w)

omit [NumberField L] [FiniteDimensional K L] in
/-- Every algebraic integer of `L` belongs to the valuation subring
defined by a finite-place extension. -/
theorem ringOfIntegers_mem_finitePlaceExtensionValuationSubring
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : 𝓞 L) :
    (x : L) ∈
      finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w := by
  rw [finitePlaceExtensionValuationSubring,
    mem_absoluteValueValuationSubring_iff]
  exact
    absoluteValue_le_one_of_isIntegral w.1
      (absoluteValueExtension_isNonarchimedean
        (HeightOneSpectrum.adicAbv K v)
        (HeightOneSpectrum.isNonarchimedean_adicAbv K v) w)
      x.property

/-- The canonical map from algebraic integers to the valuation subring
of an exact finite-place extension. -/
noncomputable def ringOfIntegersToFinitePlaceExtensionValuationSubring
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    𝓞 L →+*
      finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w :=
  RingHom.codRestrict (algebraMap (𝓞 L) L)
    (finitePlaceExtensionValuationSubring
      (K := K) (L := L) v w).toSubring
    (ringOfIntegers_mem_finitePlaceExtensionValuationSubring
      (K := K) (L := L) v w)

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem ringOfIntegersToFinitePlaceExtensionValuationSubring_coe
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : 𝓞 L) :
    ((ringOfIntegersToFinitePlaceExtensionValuationSubring
        (K := K) (L := L) v w x :
      finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w) : L) = (x : L) :=
  rfl

/-- The centre in `𝓞 L` of an exact extension of the absolute value at
`v`. -/
noncomputable def finitePlaceExtensionCentreIdeal
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    Ideal (𝓞 L) :=
  (IsLocalRing.maximalIdeal
      (finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w)).comap
    (ringOfIntegersToFinitePlaceExtensionValuationSubring
      (K := K) (L := L) v w)

omit [NumberField L] [FiniteDimensional K L] in
/-- Membership in the centre is the strict-unit-ball condition. -/
theorem mem_finitePlaceExtensionCentreIdeal_iff
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : 𝓞 L) :
    x ∈ finitePlaceExtensionCentreIdeal
        (K := K) (L := L) v w ↔
      w.1 (x : L) < 1 := by
  let A :=
    finitePlaceExtensionValuationSubring
      (K := K) (L := L) v w
  let f :=
    ringOfIntegersToFinitePlaceExtensionValuationSubring
      (K := K) (L := L) v w
  change
    f x ∈ IsLocalRing.maximalIdeal A ↔
      w.1 (((f x : A) : L)) < 1
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact
    not_isUnit_iff_abs_lt_one_of_mem_iff_le_one
      w.1 A
      (fun y => by
        change
          y ∈ finitePlaceExtensionValuationSubring
              (K := K) (L := L) v w ↔
            w.1 y ≤ 1
        rw [finitePlaceExtensionValuationSubring,
          mem_absoluteValueValuationSubring_iff])
      (f x)

omit [NumberField L] [FiniteDimensional K L] in
theorem finitePlaceExtensionCentreIdeal_isPrime
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    (finitePlaceExtensionCentreIdeal
      (K := K) (L := L) v w).IsPrime := by
  unfold finitePlaceExtensionCentreIdeal
  exact Ideal.comap_isPrime _ _

omit [NumberField L] [FiniteDimensional K L] in
/-- The centre contracts to the original finite place. -/
theorem finitePlaceExtensionCentreIdeal_under
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    (finitePlaceExtensionCentreIdeal
        (K := K) (L := L) v w).under (𝓞 K) =
      v.asIdeal := by
  ext x
  change
    algebraMap (𝓞 K) (𝓞 L) x ∈
        finitePlaceExtensionCentreIdeal
          (K := K) (L := L) v w ↔
      x ∈ v.asIdeal
  rw [mem_finitePlaceExtensionCentreIdeal_iff]
  have hcoe :
      ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) =
        algebraMap K L (x : K) := by
    rfl
  rw [hcoe, w.2]
  rw [← FinitePlace.norm_embedding]
  exact FinitePlace.norm_lt_one_iff_mem (K := K) v x

omit [NumberField L] [FiniteDimensional K L] in
theorem finitePlaceExtensionCentreIdeal_ne_bot
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    finitePlaceExtensionCentreIdeal
        (K := K) (L := L) v w ≠ ⊥ := by
  intro hbot
  apply v.ne_bot
  rw [← finitePlaceExtensionCentreIdeal_under
    (K := K) (L := L) v w, hbot]
  simp

/-- The finite place of `L` centred at an exact extension of the
absolute value at `v`. -/
noncomputable def finitePlaceExtensionCentre
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    HeightOneSpectrum (𝓞 L) where
  asIdeal :=
    finitePlaceExtensionCentreIdeal
      (K := K) (L := L) v w
  isPrime :=
    finitePlaceExtensionCentreIdeal_isPrime
      (K := K) (L := L) v w
  ne_bot :=
    finitePlaceExtensionCentreIdeal_ne_bot
      (K := K) (L := L) v w

omit [NumberField L] [FiniteDimensional K L] in
@[simp]
theorem finitePlaceExtensionCentre_asIdeal
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    (finitePlaceExtensionCentre
      (K := K) (L := L) v w).asIdeal =
      finitePlaceExtensionCentreIdeal
        (K := K) (L := L) v w :=
  rfl

omit [FiniteDimensional K L] in
@[simp]
theorem finitePlaceBelow_finitePlaceExtensionCentre
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    finitePlaceBelow (K := K)
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) =
      v := by
  apply HeightOneSpectrum.ext
  exact
    finitePlaceExtensionCentreIdeal_under
      (K := K) (L := L) v w

omit [FiniteDimensional K L] in
/-- The centre of an exact extension of the normalized absolute value
lies over the original finite place. -/
theorem finitePlaceExtensionCentre_liesOver
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    (finitePlaceExtensionCentre
      (K := K) (L := L) v w).asIdeal.LiesOver v.asIdeal := by
  constructor
  exact congrArg HeightOneSpectrum.asIdeal
    (finitePlaceBelow_finitePlaceExtensionCentre
      (K := K) (L := L) v w).symm

omit [FiniteDimensional K L] in
/-- The valuation subring defined by an exact extension is the
localization of `𝓞 L` at its centre. -/
theorem finitePlaceExtensionValuationSubring_eq_localization
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w =
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w).valuationSubringAtPrime L := by
  let P :=
    finitePlaceExtensionCentreIdeal
      (K := K) (L := L) v w
  let : P.IsPrime :=
    finitePlaceExtensionCentreIdeal_isPrime
      (K := K) (L := L) v w
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) v w
  let V := W.valuationSubringAtPrime L
  let A :=
    finitePlaceExtensionValuationSubring
      (K := K) (L := L) v w
  have hVA : V ≤ A := by
    rintro x ⟨a, s, hs, rfl⟩
    have haA : (a : L) ∈ A :=
      ringOfIntegers_mem_finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w a
    have hsA : (s : L) ∈ A :=
      ringOfIntegers_mem_finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w s
    have haLe : w.1 (a : L) ≤ 1 := by
      change (a : L) ∈
        finitePlaceExtensionValuationSubring
          (K := K) (L := L) v w at haA
      rw [finitePlaceExtensionValuationSubring,
        mem_absoluteValueValuationSubring_iff] at haA
      exact haA
    have hsLe : w.1 (s : L) ≤ 1 := by
      change (s : L) ∈
        finitePlaceExtensionValuationSubring
          (K := K) (L := L) v w at hsA
      rw [finitePlaceExtensionValuationSubring,
        mem_absoluteValueValuationSubring_iff] at hsA
      exact hsA
    have hsNotLt : ¬ w.1 (s : L) < 1 := by
      intro hlt
      apply hs
      exact
        (mem_finitePlaceExtensionCentreIdeal_iff
          (K := K) (L := L) v w s).2 hlt
    have hsEq : w.1 (s : L) = 1 :=
      le_antisymm hsLe (not_lt.mp hsNotLt)
    change
      (a : L) * (s : L)⁻¹ ∈
        finitePlaceExtensionValuationSubring
          (K := K) (L := L) v w
    rw [finitePlaceExtensionValuationSubring,
      mem_absoluteValueValuationSubring_iff,
      map_mul, map_inv₀, hsEq, inv_one, mul_one]
    exact haLe
  have hAne : A ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx0, hx1⟩ :=
      RayClass.adicAbv_isNontrivial v
    let y : L := algebraMap K L x
    have hy0 : y ≠ 0 := by
      change algebraMap K L x ≠ 0
      simpa only [map_zero] using
        (algebraMap K L).injective.ne hx0
    have hy1 : w.1 y ≠ 1 := by
      change w.1 (algebraMap K L x) ≠ 1
      rw [w.2]
      exact hx1
    have hle (z : L) : w.1 z ≤ 1 := by
      have hzA : z ∈ A := by
        rw [htop]
        trivial
      change
        z ∈ finitePlaceExtensionValuationSubring
          (K := K) (L := L) v w at hzA
      rw [finitePlaceExtensionValuationSubring,
        mem_absoluteValueValuationSubring_iff] at hzA
      exact hzA
    have honeLe : 1 ≤ w.1 y := by
      calc
        1 = w.1 y * w.1 y⁻¹ := by
          rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
        _ ≤ w.1 y * 1 :=
          mul_le_mul_of_nonneg_left (hle y⁻¹) (w.1.nonneg y)
        _ = w.1 y := mul_one _
    exact hy1 (le_antisymm (hle y) honeLe)
  exact (V.eq_of_le_of_ne_top hVA hAne).symm

section CrossBaseEquivalence

variable {F M : Type*}
    [Field F] [NumberField F]
    [Field M] [NumberField M]
    [Algebra F L] [Algebra M L]

omit [Algebra K L] [FiniteDimensional K L] in
/-- Exact finite-place extensions, even over different intermediate
base fields, define equivalent top-field valuations when their centres
coincide. -/
theorem finitePlaceExtensions_isEquiv_of_centres_eq
    (vF : HeightOneSpectrum (𝓞 F))
    (vM : HeightOneSpectrum (𝓞 M))
    (wF :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv F vF) L)
    (wM :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv M vM) L)
    (hcentre :
      finitePlaceExtensionCentre
          (K := F) (L := L) vF wF =
        finitePlaceExtensionCentre
          (K := M) (L := L) vM wM) :
    wF.1.IsEquiv wM.1 := by
  have hsubring :
      finitePlaceExtensionValuationSubring
          (K := F) (L := L) vF wF =
        finitePlaceExtensionValuationSubring
          (K := M) (L := L) vM wM := by
    rw [finitePlaceExtensionValuationSubring_eq_localization,
      finitePlaceExtensionValuationSubring_eq_localization,
      hcentre]
  have hle (x : L) :
      wF.1 x ≤ 1 ↔ wM.1 x ≤ 1 := by
    change
      x ∈
          finitePlaceExtensionValuationSubring
            (K := F) (L := L) vF wF ↔
        x ∈
          finitePlaceExtensionValuationSubring
            (K := M) (L := L) vM wM
    rw [hsubring]
  apply AbsoluteValue.isEquiv_iff_lt_one_iff.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  calc
    wF.1 x < 1 ↔ 1 < (wF.1 x)⁻¹ :=
      (one_lt_inv₀ (wF.1.pos hx)).symm
    _ ↔ 1 < wF.1 x⁻¹ := by
      rw [map_inv₀]
    _ ↔ ¬ wF.1 x⁻¹ ≤ 1 := not_le.symm
    _ ↔ ¬ wM.1 x⁻¹ ≤ 1 :=
      not_congr (hle x⁻¹)
    _ ↔ 1 < wM.1 x⁻¹ := not_le
    _ ↔ 1 < (wM.1 x)⁻¹ := by
      rw [map_inv₀]
    _ ↔ wM.1 x < 1 :=
      one_lt_inv₀ (wM.1.pos hx)

end CrossBaseEquivalence

omit [FiniteDimensional K L] in
/-- An exact extension of the normalized finite absolute value is
determined by its centre in `𝓞 L`. -/
theorem finitePlaceExtensionCentre_injective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective
      (finitePlaceExtensionCentre
        (K := K) (L := L) v) := by
  intro w w' hcentre
  have hequiv : w.1.IsEquiv w'.1 :=
    finitePlaceExtensions_isEquiv_of_centres_eq
      (F := K) (M := K) v v w w' hcentre
  exact
    equivalent_exactExtensions_eq
      (HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v) w w'
      ((LubinTate.Valuations.equivalentAbsoluteValues_iff_isEquiv
        w.1 w'.1).2 hequiv)

omit [NumberField L] [FiniteDimensional K L] in
/-- Pulling an exact extension back by `σ` carries its centre by the
inverse prime permutation. -/
theorem finitePlaceExtensionCentre_conjugate
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (σ : L ≃ₐ[K] L) :
    finitePlaceExtensionCentre
        (K := K) (L := L) v
        (absoluteValueExtensionConjugate
          (HeightOneSpectrum.adicAbv K v) w σ) =
      finitePlaceEquiv K L σ⁻¹
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) := by
  apply HeightOneSpectrum.ext
  ext x
  change
    x ∈ finitePlaceExtensionCentreIdeal
        (K := K) (L := L) v
        (absoluteValueExtensionConjugate
          (HeightOneSpectrum.adicAbv K v) w σ) ↔
      NumberField.RingOfIntegers.mapRingHom
          σ.toRingHom x ∈
        finitePlaceExtensionCentreIdeal
          (K := K) (L := L) v w
  rw [mem_finitePlaceExtensionCentreIdeal_iff,
    mem_finitePlaceExtensionCentreIdeal_iff]
  rfl

/-- An exact extension of the absolute value at `v`, regarded as a finite
place of `L` lying above `v`. -/
noncomputable def finitePlaceExtensionCentreInFibre
    (v : HeightOneSpectrum (𝓞 K)) :
    AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v) L →
      {W : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := K) W = v} :=
  fun w =>
    ⟨finitePlaceExtensionCentre (K := K) (L := L) v w,
      finitePlaceBelow_finitePlaceExtensionCentre
        (K := K) (L := L) v w⟩

omit [FiniteDimensional K L] in
@[simp]
theorem finitePlaceExtensionCentreInFibre_coe
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    (finitePlaceExtensionCentreInFibre
        (K := K) (L := L) v w :
      HeightOneSpectrum (𝓞 L)) =
      finitePlaceExtensionCentre (K := K) (L := L) v w :=
  rfl

omit [FiniteDimensional K L] in
theorem finitePlaceExtensionCentreInFibre_injective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective
      (finitePlaceExtensionCentreInFibre
        (K := K) (L := L) v) := by
  intro w w' h
  apply finitePlaceExtensionCentre_injective
    (K := K) (L := L) v
  exact congrArg Subtype.val h

theorem
    finitePlaceExtensionCentreInFibre_surjective_of_isGalois
    [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective
      (finitePlaceExtensionCentreInFibre
        (K := K) (L := L) v) := by
  let w₀ : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L :=
    pullbackAbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v)
      IsAlgClosed.lift
  let W₀ :=
    finitePlaceExtensionCentre (K := K) (L := L) v w₀
  let : Finite (L ≃ₐ[K] L) :=
    IsGaloisGroup.finite (L ≃ₐ[K] L) K L
  let :
      IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing
      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  intro W
  let : W₀.asIdeal.LiesOver v.asIdeal :=
    ⟨(finitePlaceExtensionCentreIdeal_under
      (K := K) (L := L) v w₀).symm⟩
  let : W.1.asIdeal.LiesOver v.asIdeal := ⟨by
    have h := congrArg HeightOneSpectrum.asIdeal W.2
    simpa only [finitePlaceBelow_asIdeal] using h.symm⟩
  obtain ⟨σ, hσ⟩ :=
    HilbertRamification.Dedekind.exists_smul_eq_of_isGaloisGroup
      v.asIdeal W₀.asIdeal W.1.asIdeal (L ≃ₐ[K] L)
  have hplace :
      finitePlaceEquiv K L σ W₀ = W.1 := by
    apply HeightOneSpectrum.ext
    rw [finitePlaceEquiv_asIdeal]
    exact hσ
  refine ⟨absoluteValueExtensionConjugate
      (HeightOneSpectrum.adicAbv K v) w₀ σ⁻¹, ?_⟩
  apply Subtype.ext
  rw [finitePlaceExtensionCentreInFibre_coe,
    finitePlaceExtensionCentre_conjugate]
  simpa only [inv_inv] using hplace

/-- Every finite place of `L` above `v` is the centre of an exact extension
of the normalized absolute value at `v`. -/
theorem finitePlaceExtensionCentreInFibre_surjective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective
      (finitePlaceExtensionCentreInFibre
        (K := K) (L := L) v) := by
  intro W
  let M := finiteNormalClosure K L
  let e : L →ₐ[K] M :=
    finiteNormalClosureEmbedding K L
  let : Algebra L M :=
    e.toRingHom.toAlgebra
  let : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq'
      e.comp_algebraMap.symm
  let : FiniteDimensional L M :=
    FiniteDimensional.right K L M
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 M) W.1.asIdeal
  let : Q.IsMaximal :=
    hQmax
  let U : HeightOneSpectrum (𝓞 M) :=
    { asIdeal := Q
      isPrime := hQmax.isPrime
      ne_bot :=
        Ideal.IsMaximal.ne_bot_of_isIntegral_int Q }
  have hUbelowL :
      finitePlaceBelow (K := L) U = W.1 := by
    apply HeightOneSpectrum.ext
    exact hQover.over.symm
  have hUbelowK :
      finitePlaceBelow (K := K) U = v := by
    have htrans :
        finitePlaceBelow (K := K)
            (finitePlaceBelow (K := L) U) =
          finitePlaceBelow (K := K) U := by
      apply HeightOneSpectrum.ext
      exact
        Ideal.under_under
          (A := 𝓞 K) (B := 𝓞 L) (C := 𝓞 M) Q
    rw [← htrans, hUbelowL, W.2]
  let Uv :
      {U : HeightOneSpectrum (𝓞 M) //
        finitePlaceBelow (K := K) U = v} :=
    ⟨U, hUbelowK⟩
  obtain ⟨uM, huM⟩ :=
    finitePlaceExtensionCentreInFibre_surjective_of_isGalois
      (K := K) (L := M) v Uv
  have hcentreM :
      finitePlaceExtensionCentre
          (K := K) (L := M) v uM = U :=
    congrArg Subtype.val huM
  have hcentreIdealM :
      finitePlaceExtensionCentreIdeal
          (K := K) (L := M) v uM = Q := by
    simpa only [finitePlaceExtensionCentre_asIdeal] using
      congrArg HeightOneSpectrum.asIdeal hcentreM
  let uL :
      AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v) L :=
    { val :=
        uM.1.comp (f := algebraMap L M)
          (algebraMap L M).injective
      property := by
        intro x
        change
          uM.1
              (algebraMap L M
                (algebraMap K L x)) =
            HeightOneSpectrum.adicAbv K v x
        rw [← IsScalarTower.algebraMap_apply K L M]
        exact uM.2 x }
  refine ⟨uL, ?_⟩
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  ext x
  change
    x ∈ finitePlaceExtensionCentreIdeal
        (K := K) (L := L) v uL ↔
      x ∈ W.1.asIdeal
  rw [mem_finitePlaceExtensionCentreIdeal_iff]
  change
    uM.1 (algebraMap L M (x : L)) < 1 ↔
      x ∈ W.1.asIdeal
  have hmap :
      ((algebraMap (𝓞 L) (𝓞 M) x : 𝓞 M) : M) =
        algebraMap L M (x : L) :=
    rfl
  rw [← hmap]
  rw [← mem_finitePlaceExtensionCentreIdeal_iff
      (K := K) (L := M) v uM
      (algebraMap (𝓞 L) (𝓞 M) x),
    hcentreIdealM, hQover.over]
  rfl

/-- The exact normalized extensions of the finite absolute value at `v`
are canonically indexed by the finite places of `L` above `v`. -/
noncomputable def finitePlaceExtensionEquivAbove
    (v : HeightOneSpectrum (𝓞 K)) :
    AbsoluteValueExtension
        (HeightOneSpectrum.adicAbv K v) L ≃
      {W : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := K) W = v} :=
  Equiv.ofBijective
    (finitePlaceExtensionCentreInFibre
      (K := K) (L := L) v)
    ⟨finitePlaceExtensionCentreInFibre_injective
        (K := K) (L := L) v,
      finitePlaceExtensionCentreInFibre_surjective
        (K := K) (L := L) v⟩

@[simp]
theorem finitePlaceExtensionEquivAbove_coe
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    (finitePlaceExtensionEquivAbove
        (K := K) (L := L) v w :
      HeightOneSpectrum (𝓞 L)) =
      finitePlaceExtensionCentre (K := K) (L := L) v w :=
  rfl

end Centre
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_AdicCompletionMap
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseIsUltrametricDist _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The canonical map between adic completions

A finite place above a base finite place determines the continuous
extension of the number-field algebra map to their concrete adic
completions.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v w

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The canonical map between adic completions at a finite place and a
chosen place above it.  It is obtained by completing the algebra map
between the corresponding valued copies of the number fields. -/
noncomputable def finitePlaceAdicCompletionMap
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w}) :
    w.adicCompletion K →+* W.1.adicCompletion L := by
  letI : W.1.asIdeal.LiesOver w.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal W.2.symm
  exact
    (HeightOneSpectrum.adicCompletion.equiv L W.1).symm.toRingHom.comp
      ((UniformSpace.Completion.mapRingHom
        (algebraMap
          (WithVal (w.valuation K))
          (WithVal (W.1.valuation L)))
        (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
          K L w W.1).continuous).comp
        (HeightOneSpectrum.adicCompletion.equiv K w).toRingHom)

/-- On the dense copy of the base field, the canonical map of adic
completions is the original field embedding. -/
theorem finitePlaceAdicCompletionMap_coe
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : K) :
    finitePlaceAdicCompletionMap K L w W
        (x : w.adicCompletion K) =
      (algebraMap K L x : W.1.adicCompletion L) := by
  let : W.1.asIdeal.LiesOver w.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal W.2.symm
  change
    HeightOneSpectrum.adicCompletion.ofCompletion
      (UniformSpace.Completion.mapRingHom
        (algebraMap
          (WithVal (w.valuation K))
          (WithVal (W.1.valuation L)))
        (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
          K L w W.1).continuous
        (algebraMap K (w.valuation K).Completion x)) =
      _
  congr 1
  change
    UniformSpace.Completion.mapRingHom
        (algebraMap
          (WithVal (w.valuation K))
          (WithVal (W.1.valuation L)))
        (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
          K L w W.1).continuous
        ((WithVal.equiv (w.valuation K)).symm x :
          (w.valuation K).Completion) =
      ((algebraMap
        (WithVal (w.valuation K))
        (WithVal (W.1.valuation L)))
        ((WithVal.equiv (w.valuation K)).symm x) :
          (W.1.valuation L).Completion)
  rw [UniformSpace.Completion.mapRingHom_coe]

/-- The canonical map of adic completions is compatible with the original
number-field tower. -/
theorem finitePlaceAdicCompletionMap_isScalarTower
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w}) :
    letI : Algebra (w.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L w W).toAlgebra
    IsScalarTower K (w.adicCompletion K) (W.1.adicCompletion L) := by
  let : Algebra (w.adicCompletion K) (W.1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L w W).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change
    (algebraMap K (W.1.adicCompletion L)) x =
      finitePlaceAdicCompletionMap K L w W
        (x : w.adicCompletion K)
  rw [finitePlaceAdicCompletionMap_coe K L w W x]
  exact IsScalarTower.algebraMap_apply K L (W.1.adicCompletion L) x

/-- The canonical map between the two adic completions is continuous. -/
theorem finitePlaceAdicCompletionMap_continuous
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w}) :
    Continuous (finitePlaceAdicCompletionMap K L w W) := by
  let : W.1.asIdeal.LiesOver w.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal W.2.symm
  unfold finitePlaceAdicCompletionMap
  exact
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L W.1).comp
      (UniformSpace.Completion.continuous_map.comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w))

/-- The canonical map on a finite-place adic completion induced by the
identity field extension is the identity map. -/
@[simp]
theorem finitePlaceAdicCompletionMap_self_apply
    (W : HeightOneSpectrum (𝓞 K))
    (x : W.adicCompletion K) :
    finitePlaceAdicCompletionMap K K W
        ⟨W, finitePlaceBelow_self W⟩ x =
      x := by
  let P : (W.valuation K).Completion → Prop := fun y =>
    finitePlaceAdicCompletionMap K K W
        ⟨W, finitePlaceBelow_self W⟩
        (HeightOneSpectrum.adicCompletion.ofCompletion y) =
      HeightOneSpectrum.adicCompletion.ofCompletion y
  change P x.toCompletion
  refine UniformSpace.Completion.induction_on
    (α := WithVal (W.valuation K)) x.toCompletion ?_ ?_
  · exact isClosed_eq
      ((finitePlaceAdicCompletionMap_continuous
        K K W ⟨W, finitePlaceBelow_self W⟩).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K W))
      (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K W)
  · intro r
    let k : K := WithVal.equiv (W.valuation K) r
    change
      finitePlaceAdicCompletionMap K K W
          ⟨W, finitePlaceBelow_self W⟩
          (k : W.adicCompletion K) =
        (k : W.adicCompletion K)
    rw [finitePlaceAdicCompletionMap_coe
      K K W ⟨W, finitePlaceBelow_self W⟩ k]
    simp
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_Comparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
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

omit [FiniteDimensional K L] in
/-- The standard absolute value at the centre of an exact extension has
the same valuation subring as that exact extension. -/
theorem finitePlaceExtension_adicAbv_valuationSubring
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    absoluteValueValuationSubring
        (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w))
        (finitePlaceExtension_nonarchimedean
          (K := L) (L := L)
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)
          ⟨HeightOneSpectrum.adicAbv L
              (finitePlaceExtensionCentre
                (K := K) (L := L) v w),
            fun _ => rfl⟩) =
      finitePlaceExtensionValuationSubring
        (K := K) (L := L) v w := by
  rw [finitePlaceExtensionValuationSubring_eq_localization,
    (finitePlaceExtensionCentre
      (K := K) (L := L) v w).valuationSubringAtPrime_eq_valuationSubring]
  ext x
  rw [mem_absoluteValueValuationSubring_iff]
  change
    HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) x ≤ 1 ↔
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w).valuation L x ≤ 1
  rw [HeightOneSpectrum.adicAbv_def]
  exact_mod_cast
    WithZeroMulInt.toNNReal_le_one_iff
      (HeightOneSpectrum.one_lt_absNorm_nnreal
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w))

omit [FiniteDimensional K L] in
/-- The exact extension and the standard absolute value at its centre are
equivalent absolute values. -/
theorem finitePlaceExtension_isEquiv_adicAbv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    w.1.IsEquiv
      (HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w)) := by
  apply AbsoluteValue.isEquiv_iff_lt_one_iff.mpr
  intro x
  have hle (y : L) :
      w.1 y ≤ 1 ↔
        HeightOneSpectrum.adicAbv L
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w) y ≤ 1 := by
    rw [← mem_absoluteValueValuationSubring_iff
        w.1 (finitePlaceExtension_nonarchimedean
          (K := K) (L := L) v w),
      ← mem_absoluteValueValuationSubring_iff
        (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w))
        (finitePlaceExtension_nonarchimedean
          (K := L) (L := L)
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)
          ⟨HeightOneSpectrum.adicAbv L
              (finitePlaceExtensionCentre
                (K := K) (L := L) v w),
            fun _ => rfl⟩)]
    change
      y ∈ finitePlaceExtensionValuationSubring
          (K := K) (L := L) v w ↔
        y ∈ absoluteValueValuationSubring
          (HeightOneSpectrum.adicAbv L
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w))
          (finitePlaceExtension_nonarchimedean
            (K := L) (L := L)
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w)
            ⟨HeightOneSpectrum.adicAbv L
                (finitePlaceExtensionCentre
                  (K := K) (L := L) v w),
              fun _ => rfl⟩)
    rw [finitePlaceExtension_adicAbv_valuationSubring]
  by_cases hx : x = 0
  · subst x
    simp
  calc
    w.1 x < 1 ↔ 1 < (w.1 x)⁻¹ :=
      (one_lt_inv₀ (w.1.pos hx)).symm
    _ ↔ 1 < w.1 x⁻¹ := by rw [map_inv₀]
    _ ↔ ¬ w.1 x⁻¹ ≤ 1 := not_le.symm
    _ ↔ ¬ HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w) x⁻¹ ≤ 1 :=
      not_congr (hle x⁻¹)
    _ ↔ 1 < HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w) x⁻¹ := not_le
    _ ↔ 1 < (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w) x)⁻¹ := by
      rw [map_inv₀]
    _ ↔ HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w) x < 1 :=
      one_lt_inv₀
        ((HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)).pos hx)

/-- The positive exponent relating an exact extension to the standard
absolute value at its centre. -/
noncomputable def finitePlaceExtensionExponent
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) : ℝ :=
  (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp
    (finitePlaceExtension_isEquiv_adicAbv
      (K := K) (L := L) v w)).choose

omit [FiniteDimensional K L] in
theorem finitePlaceExtensionExponent_pos
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    0 < finitePlaceExtensionExponent
      (K := K) (L := L) v w :=
  (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp
    (finitePlaceExtension_isEquiv_adicAbv
      (K := K) (L := L) v w)).choose_spec.1

omit [FiniteDimensional K L] in
theorem finitePlaceExtension_adicAbv_eq_rpow
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : L) :
    HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) x =
      w.1 x ^ finitePlaceExtensionExponent
        (K := K) (L := L) v w :=
  (congrFun
    (AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp
      (finitePlaceExtension_isEquiv_adicAbv
        (K := K) (L := L) v w)).choose_spec.2 x).symm

/-- The identity on `L`, regarded as a ring equivalence between the two
normed copies determined by the equivalent absolute values. -/
noncomputable def finitePlaceExtensionWithAbsRingEquiv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    WithAbs w.1 ≃+*
      WithAbs
        (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)) :=
  WithAbs.congr w.1
    (HeightOneSpectrum.adicAbv L
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w))
    (RingEquiv.refl L)

omit [FiniteDimensional K L] in
theorem finitePlaceExtensionWithAbsRingEquiv_continuous
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    Continuous
      (finitePlaceExtensionWithAbsRingEquiv
        (K := K) (L := L) v w) :=
  (AbsoluteValue.isEquiv_iff_isHomeomorph _ _).mp
    (finitePlaceExtension_isEquiv_adicAbv
      (K := K) (L := L) v w) |>.continuous

omit [FiniteDimensional K L] in
theorem finitePlaceExtensionWithAbsRingEquiv_symm_continuous
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    Continuous
      (finitePlaceExtensionWithAbsRingEquiv
        (K := K) (L := L) v w).symm := by
  rw [finitePlaceExtensionWithAbsRingEquiv,
    WithAbs.congr_symm]
  exact
    ((AbsoluteValue.isEquiv_iff_isHomeomorph _ _).mp
      (finitePlaceExtension_isEquiv_adicAbv
        (K := K) (L := L) v w).symm).continuous

/-- The completion comparison induced by the identity on `L`. -/
noncomputable def finitePlaceExtensionCompletionRingEquiv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    w.1.Completion ≃+*
      (HeightOneSpectrum.adicAbv L
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w)).Completion :=
  UniformSpace.Completion.mapRingEquiv
    (finitePlaceExtensionWithAbsRingEquiv
      (K := K) (L := L) v w)
    (finitePlaceExtensionWithAbsRingEquiv_continuous
      (K := K) (L := L) v w)
    (finitePlaceExtensionWithAbsRingEquiv_symm_continuous
      (K := K) (L := L) v w)

omit [FiniteDimensional K L] in
@[simp]
theorem finitePlaceExtensionCompletionRingEquiv_toCompletion
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : L) :
    finitePlaceExtensionCompletionRingEquiv
        (K := K) (L := L) v w
        (AbsoluteValue.toCompletion w.1 x) =
      AbsoluteValue.toCompletion
        (HeightOneSpectrum.adicAbv L
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w)) x := by
  change
    UniformSpace.Completion.mapRingEquiv
        (finitePlaceExtensionWithAbsRingEquiv
          (K := K) (L := L) v w)
        (finitePlaceExtensionWithAbsRingEquiv_continuous
          (K := K) (L := L) v w)
        (finitePlaceExtensionWithAbsRingEquiv_symm_continuous
          (K := K) (L := L) v w)
      (((WithAbs.equiv w.1).symm x : WithAbs w.1) :
        w.1.Completion) = _
  rw [UniformSpace.Completion.mapRingEquiv_apply,
    UniformSpace.Completion.map_coe
      (uniformContinuous_addMonoidHom_of_continuous
        (finitePlaceExtensionWithAbsRingEquiv_continuous
          (K := K) (L := L) v w))]
  rfl

omit [FiniteDimensional K L] in
/-- The completion comparison is continuous. -/
theorem finitePlaceExtensionCompletionRingEquiv_continuous
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    Continuous
      (finitePlaceExtensionCompletionRingEquiv
        (K := K) (L := L) v w) :=
  UniformSpace.Completion.continuous_map

omit [FiniteDimensional K L] in
/-- The norm on the standard completion is the positive power of the
norm on the exact-extension completion. -/
theorem finitePlaceExtensionCompletionRingEquiv_norm
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : w.1.Completion) :
    ‖finitePlaceExtensionCompletionRingEquiv
        (K := K) (L := L) v w x‖ =
      ‖x‖ ^ finitePlaceExtensionExponent
        (K := K) (L := L) v w := by
  refine UniformSpace.Completion.induction_on
    (α := WithAbs w.1) x ?_ ?_
  · exact isClosed_eq
      (continuous_norm.comp
        (finitePlaceExtensionCompletionRingEquiv_continuous
          (K := K) (L := L) v w))
      (continuous_norm.rpow_const
        (fun _ => Or.inr
          (finitePlaceExtensionExponent_pos
            (K := K) (L := L) v w).le))
  · intro a
    change
      ‖UniformSpace.Completion.map
          (finitePlaceExtensionWithAbsRingEquiv
            (K := K) (L := L) v w)
          (a : w.1.Completion)‖ =
        ‖(a : w.1.Completion)‖ ^
          finitePlaceExtensionExponent
            (K := K) (L := L) v w
    rw [UniformSpace.Completion.map_coe
        (uniformContinuous_addMonoidHom_of_continuous
          (finitePlaceExtensionWithAbsRingEquiv_continuous
            (K := K) (L := L) v w)),
      UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe,
      WithAbs.norm_eq_apply_ofAbs,
      WithAbs.norm_eq_apply_ofAbs]
    exact finitePlaceExtension_adicAbv_eq_rpow
      (K := K) (L := L) v w (WithAbs.equiv w.1 a)

/-- The local factor comparison from an exact-extension completion to
the concrete completion at its centre. -/
noncomputable def finitePlaceExtensionAdicCompletionRingEquiv
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L) :
    w.1.Completion ≃+*
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w).adicCompletion L :=
  (finitePlaceExtensionCompletionRingEquiv
    (K := K) (L := L) v w).trans
    (relativeFinitePlaceCompletionRingEquiv
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w))

omit [FiniteDimensional K L] in
theorem finitePlaceExtensionAdicCompletionRingEquiv_norm
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : w.1.Completion) :
    ‖finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w x‖ =
      ‖x‖ ^ finitePlaceExtensionExponent
        (K := K) (L := L) v w := by
  rw [finitePlaceExtensionAdicCompletionRingEquiv,
    RingEquiv.trans_apply,
    relativeFinitePlaceCompletionRingEquiv_norm,
    finitePlaceExtensionCompletionRingEquiv_norm]

omit [FiniteDimensional K L] in
@[simp]
theorem finitePlaceExtensionAdicCompletionRingEquiv_toCompletion
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : L) :
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w
        (AbsoluteValue.toCompletion w.1 x) =
      FinitePlace.embedding
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) x := by
  rw [finitePlaceExtensionAdicCompletionRingEquiv,
    RingEquiv.trans_apply,
    finitePlaceExtensionCompletionRingEquiv_toCompletion]
  change
    relativeFinitePlaceCompletionRingHom
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w)
        (((WithAbs.equiv
          (HeightOneSpectrum.adicAbv L
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w))).symm x :
          WithAbs
            (HeightOneSpectrum.adicAbv L
              (finitePlaceExtensionCentre
                (K := K) (L := L) v w))) :
          (HeightOneSpectrum.adicAbv L
            (finitePlaceExtensionCentre
              (K := K) (L := L) v w)).Completion) = _
  rw [relativeFinitePlaceCompletionRingHom_coe]
  rfl

omit [FiniteDimensional K L] in
/-- The local factor comparison identifies the valuation ring in the
exact-extension completion with the concrete adic integers. -/
theorem finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (x : w.1.Completion) :
    finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) v w x ∈
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w).adicCompletionIntegers L ↔
      x ∈ absoluteValueCompletionIntegers w.1
        (absoluteValueExtension_isNonarchimedean
          (HeightOneSpectrum.adicAbv K v)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K v) w) := by
  rw [mem_absoluteValueCompletionIntegers_iff]
  have hrpow :
      ‖x‖ ^ finitePlaceExtensionExponent
          (K := K) (L := L) v w ≤ 1 ↔
        ‖x‖ ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_iff (norm_nonneg x) zero_le_one
        (finitePlaceExtensionExponent_pos
          (K := K) (L := L) v w)
  constructor
  · intro hx
    have hnorm :=
      norm_le_one_of_mem_adicCompletionIntegers
        (finitePlaceExtensionCentre
          (K := K) (L := L) v w) hx
    rw [finitePlaceExtensionAdicCompletionRingEquiv_norm] at hnorm
    exact hrpow.mp hnorm
  · intro hx
    apply mem_adicCompletionIntegers_of_norm_le_one
      (finitePlaceExtensionCentre
        (K := K) (L := L) v w)
    rw [finitePlaceExtensionAdicCompletionRingEquiv_norm]
    exact hrpow.mpr hx
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_AdicCompletionComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseIsUltrametricDist _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Comparing the exact-extension and concrete adic-completion maps

The completion map attached to an exact extension of a finite-place
absolute value agrees with the canonical map between the concrete adic
completions at the corresponding finite places.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The concrete homomorphism of adic completions associated with an
exact extension of the normalized absolute value. -/
noncomputable def finitePlaceExtensionAdicCompletionMap
    (w : HeightOneSpectrum (𝓞 K))
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    w.adicCompletion K →+*
      (finitePlaceExtensionCentre
        (K := K) (L := L) w a).adicCompletion L :=
  (finitePlaceExtensionAdicCompletionRingEquiv
      (K := K) (L := L) w a).toRingHom.comp
    ((AbsoluteValue.completionMap
      (HeightOneSpectrum.adicAbv K w) a.1 a.2).comp
      (relativeFinitePlaceCompletionAlgEquiv w).symm.toRingHom)

/-- The exact-extension completion map agrees with the field embedding
on elements of the base number field. -/
theorem finitePlaceExtensionAdicCompletionMap_coe
    (w : HeightOneSpectrum (𝓞 K))
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : K) :
    finitePlaceExtensionAdicCompletionMap K L w a
        (x : w.adicCompletion K) =
      (algebraMap K L x :
        (finitePlaceExtensionCentre
          (K := K) (L := L) w a).adicCompletion L) := by
  have hcomparison :
      (relativeFinitePlaceCompletionAlgEquiv w).symm
          (x : w.adicCompletion K) =
        algebraMap K
          (HeightOneSpectrum.adicAbv K w).Completion x := by
    change
      (relativeFinitePlaceCompletionAlgEquiv w).symm
          (algebraMap K (w.adicCompletion K) x) =
        algebraMap K
          (HeightOneSpectrum.adicAbv K w).Completion x
    exact (relativeFinitePlaceCompletionAlgEquiv w).symm.commutes x
  change
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w a
        (AbsoluteValue.completionMap
          (HeightOneSpectrum.adicAbv K w) a.1 a.2
          ((relativeFinitePlaceCompletionAlgEquiv w).symm
            (x : w.adicCompletion K))) =
      _
  rw [hcomparison,
    AbsoluteValue.completionMap_coe,
    finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]
  rfl

/-- The completion map defined using an exact absolute-value extension
is continuous. -/
theorem finitePlaceExtensionAdicCompletionMap_continuous
    (w : HeightOneSpectrum (𝓞 K))
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    Continuous
      (finitePlaceExtensionAdicCompletionMap K L w a) := by
  have hrelative :
      Isometry (relativeFinitePlaceCompletionAlgEquiv w).symm :=
    AddMonoidHomClass.isometry_of_norm
      (relativeFinitePlaceCompletionAlgEquiv w).symm
      (relativeFinitePlaceCompletionAlgEquiv_symm_norm w)
  exact
    ((relativeFinitePlaceCompletionRingHom_isometry
      (finitePlaceExtensionCentre
        (K := K) (L := L) w a)).continuous.comp
      (finitePlaceExtensionCompletionRingEquiv_continuous
        (K := K) (L := L) w a)).comp
      ((AbsoluteValue.completionMap_isometry
        (HeightOneSpectrum.adicAbv K w) a.1 a.2).continuous.comp
        hrelative.continuous)

/-- The exact-extension construction and the canonical completion of the
field embedding agree.  Equality on the dense copy of `K` is extended by
continuity. -/
theorem finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
    (w : HeightOneSpectrum (𝓞 K))
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K) :
    finitePlaceExtensionAdicCompletionMap K L w a x =
      finitePlaceAdicCompletionMap K L w
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a) x := by
  let P : (w.valuation K).Completion → Prop := fun y =>
    finitePlaceExtensionAdicCompletionMap K L w a
        (HeightOneSpectrum.adicCompletion.ofCompletion y) =
      finitePlaceAdicCompletionMap K L w
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a)
        (HeightOneSpectrum.adicCompletion.ofCompletion y)
  change P x.toCompletion
  refine UniformSpace.Completion.induction_on
    (α := WithVal (w.valuation K)) x.toCompletion ?_ ?_
  · change IsClosed
      {y | finitePlaceExtensionAdicCompletionMap K L w a
          (HeightOneSpectrum.adicCompletion.ofCompletion y) =
        finitePlaceAdicCompletionMap K L w
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) w a)
          (HeightOneSpectrum.adicCompletion.ofCompletion y)}
    exact isClosed_eq
      ((finitePlaceExtensionAdicCompletionMap_continuous K L w a).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w))
      ((finitePlaceAdicCompletionMap_continuous K L w
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a)).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w))
  · intro r
    let k : K := WithVal.equiv (w.valuation K) r
    change
      finitePlaceExtensionAdicCompletionMap K L w a
          (HeightOneSpectrum.adicCompletion.ofCompletion
            (r : (w.valuation K).Completion)) =
        finitePlaceAdicCompletionMap K L w
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) w a)
          (HeightOneSpectrum.adicCompletion.ofCompletion
            (r : (w.valuation K).Completion))
    change
      finitePlaceExtensionAdicCompletionMap K L w a
          (k : w.adicCompletion K) =
        finitePlaceAdicCompletionMap K L w
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) w a)
          (k : w.adicCompletion K)
    rw [finitePlaceExtensionAdicCompletionMap_coe,
      finitePlaceAdicCompletionMap_coe]
    change
      (algebraMap K L k :
        (finitePlaceExtensionCentre
          (K := K) (L := L) w a).adicCompletion L) =
      (algebraMap K L k :
        (finitePlaceExtensionCentre
          (K := K) (L := L) w a).adicCompletion L)
    rfl

/-- The concrete completion at a finite place above `w` is finite over the
concrete completion at `w`, for the canonical completion map. -/
theorem finitePlaceAdicCompletionMap_moduleFinite
    [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w}) :
    letI : Algebra (w.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L w W).toAlgebra
    Module.Finite (w.adicCompletion K) (W.1.adicCompletion L) := by
  classical
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  let : Algebra
      (w.adicCompletion K)
      ((finitePlaceExtensionEquivAbove
        (K := K) (L := L) w a).1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L w
      (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w a)).toAlgebra
  let : Module
      (w.adicCompletion K)
      ((finitePlaceExtensionEquivAbove
        (K := K) (L := L) w a).1.adicCompletion L) :=
    Algebra.toModule
  let : Algebra (w.adicCompletion K) vK.Completion :=
    (relativeFinitePlaceCompletionAlgEquiv w).symm.toRingHom.toAlgebra
  let : Algebra vK.Completion a.1.Completion :=
    AbsoluteValue.completionAlgebra vK a.1 a.2
  let : Algebra (w.adicCompletion K) a.1.Completion :=
    ((algebraMap vK.Completion a.1.Completion).comp
      (relativeFinitePlaceCompletionAlgEquiv w).symm.toRingHom).toAlgebra
  let : IsScalarTower
      (w.adicCompletion K) vK.Completion a.1.Completion :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite (w.adicCompletion K) vK.Completion :=
    Module.Finite.of_surjective
      (Algebra.linearMap (w.adicCompletion K) vK.Completion)
      (relativeFinitePlaceCompletionAlgEquiv w).symm.surjective
  let : Module.Finite vK.Completion a.1.Completion :=
    completionModuleFinite vK hvK a
  let : Module.Finite (w.adicCompletion K) a.1.Completion :=
    Module.Finite.trans vK.Completion a.1.Completion
  let e :
      a.1.Completion ≃ₐ[w.adicCompletion K]
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w a).1.adicCompletion L :=
    { __ :=
        finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w a
      commutes' := fun x => by
        change
          finitePlaceExtensionAdicCompletionMap K L w a x =
            finitePlaceAdicCompletionMap K L w
              (finitePlaceExtensionEquivAbove
                (K := K) (L := L) w a) x
        exact
          finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
            K L w a x }
  exact Module.Finite.equiv e.toLinearEquiv

/-- The norm of the image under the concrete adic-completion map is
raised to the exact-extension exponent. -/
theorem finitePlaceExtensionAdicCompletionMap_norm
    (w : HeightOneSpectrum (𝓞 K))
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K) :
    ‖finitePlaceExtensionAdicCompletionMap K L w a x‖ =
      ‖x‖ ^ finitePlaceExtensionExponent
        (K := K) (L := L) w a := by
  change
    ‖finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w a
        (AbsoluteValue.completionMap
          (HeightOneSpectrum.adicAbv K w) a.1 a.2
          ((relativeFinitePlaceCompletionAlgEquiv w).symm x))‖ =
      _
  rw [
    finitePlaceExtensionAdicCompletionRingEquiv_norm,
    (AbsoluteValue.completionMap_isometry
      (HeightOneSpectrum.adicAbv K w) a.1 a.2).norm_map_of_map_zero
        (map_zero
          (AbsoluteValue.completionMap
            (HeightOneSpectrum.adicAbv K w) a.1 a.2)),
    relativeFinitePlaceCompletionAlgEquiv_symm_norm]

/-- The valuation of the image under the concrete adic-completion map
is multiplied by the ramification index.  This extends the corresponding
formula for elements of `K` to every element of the completion. -/
theorem finitePlaceExtensionAdicCompletionMap_valued
    (w : HeightOneSpectrum (𝓞 K))
    (a : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (x : w.adicCompletion K) :
    Valued.v (finitePlaceExtensionAdicCompletionMap K L w a x) =
      Valued.v x ^ w.asIdeal.ramificationIdx'
        (finitePlaceExtensionCentre
          (K := K) (L := L) w a).asIdeal := by
  let W :=
    finitePlaceExtensionCentre
      (K := K) (L := L) w a
  let : W.asIdeal.LiesOver w.asIdeal :=
    finitePlaceExtensionCentre_liesOver
      (K := K) (L := L) w a
  by_cases hx : x = 0
  · subst x
    have he :
        w.asIdeal.ramificationIdx' W.asIdeal ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
        W.asIdeal w.ne_bot
    simp only [map_zero]
    exact (zero_pow he).symm
  obtain ⟨r, hr⟩ := Valued.exists_coe_eq_v x.toCompletion
  let k : K := WithVal.equiv (w.valuation K) r
  have hkval : w.valuation K k = Valued.v x := by
    change Valued.v r = Valued.v x
    rw [← HeightOneSpectrum.adicCompletion.valued_toCompletion]
    exact hr.symm
  have hk : k ≠ 0 := by
    intro hk
    have : Valued.v x = 0 := by
      rw [← hkval, hk, map_zero]
    apply hx
    simpa using this
  let z : w.adicCompletion K := x * (k : w.adicCompletion K)⁻¹
  have hzval : Valued.v z = 1 := by
    simp [z, hkval, hx]
  have hznorm : ‖z‖ = 1 := by
    simp [FinitePlace.norm_def, hzval]
  have hmapznorm :
      ‖finitePlaceExtensionAdicCompletionMap K L w a z‖ = 1 := by
    rw [finitePlaceExtensionAdicCompletionMap_norm, hznorm]
    simp
  have hmapzval :
      Valued.v
        (finitePlaceExtensionAdicCompletionMap K L w a z) = 1 := by
    rw [FinitePlace.norm_def] at hmapznorm
    exact
      (WithZeroMulInt.toNNReal_eq_one_iff
        (Valued.v
          (finitePlaceExtensionAdicCompletionMap K L w a z))
        (HeightOneSpectrum.absNorm_ne_zero W)
        (HeightOneSpectrum.one_lt_absNorm_nnreal W).ne').mp
        (NNReal.eq hmapznorm)
  have hkcoe :
      (k : w.adicCompletion K) ≠ 0 := by
    change algebraMap K (w.adicCompletion K) k ≠ 0
    exact (map_ne_zero
      (algebraMap K (w.adicCompletion K))).2 hk
  have hx_factor :
      x = z * (k : w.adicCompletion K) := by
    dsimp [z]
    rw [mul_assoc, inv_mul_cancel₀ hkcoe, mul_one]
  calc
    Valued.v
        (finitePlaceExtensionAdicCompletionMap K L w a x) =
        Valued.v
          (finitePlaceExtensionAdicCompletionMap K L w a
            (z * (k : w.adicCompletion K))) := by
          rw [← hx_factor]
    _ = Valued.v
          (finitePlaceExtensionAdicCompletionMap K L w a z) *
        Valued.v
          (finitePlaceExtensionAdicCompletionMap K L w a
            (k : w.adicCompletion K)) := by
          rw [map_mul, map_mul]
    _ = Valued.v
          (finitePlaceExtensionAdicCompletionMap K L w a
            (k : w.adicCompletion K)) := by
          rw [hmapzval, one_mul]
    _ = W.valuation L (algebraMap K L k) := by
          rw [finitePlaceExtensionAdicCompletionMap_coe,
            HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    _ = (w.valuation K k) ^
          w.asIdeal.ramificationIdx' W.asIdeal :=
      (HeightOneSpectrum.valuation_liesOver L w W k).symm
    _ = Valued.v x ^
          w.asIdeal.ramificationIdx' W.asIdeal := by
      rw [hkval]

/-- Under the canonical map to a place above `w`, the completed
valuation is raised to the ramification index. -/
theorem finitePlaceAdicCompletionMap_valued
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w})
    (x : w.adicCompletion K) :
    Valued.v (finitePlaceAdicCompletionMap K L w W x) =
      Valued.v x ^ w.asIdeal.ramificationIdx' W.1.asIdeal := by
  obtain ⟨a, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [←
    finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap]
  exact finitePlaceExtensionAdicCompletionMap_valued K L w a x
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_SPlaces
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

/-- Relative ideles that are integral units in every local tensor
factor outside the finite set `S`. -/
noncomputable def relativeIdeleLocalTensorDecompositionSupportedSubgroup
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (RelativeIdeleGroup K L) :=
  ⨅ w : HeightOneSpectrum (𝓞 K),
    ⨅ (_ : w ∉ S),
      (relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w).comap
        (RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w)

omit [NumberField L] [IsGalois K L] in
/-- Membership in the supported relative-idele subgroup is exactly
valuation-ring integrality at every finite place outside `S`. -/
@[simp]
theorem mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : RelativeIdeleGroup K L) :
    z ∈ relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S ↔
      ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S →
        RelativeLocalTensorDecompositionIntegralUnitAt
          (K := K) (L := L) w
          (RelativeIdeleGroup.finiteComponent
            (K := K) (L := L) w z) := by
  simp only [relativeIdeleLocalTensorDecompositionSupportedSubgroup,
    Subgroup.mem_iInf, Subgroup.mem_comap,
    mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff]

/-- The finite local factors of a relative `S`-idele: unrestricted
tensor units on `S`, and actual local tensor integral units away
from `S`. -/
abbrev RelativeFiniteSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∈ S},
      (w.1.adicCompletion K ⊗[K] L)ˣ) ×
    (∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
      relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w.1)

/-- The complete local-factor model attached to a finite support. -/
abbrev RelativeIdeleSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (∀ w : InfinitePlace K, (w.Completion ⊗[K] L)ˣ) ×
    RelativeFiniteSPlaceFactors (K := K) (L := L) S

/-- Extract all local factors from an integrally supported
relative idele. -/
noncomputable def relativeIdeleSupportedComponents
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S →*
      RelativeIdeleSPlaceFactors (K := K) (L := L) S where
  toFun z :=
    ⟨fun w =>
        RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) w z,
      ⟨fun w =>
          RelativeIdeleGroup.finiteComponent
            (K := K) (L := L) w.1 z,
        fun w =>
          ⟨RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w.1 z,
            (mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
              (K := K) (L := L) w.1 _).2
              ((mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff
                (K := K) (L := L) S z).1 z.property
                w.1 w.2)⟩⟩⟩
  map_one' := by
    apply Prod.ext
    · funext w
      exact
        map_one
          (RelativeIdeleGroup.infiniteComponent
            (K := K) (L := L) w)
    · apply Prod.ext
      · funext w
        exact
          map_one
            (RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w.1)
      · funext w
        apply Subtype.ext
        exact
          map_one
            (RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w.1)
  map_mul' x y := by
    apply Prod.ext
    · funext w
      exact
        map_mul
          (RelativeIdeleGroup.infiniteComponent
            (K := K) (L := L) w)
          (x : RelativeIdeleGroup K L)
          (y : RelativeIdeleGroup K L)
    · apply Prod.ext
      · funext w
        exact
          map_mul
            (RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w.1)
            (x : RelativeIdeleGroup K L)
            (y : RelativeIdeleGroup K L)
      · funext w
        apply Subtype.ext
        exact
          map_mul
            (RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w.1)
            (x : RelativeIdeleGroup K L)
            (y : RelativeIdeleGroup K L)

omit [NumberField L] [IsGalois K L] in
/-- The infinite component of the displayed supported-factor map is the
original infinite component of the relative idele. -/
@[simp]
theorem relativeIdeleSupportedComponents_infinite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S)
    (w : InfinitePlace K) :
    (relativeIdeleSupportedComponents
      (K := K) (L := L) S z).1 w =
      RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w z :=
  rfl

omit [NumberField L] [IsGalois K L] in
/-- At a finite place in `S`, the displayed supported-factor map is the
unrestricted finite component. -/
@[simp]
theorem relativeIdeleSupportedComponents_inside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S)
    (w : {w : HeightOneSpectrum (𝓞 K) // w ∈ S}) :
    (relativeIdeleSupportedComponents
      (K := K) (L := L) S z).2.1 w =
      RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w.1 z :=
  rfl

omit [NumberField L] [IsGalois K L] in
/-- Outside `S`, coercing the integral factor back to tensor units recovers
the original finite component. -/
@[simp]
theorem relativeIdeleSupportedComponents_outside_coe
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S)
    (w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S}) :
    ((relativeIdeleSupportedComponents
        (K := K) (L := L) S z).2.2 w :
      (w.1.adicCompletion K ⊗[K] L)ˣ) =
      RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w.1 z :=
  rfl

/-- Assemble the complete `S`-place factor family as restricted local
idele data.  Away from `S` and the finite discriminant set, the converse
part of the local tensor decomposition supplies the required coefficient integrality. -/
noncomputable def relativeLocalIdeleDataOfSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S) :
    RelativeLocalIdeleData (K := K) (L := L) := by
  classical
  let f :
      ∀ w : HeightOneSpectrum (𝓞 K),
        (w.adicCompletion K ⊗[K] L)ˣ :=
    fun w =>
      if hw : w ∈ S then
        x.2.1 ⟨w, hw⟩
      else
        (x.2.2 ⟨w, hw⟩ :
          (w.adicCompletion K ⊗[K] L)ˣ)
  refine
    { infinite := x.1
      finite := f
      eventually_integral := ?_
      eventually_inverse_integral := ?_ }
  · intro i
    refine
      (S ∪ integralTensorComparisonBadPlaces
        (K := K) (L := L)).eventually_cofinite_notMem.mono ?_
    intro w hw
    have hwS : w ∉ S := by
      intro h
      exact hw (Finset.mem_union_left _ h)
    have hwBad :
        w ∉ integralTensorComparisonBadPlaces
          (K := K) (L := L) := by
      intro h
      exact hw (Finset.mem_union_right _ h)
    have hProp :
        RelativeLocalTensorDecompositionIntegralUnitAt
          (K := K) (L := L) w (f w) := by
      rw [show f w =
        (x.2.2 ⟨w, hwS⟩ :
          (w.adicCompletion K ⊗[K] L)ˣ) by
        simp [f, hwS]]
      exact
        (mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
          (K := K) (L := L) w _).1
          (x.2.2 ⟨w, hwS⟩).property
    have hBasis :
        RelativeBasisIntegralUnitAt
          (K := K) (L := L) w (f w) :=
      localTensorDecompositionIntegralUnit_imp_relativeBasisIntegralUnitAt_of_notMem
        (K := K) (L := L) w hwBad hProp
    exact
      relativeBasisIntegralAt_repr_mem
        (K := K) (L := L) w (f w : _)
        hBasis.1 i
  · intro i
    refine
      (S ∪ integralTensorComparisonBadPlaces
        (K := K) (L := L)).eventually_cofinite_notMem.mono ?_
    intro w hw
    have hwS : w ∉ S := by
      intro h
      exact hw (Finset.mem_union_left _ h)
    have hwBad :
        w ∉ integralTensorComparisonBadPlaces
          (K := K) (L := L) := by
      intro h
      exact hw (Finset.mem_union_right _ h)
    have hProp :
        RelativeLocalTensorDecompositionIntegralUnitAt
          (K := K) (L := L) w (f w) := by
      rw [show f w =
        (x.2.2 ⟨w, hwS⟩ :
          (w.adicCompletion K ⊗[K] L)ˣ) by
        simp [f, hwS]]
      exact
        (mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
          (K := K) (L := L) w _).1
          (x.2.2 ⟨w, hwS⟩).property
    have hBasis :
        RelativeBasisIntegralUnitAt
          (K := K) (L := L) w (f w) :=
      localTensorDecompositionIntegralUnit_imp_relativeBasisIntegralUnitAt_of_notMem
        (K := K) (L := L) w hwBad hProp
    exact
      relativeBasisIntegralAt_repr_mem
        (K := K) (L := L) w
        (((f w)⁻¹ : (w.adicCompletion K ⊗[K] L)ˣ) :
          w.adicCompletion K ⊗[K] L)
        hBasis.2 i

omit [IsGalois K L] in
/-- The assembled local-idele data has the prescribed infinite component. -/
@[simp]
theorem relativeLocalIdeleDataOfSPlaceFactors_infinite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S)
    (w : InfinitePlace K) :
    (relativeLocalIdeleDataOfSPlaceFactors
      (K := K) (L := L) S x).infinite w = x.1 w :=
  rfl

omit [IsGalois K L] in
/-- At a finite place in `S`, the assembled local-idele data has the
prescribed unrestricted component. -/
@[simp]
theorem relativeLocalIdeleDataOfSPlaceFactors_finite_inside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∈ S) :
    (relativeLocalIdeleDataOfSPlaceFactors
      (K := K) (L := L) S x).finite w =
        x.2.1 ⟨w, hw⟩ := by
  simp [relativeLocalIdeleDataOfSPlaceFactors, hw]

omit [IsGalois K L] in
/-- At a finite place outside `S`, the assembled local-idele data is the
coercion of the prescribed integral component. -/
@[simp]
theorem relativeLocalIdeleDataOfSPlaceFactors_finite_outside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ S) :
    (relativeLocalIdeleDataOfSPlaceFactors
      (K := K) (L := L) S x).finite w =
        (x.2.2 ⟨w, hw⟩ :
          (w.adicCompletion K ⊗[K] L)ˣ) := by
  simp [relativeLocalIdeleDataOfSPlaceFactors, hw]

/-- Assemble prescribed local factors into the actual supported
relative idele. -/
noncomputable def relativeIdeleOfSPlaceFactors
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S := by
  refine
    ⟨relativeIdeleOfLocalData
        (K := K) (L := L)
        (relativeLocalIdeleDataOfSPlaceFactors
          (K := K) (L := L) S x), ?_⟩
  rw [mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff]
  intro w hw
  rw [relativeIdeleOfLocalData_finiteComponent,
    relativeLocalIdeleDataOfSPlaceFactors_finite_outside
      (K := K) (L := L) S x w hw]
  exact
    (mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
      (K := K) (L := L) w _).1
      (x.2.2 ⟨w, hw⟩).property

omit [IsGalois K L] in
/-- The relative idele assembled from displayed `S`-place factors has the
prescribed infinite component. -/
@[simp]
theorem relativeIdeleOfSPlaceFactors_infiniteComponent
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S)
    (w : InfinitePlace K) :
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w
        (relativeIdeleOfSPlaceFactors
          (K := K) (L := L) S x) =
      x.1 w := by
  rw [relativeIdeleOfSPlaceFactors,
    relativeIdeleOfLocalData_infiniteComponent]
  rfl

omit [IsGalois K L] in
/-- At a finite place in `S`, the assembled relative idele has the
prescribed unrestricted component. -/
@[simp]
theorem relativeIdeleOfSPlaceFactors_finiteComponent_inside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∈ S) :
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w
        (relativeIdeleOfSPlaceFactors
          (K := K) (L := L) S x) =
      x.2.1 ⟨w, hw⟩ := by
  rw [relativeIdeleOfSPlaceFactors,
    relativeIdeleOfLocalData_finiteComponent,
    relativeLocalIdeleDataOfSPlaceFactors_finite_inside
      (K := K) (L := L) S x w hw]

omit [IsGalois K L] in
/-- At a finite place outside `S`, the assembled relative idele has the
coercion of the prescribed integral component. -/
@[simp]
theorem relativeIdeleOfSPlaceFactors_finiteComponent_outside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : RelativeIdeleSPlaceFactors (K := K) (L := L) S)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ S) :
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w
        (relativeIdeleOfSPlaceFactors
          (K := K) (L := L) S x) =
      (x.2.2 ⟨w, hw⟩ :
        (w.adicCompletion K ⊗[K] L)ˣ) := by
  rw [relativeIdeleOfSPlaceFactors,
    relativeIdeleOfLocalData_finiteComponent,
    relativeLocalIdeleDataOfSPlaceFactors_finite_outside
      (K := K) (L := L) S x w hw]

/-- The natural Galois action restricts to every finite-support
subgroup. -/
@[reducible]
noncomputable def
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S) := by
  letI :=
    relativeIdeleRestrictedMulDistribMulAction
      (K := K) (L := L)
  exact
    { smul := fun σ z =>
        ⟨σ • (z : RelativeIdeleGroup K L), by
          rw [mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff]
          intro w hw
          let :=
            scalarTensorUnitsAction
              (K := K) (L := L)
              (A := w.adicCompletion K)
          rw [RelativeIdeleGroup.finiteComponent_smul]
          exact
            relativeLocalTensorDecompositionIntegralUnitAt_smul
              (K := K) (L := L) w σ
              (RelativeIdeleGroup.finiteComponent
                (K := K) (L := L) w z)
              ((mem_relativeIdeleLocalTensorDecompositionSupportedSubgroup_iff
                (K := K) (L := L) S z).1 z.property w hw)⟩
      one_smul := by
        intro z
        apply Subtype.ext
        change
          (1 : L ≃ₐ[K] L) •
              (z : RelativeIdeleGroup K L) =
            (z : RelativeIdeleGroup K L)
        exact one_smul (L ≃ₐ[K] L) _
      mul_smul := by
        intro σ τ z
        apply Subtype.ext
        exact
          mul_smul σ τ
            (z : RelativeIdeleGroup K L)
      smul_one := by
        intro σ
        apply Subtype.ext
        change
          σ • (1 : RelativeIdeleGroup K L) = 1
        exact smul_one σ
      smul_mul := by
        intro σ x y
        apply Subtype.ext
        exact
          smul_mul' σ
            (x : RelativeIdeleGroup K L)
            (y : RelativeIdeleGroup K L) }

omit [NumberField L] [IsGalois K L] in
/-- Coercing the supported-subgroup action to the relative idele group
recovers the ambient Galois action. -/
@[simp]
theorem
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction_coe
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (z : relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S) :
    letI :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    ((σ • z :
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S) :
      RelativeIdeleGroup K L) =
      letI :=
        relativeIdeleRestrictedMulDistribMulAction
          (K := K) (L := L)
      σ • (z : RelativeIdeleGroup K L) :=
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_FiniteRestrictedProductBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.finitePlaceAdicCompletionMap_self_apply _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
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

/-- At one finite place of `K`, the canonical local tensor decomposition followed by completion
comparison identifies the tensor-unit group with the product of the concrete
adic unit groups at all finite places of `L` above it. -/
noncomputable def finitePlaceTensorUnitsEquivAboveAdic
    (w : HeightOneSpectrum (𝓞 K)) :
    (w.adicCompletion K ⊗[K] L)ˣ ≃*
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        (W.1.adicCompletion L)ˣ :=
  (finitePlaceLocalTensorDecompositionUnitsEquiv
      (K := K) (L := L) w).trans
    ((MulEquiv.piCongrRight fun u :
        AbsoluteValueExtension
          (HeightOneSpectrum.adicAbv K w) L =>
      Units.mapEquiv
        (finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w u).toMulEquiv).trans
      (piCongrLeftMulEquiv
        (fun W : {W : HeightOneSpectrum (𝓞 L) //
            finitePlaceBelow (K := K) W = w} =>
          (W.1.adicCompletion L)ˣ)
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w)))

/-- Evaluation of the finite-place tensor units equivalence at an
extension of the given adic absolute value. -/
@[simp]
theorem finitePlaceTensorUnitsEquivAboveAdic_apply_extension
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ)
    (u : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w x
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w u) =
      Units.mapEquiv
          (finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) w u).toMulEquiv
        (finitePlaceLocalTensorDecompositionUnitsComponent
          (K := K) (L := L) w u x) := by
  let P :=
    fun W : {W : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := K) W = w} =>
      (W.1.adicCompletion L)ˣ
  let e := finitePlaceExtensionEquivAbove (K := K) (L := L) w
  let f : ∀ a, P (e a) := fun a =>
    Units.mapEquiv
        (finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w a).toMulEquiv
      (finitePlaceLocalTensorDecompositionUnitsEquiv
        (K := K) (L := L) w x a)
  exact
    (Equiv.piCongrLeft_apply_apply P e f u).trans
      (congrArg
        (Units.mapEquiv
          (finitePlaceExtensionAdicCompletionRingEquiv
            (K := K) (L := L) w u).toMulEquiv)
        (finitePlaceLocalTensorDecompositionUnitsEquiv_apply
          (K := K) (L := L) w x u))

/-- Flatten products first over finite places of `K` and then over places
above them into one product over all finite places of `L`. -/
noncomputable def finitePlaceAbovePiMulEquiv :
    (∀ w : HeightOneSpectrum (𝓞 K),
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        (W.1.adicCompletion L)ˣ) ≃*
      ∀ W : HeightOneSpectrum (𝓞 L),
        (W.adicCompletion L)ˣ where
  toFun f W :=
    f (finitePlaceBelow (K := K) W) ⟨W, rfl⟩
  invFun f w W := f W.1
  left_inv f := by
    funext w W
    rcases W with ⟨W, hW⟩
    subst w
    rfl
  right_inv f := by
    funext W
    rfl
  map_mul' f g := by
    funext W
    rfl

/-- The unrestricted product of all finite local tensor-unit groups is the
unrestricted product of all concrete finite local unit groups of `L`. -/
noncomputable def relativeFiniteTensorPiMulEquiv :
    (∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ) ≃*
      ∀ W : HeightOneSpectrum (𝓞 L),
        (W.adicCompletion L)ˣ :=
  (MulEquiv.piCongrRight fun w =>
      finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w).trans
    (finitePlaceAbovePiMulEquiv (K := K) (L := L))

/-- Coordinate formula for the relative finite tensor units
equivalence. -/
@[simp]
theorem relativeFiniteTensorPiMulEquiv_apply
    (x : ∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ)
    (W : HeightOneSpectrum (𝓞 L)) :
    relativeFiniteTensorPiMulEquiv
        (K := K) (L := L) x W =
      finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L)
        (finitePlaceBelow (K := K) W)
        (x (finitePlaceBelow (K := K) W)) ⟨W, rfl⟩ :=
  rfl

/-- Coordinate formula for the inverse relative finite tensor units
equivalence. -/
@[simp]
theorem relativeFiniteTensorPiMulEquiv_symm_apply
    (y : ∀ W : HeightOneSpectrum (𝓞 L),
      (W.adicCompletion L)ˣ)
    (w : HeightOneSpectrum (𝓞 K)) :
    (relativeFiniteTensorPiMulEquiv
        (K := K) (L := L)).symm y w =
      (finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w).symm
        (fun W => y W.1) :=
  rfl

/-- A multiplicative equivalence carries units of one submonoid to units
of another exactly when it carries their underlying elements between
the two submonoids. -/
theorem unitsMapEquiv_mem_units_iff
    {R S : Type*} [CommMonoid R] [CommMonoid S]
    (e : R ≃* S) (A : Submonoid R) (B : Submonoid S)
    (h : ∀ y : R, e y ∈ B ↔ y ∈ A)
    (x : Rˣ) :
    Units.mapEquiv e x ∈ B.units ↔ x ∈ A.units := by
  rw [Submonoid.mem_units_iff, Submonoid.mem_units_iff]
  constructor
  · rintro ⟨hval, hinv⟩
    constructor
    · exact (h (x : R)).mp (by simpa using hval)
    · apply (h ((x⁻¹ : Rˣ) : R)).mp
      rw [← (Units.mapEquiv e).map_inv x] at hinv
      exact hinv
  · rintro ⟨hval, hinv⟩
    constructor
    · simpa using (h (x : R)).mpr hval
    · rw [← (Units.mapEquiv e).map_inv x]
      exact (h ((x⁻¹ : Rˣ) : R)).mpr hinv

/-- Cofinite quantification over finite places of `L` is equivalent to
cofinite quantification over finite places of `K`, uniformly over every
place above the chosen base place. -/
theorem eventually_finitePlace_iff_eventually_all_above
    (P : ∀ _W : HeightOneSpectrum (𝓞 L), Prop) :
    (∀ᶠ W : HeightOneSpectrum (𝓞 L) in Filter.cofinite, P W) ↔
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
          P W.1 := by
  constructor
  · intro h
    have hbad :
        {W : HeightOneSpectrum (𝓞 L) | ¬ P W}.Finite :=
      Filter.eventually_cofinite.mp h
    have himage :
        (finitePlaceBelow (K := K) ''
          {W : HeightOneSpectrum (𝓞 L) | ¬ P W}).Finite :=
      hbad.image _
    apply Filter.eventually_cofinite.mpr
    apply himage.subset
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw
    rw [Set.mem_image]
    push Not at hw
    rcases hw with ⟨W, hW⟩
    exact ⟨W.1, hW, W.2⟩
  · intro h
    have hfibre (w : HeightOneSpectrum (𝓞 K)) :
        Finite {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w} := by
      let : Fintype
          (AbsoluteValueExtension
            (HeightOneSpectrum.adicAbv K w) L) :=
        completionTensorDecomposition_extensionFintype
          (HeightOneSpectrum.adicAbv K w)
          (RayClass.adicAbv_isNontrivial w)
      exact
        Finite.of_equiv
          (AbsoluteValueExtension
            (HeightOneSpectrum.adicAbv K w) L)
          (finitePlaceExtensionEquivAbove
            (K := K) (L := L) w)
    have htendsto :
        Filter.Tendsto
          (finitePlaceBelow (K := K))
          Filter.cofinite Filter.cofinite :=
      Filter.Tendsto.cofinite_of_finite_preimage_singleton
        (f := finitePlaceBelow (K := K) (L := L))
        fun w => by
          change
            {W : HeightOneSpectrum (𝓞 L) |
              finitePlaceBelow (K := K) W = w}.Finite
          exact Set.finite_coe_iff.mp (hfibre w)
    filter_upwards [htendsto.eventually h] with W hW
    exact hW ⟨W, rfl⟩

omit [NumberField L] in
/-- Relative finite idele data are equal when their finite components
are equal. -/
@[ext]
theorem RelativeFiniteIdeleData.ext
    {a b : RelativeFiniteIdeleData (K := K) (L := L)}
    (hfinite : a.finite = b.finite) :
    a = b := by
  cases a
  cases b
  simp_all

/-- Adjoin the trivial infinite family, so that the established relative
idele support theorem can be applied to finite restricted data. -/
noncomputable def RelativeFiniteIdeleData.toLocalData
    (a : RelativeFiniteIdeleData (K := K) (L := L)) :
    RelativeLocalIdeleData (K := K) (L := L) where
  infinite _ := 1
  finite := a.finite
  eventually_integral := a.eventually_integral
  eventually_inverse_integral := a.eventually_inverse_integral
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_BaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
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

/-- An infinite place above `w`, regarded as an exact extension of the
underlying absolute value. -/
def infinitePlaceAboveToExtension
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w}) :
    AbsoluteValueExtension w.1 L := by
  refine ⟨W.1.1, ?_⟩
  intro x
  have h :=
    congrArg (fun v : InfinitePlace K => v x) W.2
  exact h

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- For a finite Galois extension, every extension of an infinite-place
absolute value is represented by an infinite place above the base
place. -/
theorem
    infinitePlaceAboveToExtension_surjective_of_isGalois
    [IsGalois K L]
    (w : InfinitePlace K) :
    Function.Surjective
      (infinitePlaceAboveToExtension
        (K := K) (L := L) w) := by
  intro u
  obtain ⟨W₀, hW₀⟩ :=
    InfinitePlace.comap_surjective
      (k := K) (K := L) w
  let W₀' :
      {W : InfinitePlace L //
        infinitePlaceBelow (K := K) W = w} :=
    ⟨W₀, hW₀⟩
  let u₀ : AbsoluteValueExtension w.1 L :=
    infinitePlaceAboveToExtension
      (K := K) (L := L) w W₀'
  obtain ⟨σ, hσ⟩ :=
    absoluteValueConjugacy w.1 w.isNontrivial u₀ u
  let Wσ : InfinitePlace L :=
    W₀.comap σ.toRingEquiv.toRingHom
  have hWσ :
      infinitePlaceBelow (K := K) Wσ = w := by
    apply InfinitePlace.ext
    intro x
    change W₀ (σ (algebraMap K L x)) = w x
    rw [σ.commutes]
    exact congrArg (fun v : InfinitePlace K => v x) hW₀
  refine ⟨⟨Wσ, hWσ⟩, ?_⟩
  rw [hσ]
  apply Subtype.ext
  rfl

/-- Infinite places of `L` above `w` are exactly the exact extensions of
the absolute value represented by `w`. -/
noncomputable def infinitePlaceAboveEquivExtension
    (w : InfinitePlace K) :
    {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w} ≃
      AbsoluteValueExtension w.1 L := by
  apply Equiv.ofBijective
    (infinitePlaceAboveToExtension
      (K := K) (L := L) w)
  constructor
  · intro W W' h
    have habs : W.1.1 = W'.1.1 :=
      congrArg
        (fun u : AbsoluteValueExtension w.1 L => u.1) h
    apply Subtype.ext
    apply Subtype.ext
    exact habs
  · intro u
    let M := finiteNormalClosure K L
    let e : L →ₐ[K] M :=
      finiteNormalClosureEmbedding K L
    let : Algebra L M :=
      e.toRingHom.toAlgebra
    let : IsScalarTower K L M :=
      IsScalarTower.of_algebraMap_eq'
        e.comp_algebraMap.symm
    let : FiniteDimensional L M :=
      FiniteDimensional.right K L M
    let hu : u.1.IsNontrivial :=
      u.isNontrivial w.isNontrivial
    let uOverL : AbsoluteValueExtension u.1 M :=
      pullbackAbsoluteValueExtension
        u.1 hu IsAlgClosed.lift
    let uM : AbsoluteValueExtension w.1 M :=
      { val := uOverL.1
        property := by
          intro x
          rw [IsScalarTower.algebraMap_apply K L M,
            uOverL.2, u.2] }
    obtain ⟨WM, hWM⟩ :=
      infinitePlaceAboveToExtension_surjective_of_isGalois
        (K := K) (L := M) w uM
    let WL : InfinitePlace L :=
      WM.1.comap (algebraMap L M)
    have hWL :
        infinitePlaceBelow (K := K) WL = w := by
      apply InfinitePlace.ext
      intro x
      change
        WM.1
            (algebraMap L M
              (algebraMap K L x)) =
          w x
      rw [← IsScalarTower.algebraMap_apply K L M]
      exact congrArg (fun v : InfinitePlace K => v x) WM.2
    refine ⟨⟨WL, hWL⟩, ?_⟩
    apply Subtype.ext
    ext x
    have hWMval :
        WM.1.1 = uM.1 :=
      congrArg Subtype.val hWM
    change
      WM.1.1 (algebraMap L M x) = u.1 x
    rw [hWMval]
    exact uOverL.2 x

/-- The absolute value underlying the extension corresponding to an
infinite place above `w`. -/
@[simp]
theorem infinitePlaceAboveEquivExtension_apply_val
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w}) :
    (infinitePlaceAboveEquivExtension
      (K := K) (L := L) w W).1 = W.1.1 :=
  rfl

/-- Reindex the relative completion product by actual infinite
places above `w`. -/
noncomputable def infiniteCompletionProductReindexAbove
    (w : InfinitePlace K) :
    (∀ u : AbsoluteValueExtension w.1 L,
      u.1.Completionˣ) ≃*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.1.Completionˣ := by
  let e :=
    Equiv.piCongrLeft'
      (fun u : AbsoluteValueExtension w.1 L =>
        u.1.Completionˣ)
      (infinitePlaceAboveEquivExtension
        (K := K) (L := L) w).symm
  exact
    { e with
      map_mul' := by
        intro x y
        funext W
        rfl }

/-- Replace the absolute-value completion in every factor by mathlib's
concrete infinite-place completion. -/
noncomputable def infiniteCompletionProductEquivAbove
    (w : InfinitePlace K) :
    (∀ u : AbsoluteValueExtension w.1 L,
      u.1.Completionˣ) ≃*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completionˣ :=
  (infiniteCompletionProductReindexAbove
    (K := K) (L := L) w).trans
    (MulEquiv.piCongrRight fun W =>
      Units.mapEquiv
        (InfinitePlace.Completion.equiv W.1).symm.toMulEquiv)

/-- The canonical local tensor decomposition for the actual archimedean tensor component, with
codomain indexed by concrete infinite places above the base place. -/
noncomputable def infinitePlaceTensorUnitsEquivAbove
    (w : InfinitePlace K) :
    (w.Completion ⊗[K] L)ˣ ≃*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completionˣ := by
  letI : ∀ u : AbsoluteValueExtension w.1 L,
      Algebra w.1.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra w.1 u.1 u.2
  exact
    (infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) w).trans
      ((localTensorUnitsEquivCompletionProduct
        (K := K) (L := L) w.1 w.isNontrivial).trans
        (infiniteCompletionProductEquivAbove
          (K := K) (L := L) w))

/-- Evaluation formula for the archimedean relative-to-ordinary
comparison at a concrete infinite place above the base place. -/
@[simp]
theorem infinitePlaceTensorUnitsEquivAbove_apply
    (w : InfinitePlace K)
    (z : (w.Completion ⊗[K] L)ˣ)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w}) :
    infinitePlaceTensorUnitsEquivAbove
        (K := K) (L := L) w z W =
      Units.mapEquiv
          (InfinitePlace.Completion.equiv W.1).symm.toMulEquiv
        (localTensorUnitsEquivCompletionProduct
          w.1 w.isNontrivial
          (infinitePlaceLocalTensorUnitsEquiv
            (K := K) (L := L) w z)
        (infinitePlaceAboveEquivExtension
          (K := K) (L := L) w W)) :=
  rfl

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- After replacing the concrete completion by the underlying
absolute-value completion, scalar extension of a local unit is the pure
tensor with right factor one. -/
@[simp]
theorem infinitePlaceLocalTensorUnitsEquiv_infiniteLocalIdeleInclusion_coe
    (w : InfinitePlace K) (x : w.Completionˣ) :
    (infinitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) w
        (infiniteLocalIdeleInclusion
          (K := K) (L := L) w x) :
      LocalClassFieldTheory.LocalTensorAlgebra (L := L) w.1) =
      infinitePlaceCompletionAlgEquiv w
          (x : w.Completion) ⊗ₜ[K] (1 : L) := by
  rfl

/-- Flatten the products over base infinite places and places above them
to the product over all infinite places of `L`. -/
noncomputable def infinitePlaceAbovePiMulEquiv :
    (∀ w : InfinitePlace K,
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completionˣ) ≃*
      ∀ W : InfinitePlace L, W.Completionˣ where
  toFun f W :=
    f (infinitePlaceBelow (K := K) W) ⟨W, rfl⟩
  invFun f w W := f W.1
  left_inv f := by
    funext w W
    rcases W with ⟨W, hW⟩
    subst w
    rfl
  right_inv f := by
    funext W
    rfl
  map_mul' f g := by
    funext W
    rfl

/-- The unrestricted product of all archimedean tensor-unit factors is
the product of the concrete archimedean local unit groups of `L`. -/
noncomputable def relativeInfiniteTensorPiMulEquiv :
    (∀ w : InfinitePlace K,
      (w.Completion ⊗[K] L)ˣ) ≃*
      ∀ W : InfinitePlace L, W.Completionˣ :=
  (MulEquiv.piCongrRight fun w =>
    infinitePlaceTensorUnitsEquivAbove
      (K := K) (L := L) w).trans
    (infinitePlaceAbovePiMulEquiv
      (K := K) (L := L))

/-- Evaluation of the archimedean tensor-product comparison at an
infinite place of the extension field. -/
@[simp]
theorem relativeInfiniteTensorPiMulEquiv_apply
    (f : ∀ w : InfinitePlace K, (w.Completion ⊗[K] L)ˣ)
    (W : InfinitePlace L) :
    relativeInfiniteTensorPiMulEquiv (K := K) (L := L) f W =
      infinitePlaceTensorUnitsEquivAbove
        (K := K) (L := L)
        (infinitePlaceBelow (K := K) W)
        (f (infinitePlaceBelow (K := K) W))
        ⟨W, rfl⟩ := rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_AdeleBaseChange
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.mem_finitePlaceDecompositionGroup_iff _root_.restrictAbsoluteValueExtensionToIntermediate_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Scalar extension from relative to ordinary adeles

This file upgrades the relative-to-ordinary idele comparison to the
underlying adele rings.  The additive structure is needed to transport
determinant norms in a field tower.
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

/-- The finite local tensor algebra, decomposed into the concrete adic
completions above the chosen base place. -/
noncomputable def finitePlaceTensorRingEquivAboveAdic
    (w : HeightOneSpectrum (𝓞 K)) :
    (w.adicCompletion K ⊗[K] L) ≃+*
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        W.1.adicCompletion L := by
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  letI : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  let e₁ :
      (w.adicCompletion K ⊗[K] L) ≃+*
        (∀ u : AbsoluteValueExtension vK L,
          u.1.Completion) :=
    (relativeFinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w).symm.toRingEquiv.trans
      (completionTensorDecomposition_left
        (K := K) (L := L) vK hvK).toRingEquiv
  let e₂ :
      (∀ u : AbsoluteValueExtension vK L,
          u.1.Completion) ≃+*
        (∀ u : AbsoluteValueExtension vK L,
          (finitePlaceExtensionCentre
            (K := K) (L := L) w u).adicCompletion L) :=
    RingEquiv.piCongrRight fun u =>
      finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w u
  let e₃ :
      (∀ u : AbsoluteValueExtension vK L,
          (finitePlaceExtensionCentre
            (K := K) (L := L) w u).adicCompletion L) ≃+*
        (∀ W : {W : HeightOneSpectrum (𝓞 L) //
            finitePlaceBelow (K := K) W = w},
          W.1.adicCompletion L) :=
    RingEquiv.piCongrLeft
      (fun W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w} =>
        W.1.adicCompletion L)
      (finitePlaceExtensionEquivAbove
        (K := K) (L := L) w)
  exact e₁.trans (e₂.trans e₃)

/-- Evaluation of the finite-place tensor equivalence at an extension of
the given adic absolute value. -/
@[simp]
theorem finitePlaceTensorRingEquivAboveAdic_apply_extension
    (w : HeightOneSpectrum (𝓞 K))
    (x : w.adicCompletion K ⊗[K] L)
    (u : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L) :
    finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w x
        (finitePlaceExtensionEquivAbove
          (K := K) (L := L) w u) =
      finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) w u
        (finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w u x) := by
  let P :=
    fun W : {W : HeightOneSpectrum (𝓞 L) //
        finitePlaceBelow (K := K) W = w} =>
      W.1.adicCompletion L
  let e := finitePlaceExtensionEquivAbove (K := K) (L := L) w
  let f : ∀ a, P (e a) := fun a =>
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) w a
      (finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w a x)
  exact Equiv.piCongrLeft_apply_apply P e f u

/-- Reindex the archimedean relative-tensor product by concrete places
above `w`, before replacing the completion wrappers. -/
noncomputable def infiniteCompletionRingProductReindexAbove
    (w : InfinitePlace K) :
    (∀ u : AbsoluteValueExtension w.1 L,
      u.1.Completion) ≃+*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.1.Completion := by
  let e :=
    Equiv.piCongrLeft'
      (fun u : AbsoluteValueExtension w.1 L =>
        u.1.Completion)
      (infinitePlaceAboveEquivExtension
        (K := K) (L := L) w).symm
  exact
    { e with
      map_add' := by
        intro x y
        funext W
        rfl
      map_mul' := by
        intro x y
        funext W
        rfl }

/-- The archimedean local tensor algebra, decomposed into the concrete
infinite completions above the chosen base place. -/
noncomputable def infinitePlaceTensorRingEquivAbove
    (w : InfinitePlace K) :
    (w.Completion ⊗[K] L) ≃+*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completion := by
  letI : ∀ u : AbsoluteValueExtension w.1 L,
      Algebra w.1.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra w.1 u.1 u.2
  exact
    (infinitePlaceLocalTensorAlgEquiv
      (K := K) (L := L) w).toRingEquiv.trans
    ((completionTensorDecomposition_left
        (K := K) (L := L) w.1
        w.isNontrivial).toRingEquiv.trans
      ((infiniteCompletionRingProductReindexAbove
          (K := K) (L := L) w).trans
        (RingEquiv.piCongrRight fun W =>
          (InfinitePlace.Completion.equiv W.1).symm)))

/-- Evaluation of the infinite-place tensor equivalence at a place above
the chosen base place. -/
@[simp]
theorem infinitePlaceTensorRingEquivAbove_apply
    (w : InfinitePlace K)
    (z : w.Completion ⊗[K] L)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w}) :
    infinitePlaceTensorRingEquivAbove
        (K := K) (L := L) w z W =
      (InfinitePlace.Completion.equiv W.1).symm
        (completionTensorDecomposition_left
          w.1 w.isNontrivial
          (infinitePlaceLocalTensorAlgEquiv
            (K := K) (L := L) w z)
          (infinitePlaceAboveEquivExtension
            (K := K) (L := L) w W)) :=
  rfl

/-- Flatten the products over finite base places and places above them
to the product over all finite places of the extension field. -/
noncomputable def finitePlaceAbovePiRingEquiv :
    (∀ w : HeightOneSpectrum (𝓞 K),
      ∀ W : {W : HeightOneSpectrum (𝓞 L) //
          finitePlaceBelow (K := K) W = w},
        W.1.adicCompletion L) ≃+*
      ∀ W : HeightOneSpectrum (𝓞 L),
        W.adicCompletion L where
  toFun f W :=
    f (finitePlaceBelow (K := K) W) ⟨W, rfl⟩
  invFun f w W := f W.1
  left_inv f := by
    funext w W
    rcases W with ⟨W, hW⟩
    subst w
    rfl
  right_inv f := by
    funext W
    rfl
  map_add' f g := by
    funext W
    rfl
  map_mul' f g := by
    funext W
    rfl

/-- All finite local tensor rings, flattened to the concrete finite
completion family of the extension field. -/
noncomputable def relativeFiniteTensorPiRingEquiv :
    (∀ w : HeightOneSpectrum (𝓞 K),
      w.adicCompletion K ⊗[K] L) ≃+*
      ∀ W : HeightOneSpectrum (𝓞 L),
        W.adicCompletion L :=
  (RingEquiv.piCongrRight fun w =>
      finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w).trans
    (finitePlaceAbovePiRingEquiv (K := K) (L := L))

/-- Coordinate formula for the relative finite tensor product
equivalence. -/
@[simp]
theorem relativeFiniteTensorPiRingEquiv_apply
    (x : ∀ w : HeightOneSpectrum (𝓞 K),
      w.adicCompletion K ⊗[K] L)
    (W : HeightOneSpectrum (𝓞 L)) :
    relativeFiniteTensorPiRingEquiv
        (K := K) (L := L) x W =
      finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L)
        (finitePlaceBelow (K := K) W)
        (x (finitePlaceBelow (K := K) W)) ⟨W, rfl⟩ :=
  rfl

/-- Coordinate formula for the inverse relative finite tensor product
equivalence. -/
@[simp]
theorem relativeFiniteTensorPiRingEquiv_symm_apply
    (y : ∀ W : HeightOneSpectrum (𝓞 L),
      W.adicCompletion L)
    (w : HeightOneSpectrum (𝓞 K)) :
    (relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)).symm y w =
      (finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w).symm
        (fun W => y W.1) :=
  rfl

/-- Pull the finite coordinates of an ordinary adele back to the
relative local tensor family. -/
noncomputable def finiteAdeleRelativeTensorFamily
    (y : IsDedekindDomain.FiniteAdeleRing (𝓞 L) L) :
    ∀ w : HeightOneSpectrum (𝓞 K),
      w.adicCompletion K ⊗[K] L :=
  (relativeFiniteTensorPiRingEquiv
    (K := K) (L := L)).symm (fun W => y W)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_NormLocalOrder
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.chosenFinitePlaceBaseValuationCompatible _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.finitePlaceTensorRingEquivAboveAdic_apply_extension _root_.finitePlaceTensorUnitsEquivAboveAdic_apply_extension _root_.relativeFiniteTensorPiMulEquiv_apply _root_.relativeFiniteTensorPiMulEquiv_symm_apply _root_.relativeFiniteTensorPiRingEquiv_apply _root_.relativeFiniteTensorPiRingEquiv_symm_apply
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

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- The local order of the actual norm between finite-place completions is
multiplied by the inertia degree of the upstairs prime. -/
theorem localOrder_normUnits
    (v₀ : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀})
    (x : (W.1.adicCompletion L)ˣ) :
    letI : Algebra
        (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
    (localOrder v₀
      (LocalFieldTheory.normUnits
        (v₀.adicCompletion K) (W.1.adicCompletion L) x)).toAdd =
      (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
        (localOrder W.1 x).toAdd := by
  classical
  let F := v₀.adicCompletion K
  let E := W.1.adicCompletion L
  let : Algebra F E :=
    (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
  let : IsScalarTower K F E :=
    finitePlaceAdicCompletionMap_isScalarTower K L v₀ W
  let : FiniteDimensional F E :=
    finitePlaceAdicCompletionMap_moduleFinite K L v₀ W
  let : CharZero F :=
    charZero_of_injective_algebraMap
      (algebraMap K F).injective
  let : Algebra.IsIntegral F E :=
    Algebra.IsIntegral.of_finite F E
  let : Algebra.IsSeparable F E :=
    Algebra.IsSeparable.of_integral F E
  let νF : Valuation F (WithZero (Multiplicative ℤ)) :=
    Valued.v
  let νE : Valuation E (WithZero (Multiplicative ℤ)) :=
    Valued.v
  have hνF : Function.Surjective νF := by
    simpa [F, νF] using
      v₀.valuedAdicCompletion_surjective K
  have hνE : Function.Surjective νE := by
    simpa [E, νE] using
      W.1.valuedAdicCompletion_surjective L
  let : ValuativeRel F :=
    ValuativeRel.ofValuation νF
  let : ValuativeRel E :=
    ValuativeRel.ofValuation νE
  let : νF.Compatible :=
    Valuation.Compatible.ofValuation νF
  let : νE.Compatible :=
    Valuation.Compatible.ofValuation νE
  let : νF.IsNontrivial := by
    obtain ⟨π, hπ⟩ :=
      hνF (WithZero.exp (-1 : ℤ))
    refine ⟨⟨π, ?_, ?_⟩⟩
    · rw [hπ]
      simp
    · rw [hπ]
      change
        WithZero.exp (-1 : ℤ) ≠
          WithZero.exp (0 : ℤ)
      simp
  let : νE.IsNontrivial := by
    obtain ⟨π, hπ⟩ :=
      hνE (WithZero.exp (-1 : ℤ))
    refine ⟨⟨π, ?_, ?_⟩⟩
    · rw [hπ]
      simp
    · rw [hπ]
      change
        WithZero.exp (-1 : ℤ) ≠
          WithZero.exp (0 : ℤ)
      simp
  let : ValuativeRel.IsNontrivial F :=
    (ValuativeRel.isNontrivial_iff_isNontrivial νF).2
      inferInstance
  let : ValuativeRel.IsNontrivial E :=
    (ValuativeRel.isNontrivial_iff_isNontrivial νE).2
      inferInstance
  let : IsValuativeTopology F :=
    LocalFieldTheory.isValuativeTopology_of_valued_ofValuation
      F (WithZero (Multiplicative ℤ))
  let : IsValuativeTopology E :=
    LocalFieldTheory.isValuativeTopology_of_valued_ofValuation
      E (WithZero (Multiplicative ℤ))
  let : IsNonarchimedeanLocalField F :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let : IsNonarchimedeanLocalField E :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  let ν₀F := ValuativeRel.valuation F
  let ν₀E := ValuativeRel.valuation E
  let : W.1.asIdeal.LiesOver v₀.asIdeal := by
    constructor
    exact congrArg HeightOneSpectrum.asIdeal W.2.symm
  let : ν₀F.HasExtension ν₀E := by
    apply Valuation.HasExtension.ofComapInteger
    ext z
    change
      ν₀E (algebraMap F E z) ≤ 1 ↔
        ν₀F z ≤ 1
    rw [(ValuativeRel.isEquiv ν₀E νE).le_one_iff_le_one,
      (ValuativeRel.isEquiv ν₀F νF).le_one_iff_le_one]
    have hmap :
        νE (algebraMap F E z) =
          νF z ^
            W.1.asIdeal.ramificationIdx (𝓞 K) := by
      have h :=
        finitePlaceAdicCompletionMap_valued
          K L v₀ W z
      rw [Ideal.ramificationIdx'_eq_ramificationIdx
        v₀.asIdeal W.1.asIdeal v₀.ne_bot] at h
      exact h
    rw [hmap,
      pow_le_one_iff
        (W.1.asIdeal.ramificationIdx_pos
          (𝓞 K)).ne']
  let : Algebra 𝒪[F] E :=
    Algebra.ofSubsemiring 𝒪[F]
  let : IsIntegralClosure 𝒪[E] 𝒪[F] E :=
    LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure F E
  have hNormValue :=
    LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparable
      F E x
  rw [
    normalizedValue_eq_withZeroLog_of_surjective
      F νF hνF
        (LocalFieldTheory.normUnits F E x),
    normalizedValue_eq_withZeroLog_of_surjective
      E νE hνE x
  ] at hNormValue
  have hResidueDegree :
      Module.finrank 𝓀[F] 𝓀[E] =
        W.1.asIdeal.inertiaDeg (𝓞 K) := by
    apply
      Nat.pow_right_injective
        (Nat.succ_le_iff.mpr
          (HeightOneSpectrum.one_lt_absNorm v₀))
    calc
      Ideal.absNorm v₀.asIdeal ^
            Module.finrank 𝓀[F] 𝓀[E] =
          Nat.card 𝓀[F] ^
            Module.finrank 𝓀[F] 𝓀[E] := by
              rw [
                absNorm_eq_card_intrinsicAdicResidueField
                  K v₀
              ]
      _ = Nat.card 𝓀[E] :=
        Module.natCard_eq_pow_finrank.symm
      _ = Ideal.absNorm W.1.asIdeal := by
        rw [
          absNorm_eq_card_intrinsicAdicResidueField
            L W.1
        ]
      _ =
          Ideal.absNorm v₀.asIdeal ^
            W.1.asIdeal.inertiaDeg (𝓞 K) := by
        exact
          (Ideal.absNorm_pow_inertiaDeg
            v₀.asIdeal W.1.asIdeal).symm
  rw [hResidueDegree] at hNormValue
  rw [localOrder_apply, localOrder_apply]
  change
    -WithZero.log
        (νF
          (LocalFieldTheory.normUnits F E x : F)) =
      (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
        -WithZero.log (νE (x : E))
  calc
    -WithZero.log
          (νF
            (LocalFieldTheory.normUnits F E x : F)) =
        -((W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
          WithZero.log (νE (x : E))) := by
            rw [hNormValue]
    _ =
        (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
          -WithZero.log (νE (x : E)) := by
            ring

end FiniteIdeleGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdeleClassPowerLocalUnitQuotient_ArchimedeanPowerIndex
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Archimedean power indices in idele class quotients

This file defines the concrete idele-class subgroup attached to local power
conditions and computes its archimedean local indices.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The subgroup `C_K(S,T) = h(S,T)Kˣ/Kˣ` inside the idele class
group. -/
def ideleClassPowerLocalUnitSubgroup
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (IdeleClassGroup K) :=
  (idelePowerLocalUnitSubgroup (K := K) n S T).map
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup K))

/-- The quotient whose cardinality is the index
`[C_K : C_K(S,T)]`. -/
abbrev IdeleClassPowerLocalUnitQuotient
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :=
  IdeleClassGroup K ⧸
    ideleClassPowerLocalUnitSubgroup (K := K) n S T


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_NormRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norm--restriction for finite-place Artin homomorphisms

This module proves norm--restriction naturality for finite-place Artin maps in an actual square of number fields and their chosen completed local extensions.
-/

open scoped Classical IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

noncomputable def finitePlaceConcreteNormUnits
    {K' : Type}
    [Field K'] [NumberField K'] [Algebra K K']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v) :
    (W.adicCompletion K')ˣ →* (v.adicCompletion K)ˣ := by
  letI : Algebra (v.adicCompletion K) (W.adicCompletion K') :=
    (finitePlaceAdicCompletionMap
      K K' v ⟨W, hW⟩).toAlgebra
  exact LocalFieldTheory.normUnits
    (v.adicCompletion K) (W.adicCompletion K')

end Reciprocity
end GlobalClassFieldTheory
end
end


