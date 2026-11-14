-- Prove2me | Definitions.Def_OAIQ244Duke038
-- name    : OAIQ244Duke038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:39:00.32145+00:00
-- url     : https://prove2.me/theorems/929125ad-ecf8-4798-ad40-bfa4cf4a2291
-- title:
--   Definitions bundle OAIQ244Duke038 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 76 declarations of OpenAI's Lean: 23 definitions, 1 inductive type or structure, 1 instance and 51 theorems. The definitions and types are `ClassFormation.DegreeData.frobeniusFixedFiniteExtension`, `ClassFormation.DegreeData.unramifiedFrobenius`, `ClassFormation.ValuationData.canonicalValueQuotientEquiv`, `ClassFormation.ValuationData.unramifiedReciprocity_equiv_of_generator`, `ClassFormation.ValuationData.unramifiedReciprocity_valuationEquiv`, `CyclicCohomology.additiveNormSubgroup`, `CyclicCohomology.herbrandHMinusOneProdEquiv`, `FinitePlaceCompletionIntegralUniformizer`, `FinitePlaceSplitsCompletelyInExtension`, `LocalClassFieldTheory.B`, `LocalFieldTheory.DiscreteValuationField.fieldNormFiltrationPreimageSubgroup`, `LocalFieldTheory.DiscreteValuationField.fieldNormFiltrationQuotientMap`, `LocalFieldTheory.DiscreteValuationField.fieldNormMapLevelOfMapsFiltrationLevels`, `LocalFieldTheory.DiscreteValuationField.fieldNormMapsFiltrationLevels`, `LocalFieldTheory.DiscreteValuationField.fieldNormQuotientMap`, `LocalFieldTheory.DiscreteValuationField.valuedFieldNorm`, `LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitOfValuationMapZero`, `LocalFieldTheory.IsNonarchimedeanLocalField.multiplicativeIntegerValuation`, `LocalFieldTheory.IsNonarchimedeanLocalField.uniformizerUnitFactor`, `LocalFieldTheory.principalUnitsSuccQuotAddEquivResidue`, `finitePlaceIdealResidueEquivCompletion`, `finitePlaceIntegerToCompletion`, `integralTensorControlElement`, `integralTensorControlIdeal`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AbstractClassFieldTheory_Reciprocity_Construction_CanonicalUnramifiedNormQuotient`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusDescent`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusField`, `AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusSemigroup`, `AbstractClassFieldTheory_Reciprocity_Construction_MainFiniteReciprocity`, `AbstractClassFieldTheory_Reciprocity_Construction_UnramifiedNormQuotient`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice`, `AlgebraicNumberTheory_Completion_IntegerRingComparison`, `AlgebraicNumberTheory_Completion_UnramifiedComparison_IdealToCompletion`, `AlgebraicNumberTheory_Idele_Extension_NormLocalOrder`, `AlgebraicNumberTheory_Ramification_Splitting_NormalClosure`, `Cyclic_Herbrand_HerbrandLowDegree_BinaryProduct`, `Cyclic_Herbrand_Permutation_Module`, `Cyclic_Herbrand_PrincipalUnits_QuotientTower`, `Cyclic_TateH0_NormImage`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedNormalization`, `LocalField_DiscreteValuationField_FieldNorm`, `LocalField_NonarchimedeanLocalField_IdealQuotients`, `LocalField_NonarchimedeanLocalField_SeparableNormValuation`, `LocalField_NonarchimedeanLocalField_Valuation`, `LocalField_NonarchimedeanLocalField_ValuationExactSequence`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke025`, `OAIQ244Duke026`, `OAIQ244Duke027`, `OAIQ244Duke028`, `OAIQ244Duke029` and `OAIQ244Duke033` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke045`, `OAIQ244Duke046`, `OAIQ244Duke047`, `OAIQ244Duke048`, `OAIQ244Duke049`, `OAIQ244Duke050`, `OAIQ244Duke051` and `OAIQ244Duke052`.
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
import Mathlib.Algebra.GroupWithZero.Action.Prod
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
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Definitions.Def_OAIQ244Duke025
import Definitions.Def_OAIQ244Duke026
import Definitions.Def_OAIQ244Duke027
import Definitions.Def_OAIQ244Duke028
import Definitions.Def_OAIQ244Duke029
import Definitions.Def_OAIQ244Duke033

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusField
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# The abstract reciprocity construction: the field fixed by a Frobenius lift

This file passes from the group-dual `Γ` of the Frobenius fixed-field theorem to the actual
abstract field `Σ`.  Thus `G_Σ` is the inverse image of `Γ` under
`G_K → G_K / I_L`, embedded back into the ambient profinite group.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The Frobenius fixed field bundled with its finite extension data. -/
def frobeniusFixedFiniteExtension (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK) :
    FiniteAbstractExtension G where
  field := D.frobeniusFixedField K L hLK σ
  base := K.field
  below := D.frobeniusFixedField_le K L hLK σ
  finiteQuotient := D.frobeniusFixedField_finite K L hLK σ

end DegreeData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusSemigroup
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# The abstract reciprocity construction: the Frobenius semigroup

The set `Frob(\widetilde L | K)` from  is closed under multiplication:
normalized degrees are positive natural numbers and add under products.
-/

noncomputable section

namespace DegreeData

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The induced multiplication makes the Frobenius elements a semigroup. -/
instance frobeniusElementsSemigroup (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (CyclicCohomology.extensionSubgroup (G := G)
      K.field L hLK).Normal] :
    Semigroup (D.FrobeniusElements K L hLK) where
  mul_assoc σ τ υ := by
    apply Subtype.ext
    change (σ.1 * τ.1) * υ.1 = σ.1 * (τ.1 * υ.1)
    exact mul_assoc σ.1 τ.1 υ.1

end DegreeData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_UnramifiedNormQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusExponent_powerOfDegreeOne _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.frobeniusPowerSum_coe _root_.ClassFormation.DegreeData.frobeniusQuotientAction_mk _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isTotallyRamified_iff _root_.ClassFormation.FiniteGaloisSubextension.toGaloisSubextension_isUnramified_iff _root_.ClassFormation.ValuationData.canonicalUnramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.canonicalValueQuotientHom_mk _root_.ClassFormation.ValuationData.canonicalValueReduction_one _root_.ClassFormation.ValuationData.mem_infiniteUnitAddSubgroup_iff _root_.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iff _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.conjugateStableAction_coe _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed_val _root_.LocalClassFieldTheory.embeddedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe _root_.LocalClassFieldTheory.finiteGaloisUnitsEquivAbstractFixed_coe _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_apply _root_.LocalClassFieldTheory.finiteResidueFrobeniusFromZHat_one _root_.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalClassFieldTheory.residueAbsoluteDegreeIn_frobenius _root_.LocalClassFieldTheory.residueAbsoluteFrobenius_one _root_.LocalClassFieldTheory.residueFrobeniusToLimit_apply_component _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.ClassFormation.DegreeData.inertiaConjugationCosetEquiv_mk _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction, the unramified norm-quotient equivalence: the unramified norm quotient

For a finite unramified Galois extension `L / K`, normalized valuation
identifies the actual norm quotient `A_K / N_{L/K} A_L` with
`ℤ / [L : K]ℤ`.  The only non-formal part of injectivity is the unit
correction: the unit-cohomology axiom (`H⁰ = 0`) makes every unit of `K` the norm
of a unit of `L`.
-/

noncomputable section

section unramifiedFrobenius

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The arithmetic Frobenius `φ_{L/K}`, obtained by restricting `φ_K`. -/
def unramifiedFrobenius
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal] :
    K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK :=
  D.frobeniusRestriction K L hLK
    (D.chosenUnramifiedFrobeniusLift K L hLK)

/-- In an unramified extension, arithmetic Frobenius generates the actual
finite Galois quotient. -/
theorem unramifiedFrobenius_generates
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    ∀ x : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK,
      x ∈ Subgroup.zpowers (D.unramifiedFrobenius K L hLK) := by
  let φ : K.field.toSubgroup := Classical.choose
    (D.normalizedDegree_surjective K
      (Multiplicative.ofAdd (1 : ZHat)))
  have hφ : D.normalizedDegree K φ =
      Multiplicative.ofAdd (1 : ZHat) :=
    Classical.choose_spec
      (D.normalizedDegree_surjective K
        (Multiplicative.ofAdd (1 : ZHat)))
  simpa only [unramifiedFrobenius, chosenUnramifiedFrobeniusLift, φ,
    frobeniusRestriction, extensionRestriction_mk] using
    D.quotient_generator_of_unramified_degree_one
      K L hLK hUnramified φ hφ

/-- Additive form of the preceding generator statement, matching the
domain of the reciprocity homomorphism in the finite reciprocity equivalence. -/
theorem unramifiedFrobenius_zmultiples_eq_top
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    AddSubgroup.zmultiples
      (Additive.ofMul (D.unramifiedFrobenius K L hLK)) = ⊤ := by
  ext x
  constructor
  · intro _
    exact AddSubgroup.mem_top x
  · intro _
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (D.unramifiedFrobenius_generates K L hLK hUnramified x.toMul)
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨m, ?_⟩
    change Additive.ofMul
      ((D.unramifiedFrobenius K L hLK) ^ m) = x
    exact congrArg Additive.ofMul hm

end DegreeData

end unramifiedFrobenius

section valuationQuotient

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/--
The specified map is surjective: `Function.Surjective (v.unramifiedNormQuotientValuation K L hLK
hUnramified)`.
-/
theorem unramifiedNormQuotientValuation_surjective
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    Function.Surjective
      (v.unramifiedNormQuotientValuation K L hLK hUnramified) := by
  intro z
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  obtain ⟨c, hc⟩ :=
    v.valueModulo_surjective n E.degree.property z
  obtain ⟨a, ha⟩ := v.normalizedValuation_surjective K c
  refine ⟨finiteNormClass A K.field L hLK a, ?_⟩
  rw [v.unramifiedNormQuotientValuation_finiteNormClass]
  change v.valueModulo n E.degree.property
      (v.valuationAt K a) = z
  rw [ha]
  exact hc

/-- The unit argument: modulo valuation, the unit-cohomology axiom makes the
remaining unit an actual norm. -/
theorem unramifiedNormQuotientValuation_injective
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    Function.Injective
      (v.unramifiedNormQuotientValuation K L hLK hUnramified) := by
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  have hUn : E.IsUnramified D := by
    change (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D
    exact hUnramified
  have hkernel : ∀ q : FiniteNormQuotient A K.field L hLK,
      v.unramifiedNormQuotientValuation K L hLK hUnramified q = 0 → q = 0 := by
    intro q
    refine FiniteNormQuotient.induction_on A K.field L hLK q ?_
    intro a ha
    change v.unramifiedValuationHom K L hLK a = 0 at ha
    change v.valueModulo n E.degree.property
        (v.valuationAt K a) = 0 at ha
    obtain ⟨z, haz⟩ :=
      (v.valueModulo_eq_zero_iff n E.degree.property
        (v.valuationAt K a)).1 ha
    obtain ⟨b, hb⟩ := v.normalizedValuation_surjective E.field z
    let normb : ambientFixedAddSubgroup A K.field :=
      relativeNorm A K.field L hLK b
    have htower := v.normalizedValuation_tower E b
    change (E.residueDegree D : ℕ) • _ = _ at htower
    rw [E.residueDegree_eq_degree_of_isUnramified D hUn] at htower
    have hnormb : v.valuationAt K normb = n • z := by
      apply Subtype.ext
      calc
        ((v.valuationAt K normb : v.valueGroup) : ZHat) =
            n • ((v.valuationAt E.field b : v.valueGroup) : ZHat) := htower.symm
        _ = n • ((z : v.valueGroup) : ZHat) := by rw [hb]
        _ = (((n • z : v.valueGroup)) : ZHat) := rfl
    let u : v.unitAddSubgroup K :=
      ⟨a - normb, by
        rw [v.mem_unitAddSubgroup_iff, map_sub, haz, hnormb, sub_self]⟩
    let KR := K.toFiniteResidueAbstractField D
    let : (extensionSubgroup KR.field L hLK).Normal := by
      change (extensionSubgroup K.field L hLK).Normal
      exact hnormal
    let : Finite
        (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
      change Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)
      exact hfinite
    obtain ⟨g, hg⟩ :=
      D.exists_quotient_generator_of_unramified
        KR L hLK hUnramified
    let : Fintype
        (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) :=
      Fintype.ofFinite _
    let Euc : FiniteUnramifiedCyclicExtension D K :=
      { field := L
        below := hLK
        normal := hnormal
        finite := hfinite
        generator := g
        generates := hg
        unramified := hUnramified }
    have hzero :
        CategoryTheory.Limits.IsZero
            (tateCohomology (Euc.unitRepresentation v) 0) ∧
          CategoryTheory.Limits.IsZero
            (tateCohomology (Euc.unitRepresentation v) (-1)) :=
      hAxiom K Euc
    obtain ⟨ε, hε⟩ :=
      v.exists_unit_relativeNorm_eq_of_tateHZero_isZero
        Euc.toFiniteAbstractFieldExtension Euc.normal
          Euc.toFiniteAbstractFieldExtension_isUnramified
          g hg hzero.1 u
    change v.unitAddSubgroup E.field at ε
    change relativeNorm A K.field L hLK ε.1 = u.1 at hε
    apply (finiteNormClass_eq_zero_iff A K.field L hLK a).2
    refine ⟨b + ε.1, ?_⟩
    rw [map_add, hε]
    change normb + (a - normb) = a
    abel
  intro x y hxy
  apply sub_eq_zero.mp
  apply hkernel
  rw [map_sub, hxy, sub_self]

/-- **the unramified norm-quotient equivalence (valuation part).**  For finite unramified `L / K`,
valuation induces `A_K / N_{L/K}A_L ≃ ℤ/[L:K]ℤ`. -/
def unramifiedReciprocity_valuationEquiv
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    FiniteNormQuotient A K.field L hLK ≃+
      ZMod ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) :=
  AddEquiv.ofBijective
    (v.unramifiedNormQuotientValuation K L hLK hUnramified)
    ⟨v.unramifiedNormQuotientValuation_injective hAxiom K L hLK
        hUnramified,
      v.unramifiedNormQuotientValuation_surjective K L hLK hUnramified⟩

/-- A prime class has exact additive order `[L : K]` in an unramified
norm quotient.  The lower bound is read after reduction in `ℤ̂/nℤ̂`; the
upper bound is the norm of the included prime. -/
theorem primeClass_addOrderOf
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (π : ambientFixedAddSubgroup A K.field) (hπ : v.IsPrimeElement K π) :
    addOrderOf
      (finiteNormClass A K.field L hLK π) =
      ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) := by
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let n := (E.degree : ℕ)
  have hUn : E.IsUnramified D := by
    change (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D
    exact hUnramified
  let g : FiniteNormQuotient A K.field L hLK :=
    finiteNormClass A K.field L hLK π
  have hn : 0 < n := E.degree.property
  have hng : n • g = 0 := by
    change n • finiteNormClass A K.field L hLK π = 0
    rw [← finiteNormClass_nsmul]
    apply (finiteNormClass_eq_zero_iff A K.field L hLK _).2
    refine ⟨fixedFieldInclusion A K.field L hLK π, ?_⟩
    have hnorm :=
      relativeNorm_fixedFieldInclusion A E.toFiniteAbstractExtension π
    change relativeNorm A K.field L hLK
        (fixedFieldInclusion A K.field L hLK π) = n • π at hnorm
    exact hnorm
  have hdiv : ∀ m : ℕ, m • g = 0 → n ∣ m := by
    intro m hm
    have hm' :
        finiteNormClass A K.field L hLK (m • π) = 0 := by
      simpa [g] using hm
    have hmNorm := (finiteNormClass_eq_zero_iff A K.field L hLK _).1 hm'
    obtain ⟨b, hb⟩ := hmNorm
    have htower := v.normalizedValuation_tower E b
    change (E.residueDegree D : ℕ) • _ = _ at htower
    rw [E.residueDegree_eq_degree_of_isUnramified D hUn] at htower
    have hval :
        n • ((v.valuationAt E.field b : v.valueGroup) : ZHat) =
          m • (1 : ZHat) := by
      calc
        n • ((v.valuationAt E.field b : v.valueGroup) : ZHat) =
            ((v.valuationAt K (relativeNorm A K.field L hLK b) :
              v.valueGroup) : ZHat) := htower
        _ = ((v.valuationAt K (m • π) : v.valueGroup) : ZHat) := by
          rw [hb]
        _ = m • ((v.valuationAt K π : v.valueGroup) : ZHat) := by
          exact congrArg Subtype.val (map_nsmul (v.valuationAt K) m π)
        _ = m • (1 : ZHat) := by rw [hπ, v.oneValue_coe]
    have hred := congrArg (fun z : ZHat => zHatReduction n hn z) hval
    have hredOne : zHatReduction n hn (1 : ZHat) = 1 := rfl
    have hred' :
        n • zHatReduction n hn
            ((v.valuationAt E.field b : v.valueGroup) : ZHat) =
          m • (1 : ZMod n) := by
      simpa only [map_nsmul, hredOne] using hred
    have hmzero : (m : ZMod n) = 0 := by
      have hmzero' : m • (1 : ZMod n) = 0 := by
        rw [← hred']
        simp [nsmul_eq_mul]
      simpa using hmzero'
    exact (ZMod.natCast_eq_zero_iff m n).1 hmzero
  apply Nat.dvd_antisymm
  · exact (addOrderOf_dvd_iff_nsmul_eq_zero).2 hng
  · exact hdiv (addOrderOf g) (addOrderOf_nsmul_eq_zero g)

/-- The prime class generates the full unramified norm quotient, as in the
last sentence of the proof of the unramified norm-quotient equivalence. -/
theorem primeClass_zmultiples_eq_top
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (π : ambientFixedAddSubgroup A K.field) (hπ : v.IsPrimeElement K π) :
    AddSubgroup.zmultiples
      (finiteNormClass A K.field L hLK π) = ⊤ := by
  let e := v.unramifiedReciprocity_valuationEquiv hAxiom K L hLK hUnramified
  let E := FiniteAbstractFieldExtension.ofInclusion L K hLK
  let : NeZero (E.degree : ℕ) :=
    ⟨E.degree.property.ne'⟩
  let : Finite (FiniteNormQuotient A K.field L hLK) :=
    Finite.of_equiv (ZMod (E.degree : ℕ)) (by
      simpa [E] using e.symm.toEquiv)
  apply AddSubgroup.eq_top_of_card_eq
  rw [Nat.card_zmultiples,
    v.primeClass_addOrderOf K L hLK hUnramified π hπ]
  exact ((Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)).symm

end ValuationData

end valuationQuotient

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_CanonicalUnramifiedNormQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction: the canonical unramified valuation quotient

the valuation-quotient axiom supplies the order of `Z / nZ`.  The construction then uses the
canonical reduction inherited from `Z ⊆ ℤ̂`, rather than an arbitrary
isomorphism with `ℤ / nℤ`.  This file constructs that canonical map and
proves directly that it induces the unramified norm-quotient isomorphism
used in the unramified norm-quotient equivalence.
-/

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- The canonical isomorphism `Z / nZ ≃ ℤ / nℤ` from the valuation-quotient axiom. -/
def canonicalValueQuotientEquiv
    (v : ValuationData D A) (n : ℕ) (hn : 0 < n) :
    (v.valueGroup ⧸ nsmulWithin v.valueGroup n) ≃+ ZMod n :=
  v.cyclic_value_quotients n hn

/-- The valuation map separates classes in the unramified norm quotient. -/
theorem canonicalUnramifiedNormQuotientValuation_injective
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (hUnramified : E.IsUnramified D) :
    Function.Injective
      (v.canonicalUnramifiedNormQuotientValuation E hUnramified) := by
  let := hnormal
  let n := (E.degree : ℕ)
  let hn : 0 < n := E.degree.property
  have hkernel : ∀ q : FiniteNormQuotient A E.base.field
      E.field.field E.below,
      v.canonicalUnramifiedNormQuotientValuation E hUnramified q = 0 →
        q = 0 := by
    intro q
    refine FiniteNormQuotient.induction_on A E.base.field E.field.field
      E.below q ?_
    intro a ha
    change v.canonicalValueReduction n hn (v.valuationAt E.base a) = 0 at ha
    have hqValue :
        (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)
          (v.valuationAt E.base a)) = 0 := by
      apply (v.canonicalValueQuotientEquiv n hn).injective
      change v.canonicalValueQuotientHom n hn
          (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n)
            (v.valuationAt E.base a)) =
        v.canonicalValueQuotientHom n hn 0
      rw [v.canonicalValueQuotientHom_mk, ha, map_zero]
    obtain ⟨z, haz⟩ :=
      (QuotientAddGroup.eq_zero_iff (v.valuationAt E.base a)).1 hqValue
    have haz' : v.valuationAt E.base a = n • z := haz.symm
    obtain ⟨b, hb⟩ := v.normalizedValuation_surjective E.field z
    let normb : ambientFixedAddSubgroup A E.base.field :=
      relativeNorm A E.base.field E.field.field E.below b
    have htower := v.normalizedValuation_tower E b
    have hresidueDegree :
        ((E.toFiniteResidueAbstractExtension D).residueDegree : ℕ) =
          (E.degree : ℕ) := by
      exact E.residueDegree_eq_degree_of_isUnramified D hUnramified
    dsimp only at htower
    rw [hresidueDegree] at htower
    have hnormb : v.valuationAt E.base normb = n • z := by
      apply Subtype.ext
      calc
        ((v.valuationAt E.base normb : v.valueGroup) : ZHat) =
            n • ((v.valuationAt E.field b : v.valueGroup) : ZHat) := htower.symm
        _ = n • ((z : v.valueGroup) : ZHat) := by rw [hb]
        _ = (((n • z : v.valueGroup)) : ZHat) := rfl
    let u : v.unitAddSubgroup E.base :=
      ⟨a - normb, by
        rw [v.mem_unitAddSubgroup_iff, map_sub, haz', hnormb, sub_self]⟩
    let KR := E.base.toFiniteResidueAbstractField D
    let hnormalKR :
        (extensionSubgroup KR.field E.field.field E.below).Normal := by
      change (extensionSubgroup E.base.field E.field.field E.below).Normal
      exact hnormal
    let hfiniteKR : Finite
        (KR.field.toSubgroup ⧸
          extensionSubgroup KR.field E.field.field E.below) := by
      change Finite (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below)
      exact E.finiteQuotient
    obtain ⟨g, hg⟩ :=
      D.exists_quotient_generator_of_unramified
        KR E.field.field E.below hUnramified
    let : Fintype (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below) :=
      Fintype.ofFinite _
    let Euc : FiniteUnramifiedCyclicExtension D E.base :=
      { field := E.field.field
        below := E.below
        normal := hnormal
        finite := E.finiteQuotient
        generator := g
        generates := hg
        unramified := by
          change E.IsUnramified D
          exact hUnramified }
    have hzero :
        CategoryTheory.Limits.IsZero
            (tateCohomology (Euc.unitRepresentation v) 0) ∧
          CategoryTheory.Limits.IsZero
            (tateCohomology (Euc.unitRepresentation v) (-1)) :=
      hAxiom E.base Euc
    obtain ⟨ε, hε⟩ :=
      v.exists_unit_relativeNorm_eq_of_tateHZero_isZero
        Euc.toFiniteAbstractFieldExtension Euc.normal
          Euc.toFiniteAbstractFieldExtension_isUnramified
          g hg hzero.1 u
    change v.unitAddSubgroup E.field at ε
    change relativeNorm A E.base.field E.field.field E.below ε.1 = u.1 at hε
    apply (finiteNormClass_eq_zero_iff A E.base.field E.field.field
      E.below a).2
    refine ⟨b + ε.1, ?_⟩
    rw [map_add, hε]
    change normb + (a - normb) = a
    abel
  intro x y hxy
  apply sub_eq_zero.mp
  apply hkernel
  rw [map_sub, hxy, sub_self]

end ValuationData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FrobeniusDescent
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# The abstract reciprocity construction: descent from the Frobenius semigroup

The two maps on `G(\widetilde L/K)`--restriction to `G(L/K)` and normalized
degree--are jointly injective.  This is the group-theoretic fact used when two Frobenius lifts have the same
restriction and degree.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Restriction and normalized degree jointly distinguish elements of
`G(\widetilde L/K)`. -/
theorem extensionRestriction_normalizedDegree_joint_injective
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    Function.Injective (fun q :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK =>
      (D.extensionRestriction K.field L hLK q,
        D.extensionNormalizedDegree K L hLK q)) := by
  intro q r hqr
  refine Quotient.inductionOn₂' q r ?_ hqr
  intro a b hab
  apply QuotientGroup.eq.mpr
  have hRestriction : QuotientGroup.mk a =
      (QuotientGroup.mk b :
        K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) := by
    exact congrArg Prod.fst hab
  have hExtension : a⁻¹ * b ∈ extensionSubgroup K.field L hLK :=
    QuotientGroup.eq.mp hRestriction
  have hDegree : D.normalizedDegree K a =
      D.normalizedDegree K b :=
    congrArg Prod.snd hab
  refine ⟨hExtension, ?_⟩
  rw [← D.normalizedDegree_ker K]
  change D.normalizedDegree K (a⁻¹ * b) = 1
  rw [map_mul, map_inv, hDegree, inv_mul_cancel]

/-- Frobenius elements with equal restriction and equal normalized degree
are equal. -/
theorem frobenius_eq_of_restriction_eq_of_degree_eq
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    {σ τ : D.FrobeniusElements K L hLK}
    (hRestriction :
      D.frobeniusRestriction K L hLK σ =
        D.frobeniusRestriction K L hLK τ)
    (hDegree :
      D.extensionNormalizedDegree K L hLK σ.1 =
        D.extensionNormalizedDegree K L hLK τ.1) :
    σ = τ := by
  apply Subtype.ext
  apply D.extensionRestriction_normalizedDegree_joint_injective
    K L hLK
  exact Prod.ext hRestriction hDegree

end DegreeData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainFiniteReciprocity
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.mem_normFilterBasis_iff _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.baseFixingExtensionQuotientEquivAmbient_mk _root_.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

open CategoryTheory
open scoped BigOperators


/-!
# The abstract reciprocity construction, the finite reciprocity equivalence

This file carries out the descent preparation.  The reciprocity
value on the Frobenius semigroup is first mapped to the finite norm quotient.
We then compare two lifts by their positive Frobenius exponents, construct
the degree-zero quotient between unequal lifts, and prove that this quotient
has zero finite reciprocity value.  Finally reciprocity multiplicativity supplies
additivity on the Frobenius semigroup, so the lift supplied by the finite degree-quotient decomposition descends to the additive reciprocity homomorphism of the finite reciprocity equivalence.
-/

noncomputable section

section finiteReciprocityValues

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The same formula for any prime element of the fixed field.  Prime-choice
independence is exactly the reciprocity construction's consequence of the unit-cohomology axiom. -/
theorem finiteReciprocityValue_eq_primeNormClass_of_isPrime
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let Sigma : FiniteAbstractField G :=
        { field := D.frobeniusFixedField
            (K.toFiniteResidueAbstractField D) L hLK σ
          finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
      v.IsPrimeElement Sigma π) :
    let KR := K.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    D.finiteReciprocityValue A v K L hLK σ =
      finiteNormClass A K.field L hLK
        (relativeNorm A K.field S hSK π) := by
  dsimp only
  rw [finiteReciprocityValue,
    ← D.reciprocityValueOfPrime_eq_reciprocityMap
      A v hAxiom K L hLK σ π hπ]
  exact D.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass
    A K.field L hLK _

end DegreeData

end finiteReciprocityValues

section equalFrobeniusLifts

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Equal restrictions and equal positive degrees give equal Frobenius
lifts.  This is the first case in the lift-independence proof. -/
theorem frobenius_eq_of_restriction_eq_of_exponent_eq (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    {σ τ : D.FrobeniusElements K L hLK}
    (hRestriction : D.frobeniusRestriction K L hLK σ =
      D.frobeniusRestriction K L hLK τ)
    (hExponent : D.frobeniusExponent K L hLK σ =
      D.frobeniusExponent K L hLK τ) :
    σ = τ := by
  apply D.frobenius_eq_of_restriction_eq_of_degree_eq
    K L hLK hRestriction
  rw [D.extensionNormalizedDegree_frobenius_eq_pow,
    D.extensionNormalizedDegree_frobenius_eq_pow, hExponent]

end DegreeData

end equalFrobeniusLifts

/-!
# The abstract reciprocity construction, the unramified norm-quotient equivalence

This file proves the generator calculation in the unramified case: the finite reciprocity equivalence sends arithmetic Frobenius to the prime
class.  That class generates the finite norm quotient, so the resulting
reciprocity homomorphism is promoted to an additive equivalence.
-/

noncomputable section

section unramifiedFixedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- For an unramified `L / K`, the fixed field of the degree-one
Frobenius lift is itself unramified over `K`. -/
theorem unramifiedFrobenius_fixedField_isUnramified
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    (DegreeData.AbstractExtension.mk
      (D.frobeniusFixedField K L hLK
        (D.chosenUnramifiedFrobeniusLift K L hLK)) K.field
      (D.frobeniusFixedField_le K L hLK
        (D.chosenUnramifiedFrobeniusLift K L hLK))).IsUnramified D := by
  let σ := D.chosenUnramifiedFrobeniusLift K L hLK
  let S := D.frobeniusFixedField K L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le K L hLK σ
  rw [(DegreeData.AbstractExtension.mk S K.field hSK).isUnramified_iff_inertia_le D]
  intro g hg
  have hgL : g ∈ L.toSubgroup :=
    ((DegreeData.AbstractExtension.mk L K.field hLK).isUnramified_iff_inertia_le D).1
      hUnramified hg
  exact D.fieldInertia_le_frobeniusFixedField K L hLK σ
    ⟨hgL, hg.2⟩

end DegreeData

end unramifiedFixedFields

section unramifiedReciprocity

/-! Mathlib's `Rep ℤ G` forces its representation-bearing group `G` to `Type 0`. -/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- The included prime element is a prime element in the fixed field used
for the degree-one Frobenius lift. -/
theorem unramifiedFrobenius_includedPrime_isPrime
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) :
    let KR := K.toFiniteResidueAbstractField D
    letI hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
      simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hnormal
    let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
      D.frobeniusFixedField_finite KR L hLK σ
    letI : Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) S (le_baseField S)) :=
      D.frobeniusFixedField_absoluteFinite K L hLK σ
    let Sigma : FiniteAbstractField G := ⟨S, inferInstance⟩
    v.IsPrimeElement Sigma
      (fixedFieldInclusion A K.field S hSK (v.chosenPrimeElement K)) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hnormal
  let σ := D.chosenUnramifiedFrobeniusLift KR L hLK
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let hSfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S hSK) :=
    D.frobeniusFixedField_finite KR L hLK σ
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let ES : FiniteAbstractFieldExtension G :=
    { field := Sigma
      base := K
      below := hSK
      finiteQuotient := hSfinite }
  have hES : ES.IsUnramified D := by
    have hunramified :=
      D.unramifiedFrobenius_fixedField_isUnramified KR L hLK hUnramified
    change ES.IsUnramified D at hunramified
    exact hunramified
  exact v.prime_of_unramified ES hES
    (v.chosenPrimeElement K) (v.chosenPrimeElement_isPrime K)

/-- The last generator-and-order argument in the unramified norm-quotient equivalence.  Any
homomorphism which sends the arithmetic Frobenius generator to the prime
class is bijective: the prime class generates the norm quotient, and both
finite groups have order `[L : K]`. -/
theorem unramifiedReciprocity_bijective_of_generator
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (f : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) →+
      FiniteNormQuotient A K.field L hLK)
    (hf : f (Additive.ofMul (D.unramifiedFrobenius
        (K.toFiniteResidueAbstractField D) L hLK)) =
      finiteNormClass A K.field L hLK (v.chosenPrimeElement K)) :
    Function.Bijective f := by
  let e := v.unramifiedReciprocity_valuationEquiv
    hAxiom K L hLK hUnramified
  let E : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion L K hLK
  let : NeZero (E.degree : ℕ) := ⟨E.degree.property.ne'⟩
  let : Finite (FiniteNormQuotient A K.field L hLK) :=
    Finite.of_equiv (ZMod (E.degree : ℕ)) e.symm
  have hsurj : Function.Surjective f := by
    rw [← AddMonoidHom.range_eq_top]
    apply top_unique
    rw [← v.primeClass_zmultiples_eq_top hAxiom K L hLK
      hUnramified (v.chosenPrimeElement K) (v.chosenPrimeElement_isPrime K)]
    rw [AddSubgroup.zmultiples_le]
    exact ⟨Additive.ofMul (D.unramifiedFrobenius
      (K.toFiniteResidueAbstractField D) L hLK), hf⟩
  apply (Nat.bijective_iff_surjective_and_card f).2
  refine ⟨hsurj, ?_⟩
  calc
    Nat.card (Additive
        (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)) =
        Nat.card
          (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) :=
      Nat.card_congr Additive.toMul
    _ = (extensionSubgroup K.field L hLK).index :=
      (Subgroup.index_eq_card _).symm
    _ = (E.degree : ℕ) := by
      exact E.toFiniteAbstractExtension.extensionSubgroup_index_eq_degree
    _ = Nat.card (ZMod (E.degree : ℕ)) :=
      (Nat.card_zmod _).symm
    _ = Nat.card (FiniteNormQuotient A K.field L hLK) :=
      (Nat.card_congr e.toEquiv).symm

/-- Additive-equivalence form of the generator criterion for the unramified norm-quotient equivalence.  This is useful independently of the particular construction of the
reciprocity homomorphism: a homomorphism with the required Frobenius value
is canonically promoted to an equivalence. -/
noncomputable def unramifiedReciprocity_equiv_of_generator
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (f : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) →+
      FiniteNormQuotient A K.field L hLK)
    (hf : f (Additive.ofMul (D.unramifiedFrobenius
        (K.toFiniteResidueAbstractField D) L hLK)) =
      finiteNormClass A K.field L hLK (v.chosenPrimeElement K)) :
    Additive (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) ≃+
      FiniteNormQuotient A K.field L hLK :=
  AddEquiv.ofBijective f
    (v.unramifiedReciprocity_bijective_of_generator hAxiom
      K L hLK hUnramified f hf)

/-- The generator-dependent unramified reciprocity equivalence has the expected
value on each class. -/
@[simp]
theorem unramifiedReciprocity_equiv_of_generator_apply
    (v : ValuationData D A) (hAxiom : SatisfiesUnramifiedUnitCohomology D v)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (f : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) →+
      FiniteNormQuotient A K.field L hLK)
    (hf : f (Additive.ofMul (D.unramifiedFrobenius
        (K.toFiniteResidueAbstractField D) L hLK)) =
      finiteNormClass A K.field L hLK (v.chosenPrimeElement K))
    (q : Additive
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)) :
    v.unramifiedReciprocity_equiv_of_generator hAxiom K L hLK
      hUnramified f hf q = f q :=
  rfl

end ValuationData
end unramifiedReciprocity
end
end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Permutation_Module
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Herbrand quotients of permutation lattices

This file supplies the abstract cohomology calculation for permutation
lattices.  It proves the value of the Herbrand quotient on the trivial
integer lattice, transports that calculation through Shapiro's lemma to
transitive permutation lattices, and multiplies over a finite family of
orbits.  It also records invariance under passage to a finite-index stable
subgroup.
-/

open scoped BigOperators

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA uι

section TrivialInteger

variable {G : Type uG} [Group G] [Fintype G]

/-- For the one-point orbit, the Herbrand quotient of the trivial
integer lattice is the order of the acting group. -/
theorem trivialInt_herbrandQuotient_eq_card
    (σ : G) :
    letI := trivialIntMulDistribMulAction G
    letI := trivialIntHerbrandH0Finite (G := G)
    letI :=
      trivialIntHerbrandHMinusOneFinite
        (G := G) σ
    herbrandQuotient
        (G := G) (A := Multiplicative ℤ) σ =
      (Fintype.card G : ℚ) := by
  let := trivialIntMulDistribMulAction G
  let := trivialIntHerbrandH0Finite (G := G)
  let :=
    trivialIntHerbrandHMinusOneFinite
      (G := G) σ
  rw [herbrandQuotient_eq_card_ratio,
    trivialInt_herbrandH0_card (G := G),
    trivialInt_herbrandHMinusOne_card_eq_one
      (G := G) σ]
  simp

end TrivialInteger

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_FieldNorm
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.ofWithZeroValuation_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Field norm on unit groups

This file connects mathlib's `Algebra.norm` with the unit-group and valued-norm
APIs used by local CFT.
-/

noncomputable section

universe u v w

namespace DiscreteValuationField

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/-- The quotient map `Kˣ → Kˣ / N_{L/K}(Lˣ)` attached to the field norm. -/
noncomputable def fieldNormQuotientMap :
    Kˣ →* Kˣ ⧸ fieldNormSubgroup K L :=
  QuotientGroup.mk' (fieldNormSubgroup K L)

/--
The defining evaluation formula for `fieldNormQuotientMap` is `fieldNormQuotientMap K L x =
QuotientGroup.mk' (fieldNormSubgroup K L) x`.
-/
@[simp] theorem fieldNormQuotientMap_apply (x : Kˣ) :
    fieldNormQuotientMap K L x =
      QuotientGroup.mk' (fieldNormSubgroup K L) x :=
  rfl

/-- Norm of an element coming from the base field. -/
@[simp] theorem fieldNormUnits_algebraMap (u : Kˣ) :
    normUnits K L (Units.map (algebraMap K L).toMonoidHom u) =
      u ^ Module.finrank K L := by
  ext
  simp [normUnits, Algebra.norm_algebraMap]

/-- Package a field norm as a `ValuedNorm` once the valuation formula has been
proved for the concrete extension.  The natural-number argument is not a
second source of extension-invariant data: `hformula` certifies it as the
valuation multiplier (and a source uniformizer makes that multiplier unique). -/
@[reducible] noncomputable def valuedFieldNorm
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    ValuedNorm vK vL where
  toHom := normUnits K L
  residueDegree := residueDegree
  valuation_formula := hformula

/--
Establishes the identity `(valuedFieldNorm K L vK vL residueDegree hformula).toHom =
normUnits K L`.
-/
@[simp] theorem valuedFieldNorm_toHom
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    (valuedFieldNorm K L vK vL residueDegree hformula).toHom =
      normUnits K L :=
  rfl

/-- Concrete compatibility condition saying that the field norm maps the
`n`-th source principal-unit subgroup into the requested target level. -/
abbrev fieldNormMapsFiltrationLevels
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) : Prop :=
  ∀ n {x : Lˣ}, x ∈ UL.principalUnitSubgroup n →
    normUnits K L x ∈ UK.principalUnitSubgroup (targetLevel n)

/-- The field norm restricted to a principal-unit filtration level. -/
def fieldNormMapLevelOfMapsFiltrationLevels
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ) :
    UL.principalUnitSubgroup n →*
      UK.principalUnitSubgroup (targetLevel n) where
  toFun x := ⟨normUnits K L x.1, hN n x.2⟩
  map_one' := by
    apply Subtype.ext
    exact (normUnits K L).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (normUnits K L).map_mul x.1 y.1

/--
The defining evaluation formula for `fieldNormMapLevelOfMapsFiltrationLevels` is
`(fieldNormMapLevelOfMapsFiltrationLevels K L UK UL targetLevel hN n x : Kˣ) = normUnits K L
x.1`.
-/
@[simp] theorem fieldNormMapLevelOfMapsFiltrationLevels_apply
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    (x : UL.principalUnitSubgroup n) :
    (fieldNormMapLevelOfMapsFiltrationLevels K L UK UL targetLevel hN n x :
        Kˣ) =
      normUnits K L x.1 :=
  rfl

/-- The field norm descended to quotients by compatible principal-unit
filtration levels. -/
def fieldNormFiltrationQuotientMap
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    Lˣ ⧸ UL.principalUnitSubgroup n →*
      Kˣ ⧸ UK.principalUnitSubgroup (targetLevel n) :=
  QuotientGroup.map (UL.principalUnitSubgroup n)
    (UK.principalUnitSubgroup (targetLevel n)) (normUnits K L) (by
      intro x hx
      exact hN n hx)

/--
The defining evaluation formula for `fieldNormFiltrationQuotientMap` is
`fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n (QuotientGroup.mk x) = QuotientGroup.mk
(normUnits K L x)`.
-/
@[simp] theorem fieldNormFiltrationQuotientMap_apply_mk
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] (x : Lˣ) :
    fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
        (QuotientGroup.mk x) =
      QuotientGroup.mk (normUnits K L x) :=
  rfl

/--
Establishes the identity `fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
(QuotientGroup.mk' (UL.principalUnitSubgroup n) x) = QuotientGroup.mk' (UK.principalUnitSubgroup
(targetLevel n)) (normUnits K L x)`.
-/
@[simp] theorem fieldNormFiltrationQuotientMap_apply_mk'
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] (x : Lˣ) :
    fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
        (QuotientGroup.mk' (UL.principalUnitSubgroup n) x) =
      QuotientGroup.mk' (UK.principalUnitSubgroup (targetLevel n))
        (normUnits K L x) :=
  rfl

/-- The preimage of a target principal-unit filtration subgroup under the
field norm. -/
def fieldNormFiltrationPreimageSubgroup
    (UK : AntitoneSubgroupFiltration Kˣ) (targetLevel : ℕ → ℕ) (n : ℕ) :
    Subgroup Lˣ :=
  (UK.principalUnitSubgroup (targetLevel n)).comap (normUnits K L)

/--
Characterizes `x ∈ fieldNormFiltrationPreimageSubgroup K L UK targetLevel n` by the equivalent
condition `normUnits K L x ∈ UK.principalUnitSubgroup (targetLevel n)`.
-/
@[simp] theorem mem_fieldNormFiltrationPreimageSubgroup_iff
    (UK : AntitoneSubgroupFiltration Kˣ) (targetLevel : ℕ → ℕ) (n : ℕ)
    (x : Lˣ) :
    x ∈ fieldNormFiltrationPreimageSubgroup K L UK targetLevel n ↔
      normUnits K L x ∈
        UK.principalUnitSubgroup (targetLevel n) :=
  Iff.rfl

end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_Valuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.ofWithZeroValuation_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

/-- The normalized integer valuation, packaged as the
`MultiplicativeIntegerValuation` used by the value-group layer. -/
def multiplicativeIntegerValuation
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    MultiplicativeIntegerValuation Kˣ where
  val x := LocalFieldTheory.IsNonarchimedeanLocalField.v K (Additive.ofMul x)
  map_one := by
    exact LocalFieldTheory.IsNonarchimedeanLocalField.v_one K
  map_mul x y := by
    exact LocalFieldTheory.IsNonarchimedeanLocalField.v_mul K x y

/-- The multiplicative integer valuation records the additive integer exponent of the original
valuation. -/
@[simp] theorem multiplicativeIntegerValuation_val
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) :
    (multiplicativeIntegerValuation K).val x =
      LocalFieldTheory.IsNonarchimedeanLocalField.v K (Additive.ofMul x) :=
  rfl

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_IdealQuotients
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-! ### Residue and maximal-ideal successive quotients -/

/-- The unit-quotient coordinate theorem in additive form:
`U^n/U^(n+1) ≃ 𝓀[K]`, for `n ≥ 1`. -/
def principalUnitsSuccQuotAddEquivResidue
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) (hn : 1 ≤ n) :
    Additive (PrincipalUnitsSuccQuot K n) ≃+ 𝓀[K] :=
  (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).symm.trans
    (chosenResidueAddEquivMaximalIdealPowSuccQuot K n).symm

/-- Successive principal-unit quotients over a local field are finite. -/
theorem finite_principalUnitsSuccQuot
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) (hn : 1 ≤ n) :
    Finite (PrincipalUnitsSuccQuot K n) :=
  Finite.of_equiv 𝓀[K]
    ((Additive.ofMul.trans (principalUnitsSuccQuotAddEquivResidue K n hn).toEquiv).symm)

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ValuationExactSequence
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceBaseValuativeRelIsNontrivial _root_.finiteLocalUnitsOpen
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

/-- The additive valuation map evaluates a field unit by applying the normalized integer valuation.
The additive valuation map evaluates a field unit by applying the normalized integer valuation. -/
@[simp]
theorem valuationMap_apply (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Additive Kˣ) :
    valuationMap K x = v K x :=
  rfl

/-- Coercing the field unit attached to a valuation-theoretic uniformizer
recovers the original field element. -/
@[simp]
theorem uniformizerFieldUnit_coe
    (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : 𝒪[K])
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K)) :
    (uniformizerFieldUnit K π hπ : K) = (π : K) :=
  rfl


/-- The additive valuation map sends the zero element of the additive unit group to zero. -/
@[simp]
theorem valuationMap_zero (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    valuationMap K (0 : Additive Kˣ) = 0 :=
  map_zero (valuationMap K)

/-- The multiplicative identity, viewed additively, has valuation zero. -/
@[simp]
theorem valuationMap_ofMul_one (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    valuationMap K (Additive.ofMul (1 : Kˣ)) = 0 := by
  change valuationMap K (0 : Additive Kˣ) = 0
  exact valuationMap_zero K

/-- A field unit with additive valuation zero has multiplicative valuation one. -/
theorem valuation_eq_one_of_valuationMap_eq_zero (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {x : Kˣ} (hx : valuationMap K (Additive.ofMul x) = 0) :
    ValuativeRel.valuation K (x : K) = 1 := by
  rw [valuationMap_apply] at hx
  dsimp [v] at hx
  have hunzero :
      WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K) (ValuativeRel.valuation K (x : K)))
        (by simp) = (1 : Multiplicative Int) := by
    have h := congrArg Multiplicative.ofAdd hx
    simpa using h
  apply (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
  have hcoe :
      ((WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K) (ValuativeRel.valuation K (x : K)))
        (by simp) : Multiplicative Int) : WithZero (Multiplicative Int)) =
        (1 : WithZero (Multiplicative Int)) := by
    simpa using congrArg
      (fun y : Multiplicative Int => (y : WithZero (Multiplicative Int))) hunzero
  rw [WithZero.coe_unzero] at hcoe
  simpa using hcoe

/-- The valuation of a quotient of field units is the difference of their valuations. -/
theorem valuationMap_ofMul_div (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    valuationMap K (Additive.ofMul (x / y)) =
      valuationMap K (Additive.ofMul x) - valuationMap K (Additive.ofMul y) := by
  change v K (Additive.ofMul (x / y)) = v K (Additive.ofMul x) - v K (Additive.ofMul y)
  exact v_div K x y

/-- The valuation of an integral power is the exponent times the original valuation. -/
theorem valuationMap_ofMul_zpow (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Int) :
    valuationMap K (Additive.ofMul (x ^ n)) =
      n * valuationMap K (Additive.ofMul x) := by
  change v K (Additive.ofMul (x ^ n)) = n * v K (Additive.ofMul x)
  exact v_zpow K x n

/-- The additive inclusion of valuation-ring units agrees with the underlying multiplicative
inclusion. -/
@[simp]
theorem additiveIntegerUnitsToFieldUnits_apply (K : Type u) [Field K] [ValuativeRel K]
    (u : 𝒪[K]ˣ) :
    additiveIntegerUnitsToFieldUnits K (Additive.ofMul u) =
      Additive.ofMul (integerUnitsToFieldUnits K u) :=
  rfl

/-- Defines `integerUnitOfValuationMapZero`. -/
def integerUnitOfValuationMapZero (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Kˣ) (hx : valuationMap K (Additive.ofMul x) = 0) : 𝒪[K]ˣ where
  val := ⟨(x : K), by
    rw [valuation_integer_membership]
    have hv := valuation_eq_one_of_valuationMap_eq_zero K hx
    simp [hv]⟩
  inv := ⟨(x⁻¹ : K), by
    rw [valuation_integer_membership]
    have hv := valuation_eq_one_of_valuationMap_eq_zero K hx
    simp [hv]⟩
  val_inv := by
    ext
    simp
  inv_val := by
    ext
    simp

/-- The valuation-ring unit reconstructed from a field unit of valuation zero maps back to that
field unit. -/
@[simp]
theorem integerUnitOfValuationMapZero_spec (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Kˣ) (hx : valuationMap K (Additive.ofMul x) = 0) :
    integerUnitsToFieldUnits K (integerUnitOfValuationMapZero K x hx) = x := by
  ext
  rfl

/-- The quotient of a field unit by the corresponding power of a uniformizer has
normalized valuation zero. -/
theorem uniformizerUnitFactorValuationZero (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ x : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    valuationMap K
      (Additive.ofMul (x / ϖ ^ valuationMap K (Additive.ofMul x))) = 0 := by
  rw [valuationMap_ofMul_div, valuationMap_ofMul_zpow, hϖ, mul_one, sub_self]

/-- The integer-unit factor in the standard decomposition `x = u * ϖ ^ v(x)`. -/
noncomputable def uniformizerUnitFactor (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (x : Kˣ) : 𝒪[K]ˣ :=
  integerUnitOfValuationMapZero K
    (x / ϖ ^ valuationMap K (Additive.ofMul x))
    (uniformizerUnitFactorValuationZero K ϖ x hϖ)

/-- Removing the uniformizer power prescribed by a field unit's valuation leaves a valuation-ring
unit. -/
@[simp]
theorem integerUnitsToFieldUnits_uniformizerUnitFactor (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ) :
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) =
      x / ϖ ^ valuationMap K (Additive.ofMul x) :=
  integerUnitOfValuationMapZero_spec K
    (x / ϖ ^ valuationMap K (Additive.ofMul x))
    (uniformizerUnitFactorValuationZero K ϖ x hϖ)

/-- Standard local-field unit/uniformizer decomposition in multiplicative form. -/
theorem uniformizerUnitFactor_mul_uniformizer_zpow (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ) :
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) *
        ϖ ^ valuationMap K (Additive.ofMul x) = x := by
  rw [integerUnitsToFieldUnits_uniformizerUnitFactor]
  simp [div_eq_mul_inv, mul_assoc]

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_TateH0_NormImage
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
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

/-- The additive subgroup of `Additive Kˣ` attached to the multiplicative norm subgroup. -/
def additiveNormSubgroup (K L : Type u) [Field K] [Field L] [Algebra K L] :
    AddSubgroup (Additive Kˣ) :=
  (localNormSubgroup K L).toAddSubgroup

/-- The invariant-unit equivalence maps the Tate norm submodule onto the additive norm subgroup. -/
lemma invariantsUnitsAddEquivBaseUnits_map_tateNormSubgroup (K L : Type)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    (letI := AlgEquiv.fintype K L
     (unitsTateH0NormSubmodule K L).toAddSubgroup.map
        (invariantsUnitsAddEquivBaseUnits K L).toAddMonoidHom) =
      additiveNormSubgroup K L := by
  let := AlgEquiv.fintype K L
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨z, rfl⟩
    change Additive.toMul
        (invariantsUnitsAddEquivBaseUnits K L
          (unitsNormToInvariantsLinearMap K L z)) ∈ localNormSubgroup K L
    let a : Lˣ := Additive.toMul z
    rw [show z = Additive.ofMul a by cases z; rfl]
    have hmap :=
      congrArg Additive.toMul
        (invariantsUnitsAddEquivBaseUnits_unitsNorm_apply K L a)
    rw [hmap]
    exact ⟨a, rfl⟩
  · intro hy
    change Additive.toMul y ∈ localNormSubgroup K L at hy
    rcases hy with ⟨x, hx⟩
    refine ⟨unitsNormToInvariantsLinearMap K L (Additive.ofMul x), ⟨Additive.ofMul x, rfl⟩, ?_⟩
    change
      invariantsUnitsAddEquivBaseUnits K L
          (unitsNormToInvariantsLinearMap K L (Additive.ofMul x)) = y
    calc
      invariantsUnitsAddEquivBaseUnits K L
          (unitsNormToInvariantsLinearMap K L (Additive.ofMul x))
          = Additive.ofMul (normUnits K L x) :=
            invariantsUnitsAddEquivBaseUnits_unitsNorm_apply K L x
      _ = Additive.ofMul (Additive.toMul y) := congrArg Additive.ofMul hx
      _ = y := by cases y; rfl

/-- The multiplicative invariant-unit equivalence maps Tate norms onto field norms. -/
lemma invariantsUnitsEquivBaseUnits_map_tateNormSubmodule (K L : Type)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    (letI := AlgEquiv.fintype K L
     (unitsTateH0NormSubmodule K L).map
        (invariantsUnitsEquivBaseUnits K L : unitsInvariantSubmodule K L →ₗ[ℤ] Additive Kˣ)) =
      (additiveNormSubgroup K L).toIntSubmodule := by
  let := AlgEquiv.fintype K L
  apply Submodule.toAddSubgroup_injective
  rw [Submodule.map_toAddSubgroup]
  exact invariantsUnitsAddEquivBaseUnits_map_tateNormSubgroup K L

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_PrincipalUnits_QuotientTower
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `CyclicCohomology.Herbrand.PrincipalUnits.QuotientTower` Lean module. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Every finite principal-unit quotient `𝒪_Kˣ/U_K^n` is finite over a
nonarchimedean local field. -/
theorem integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    Finite (IntegerUnitsModPrincipalUnitsAtLevel K n) := by
  induction n with
  | zero =>
      exact integerUnitsModPrincipalUnitsAtLevel_finite_zero K
  | succ n ih =>
      cases n with
      | zero =>
          exact integerUnitsModPrincipalUnitsAtLevel_finite_one_of_isNonarchimedeanLocalField K
      | succ k =>
          have : Finite (PrincipalUnitsSuccQuot K (k + 1)) :=
            finite_principalUnitsSuccQuot K (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
          exact integerUnitsModPrincipalUnitsAtLevel_finite_succ_of_finite K (k + 1)

/-- Actual finite-cyclic-module endpoint for the finite quotient
`𝒪_Lˣ/U_L^n`. -/
theorem integerUnitsModPrincipalUnitsAtLevel_herbrandQuotient_eq_one_of_isNonarchimedeanLocalField
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Fintype (Gal(L / K))] (n : Nat) (σ : Gal(L / K))
    (hgen : ∀ g : Gal(L / K), g ∈ Subgroup.zpowers σ) :
    letI := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
    letI : Finite (IntegerUnitsModPrincipalUnitsAtLevel L n) :=
      integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField L n
    CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient
      (G := Gal(L / K)) (A := IntegerUnitsModPrincipalUnitsAtLevel L n) σ = 1 := by
  let := galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n
  let : Finite (IntegerUnitsModPrincipalUnitsAtLevel L n) :=
    integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField L n
  exact CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient_finite_module_eq_one
    (G := Gal(L / K)) (A := IntegerUnitsModPrincipalUnitsAtLevel L n) σ hgen

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_SeparableNormValuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.mem_chosenBaseUniformizerPowSubmodule_iff _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open LocalFieldTheory

/-!
# Finite local reciprocity: normalized valuation of field norms

This file supplies the local-field calculation used when the abstract
class-formation framework is specialized to separable-closure units.  All
ramification and residue degrees below are the actual invariants of the
valuation-ring extension; no packaged norm-valuation hypothesis is assumed.
-/

noncomputable section

universe u v w

open scoped BigOperators ValuativeRel
open IsNonarchimedeanLocalField

attribute [local instance] FractionRing.liftAlgebra

/-- The norm of the chosen upstairs prime element has base normalized value
the negative of the actual residue degree, for every finite separable
extension (not only a Galois one). -/
theorem v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    v K (Additive.ofMul
        (normUnits K L (integerRingUniformizerFieldUnit L))) =
      -(Module.finrank 𝓀[K] 𝓀[L] : Int) := by
  let : Module.Finite 𝒪[K] 𝒪[L] :=
    IsIntegralClosure.finite 𝒪[K] K L 𝒪[L]
  let f : Nat := Module.finrank 𝓀[K] 𝓀[L]
  have hspan :
      Ideal.span
          ({Algebra.intNorm 𝒪[K] 𝒪[L]
            (chosenIntegerRingUniformizer L)} : Set 𝒪[K]) =
        Ideal.span ({chosenIntegerRingUniformizer K ^ f} : Set 𝒪[K]) := by
    calc
      Ideal.span
          ({Algebra.intNorm 𝒪[K] 𝒪[L]
            (chosenIntegerRingUniformizer L)} : Set 𝒪[K]) =
          Ideal.relNorm 𝒪[K]
            (Ideal.span ({chosenIntegerRingUniformizer L} : Set 𝒪[L])) := by
        exact (Ideal.spanNorm_singleton (R := 𝒪[K])
          (r := chosenIntegerRingUniformizer L)).symm
      _ = Ideal.relNorm 𝒪[K] (𝓂[L] : Ideal 𝒪[L]) := by
        rw [chosenIntegerRingUniformizer_maximalIdeal_eq L]
      _ = (𝓂[K] : Ideal 𝒪[K]) ^ f := by
        simpa [f] using relNorm_maximalIdeal_eq_pow_residue_finrank K L
      _ = Ideal.span ({chosenIntegerRingUniformizer K ^ f} : Set 𝒪[K]) :=
        maximalIdeal_pow_eq_span_uniformizer_pow K f
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hfieldUnits :
      normUnits K L (integerRingUniformizerFieldUnit L) *
        integerUnitsToFieldUnits K u =
      integerRingUniformizerFieldUnit K ^ f := by
    apply Units.ext
    have huField := congrArg (algebraMap 𝒪[K] K) hu
    rw [map_mul, Algebra.algebraMap_intNorm (K := K) (L := L)] at huField
    change
      Algebra.norm K (algebraMap 𝒪[L] L (chosenIntegerRingUniformizer L)) *
          algebraMap 𝒪[K] K (u : 𝒪[K]) =
        algebraMap 𝒪[K] K (chosenIntegerRingUniformizer K) ^ f
    exact huField
  have hvalue := congrArg
    (fun z : Kˣ => v K (Additive.ofMul z)) hfieldUnits
  change v K (Additive.ofMul
      (normUnits K L (integerRingUniformizerFieldUnit L) *
        integerUnitsToFieldUnits K u)) =
    v K (Additive.ofMul (integerRingUniformizerFieldUnit K ^ f)) at hvalue
  rw [v_mul, v_integerUnitsToFieldUnits, add_zero, v_pow,
    v_integerRingUniformizerFieldUnit] at hvalue
  simpa [f] using hvalue

/-- The norm of the positive generator (the inverse chosen prime element) has
base normalized value equal to the actual residue degree. -/
theorem v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    v K (Additive.ofMul
        (normUnits K L (inverseIntegerRingUniformizerFieldUnit L))) =
      (Module.finrank 𝓀[K] 𝓀[L] : Int) := by
  rw [inverseIntegerRingUniformizerFieldUnit, map_inv, v_inv,
    v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable]
  simp only [neg_neg]

/-- Finite local reciprocity, normalized norm calculation for every finite separable
local-field extension: the normalized value of a field norm is the actual
residue degree times the upstairs normalized value. -/
theorem v_normUnits_eq_residue_finrank_mul_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (x : Lˣ) :
    v K (Additive.ofMul (normUnits K L x)) =
      (Module.finrank 𝓀[K] 𝓀[L] : Int) *
        v L (Additive.ofMul x) := by
  let ϖ : Lˣ := inverseIntegerRingUniformizerFieldUnit L
  have hϖ : v L (Additive.ofMul ϖ) = 1 :=
    v_inverseIntegerRingUniformizerFieldUnit L
  let n : Int := v L (Additive.ofMul x)
  let a : 𝒪[L]ˣ := uniformizerUnitFactor L ϖ hϖ x
  have haNorm :
      normUnits K L (integerUnitsToFieldUnits L a) =
        integerUnitsToFieldUnits K (normIntegerUnits K L a) := by
    apply Units.ext
    rfl
  have hx : integerUnitsToFieldUnits L a * ϖ ^ n = x := by
    exact uniformizerUnitFactor_mul_uniformizer_zpow L ϖ hϖ x
  have hxNorm :
      normUnits K L x =
        integerUnitsToFieldUnits K (normIntegerUnits K L a) *
          (normUnits K L ϖ) ^ n := by
    calc
      normUnits K L x =
          normUnits K L (integerUnitsToFieldUnits L a * ϖ ^ n) :=
        congrArg (normUnits K L) hx.symm
      _ = normUnits K L (integerUnitsToFieldUnits L a) *
          (normUnits K L ϖ) ^ n := by
        simp only [map_mul, map_zpow]
      _ = integerUnitsToFieldUnits K (normIntegerUnits K L a) *
          (normUnits K L ϖ) ^ n := by rw [haNorm]
  rw [hxNorm, v_mul, v_integerUnitsToFieldUnits, zero_add, v_zpow,
    v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable]
  simp only [n]
  ring

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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

/-- One nonzero element controlling both the initial basis scaling and
the finite index of the resulting lattice. -/
noncomputable def integralTensorControlElement :
    𝓞 K :=
  relativeBasisIntegralScaleInRingOfIntegers
      (K := K) (L := L) *
    scaledRelativeIntegerLatticeAnnihilator
      (K := K) (L := L)

/-- The nonzero principal ideal defining the bad primes. -/
noncomputable def integralTensorControlIdeal :
    Ideal (𝓞 K) :=
  Ideal.span
    ({integralTensorControlElement
      (K := K) (L := L)} : Set (𝓞 K))
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_IntegerRingComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

open AlgebraicNumberTheory.Valuations
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- Embed global integers into the valuation ring of their finite-place
completion. -/
noncomputable def finitePlaceIntegerToCompletion
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 K) →+* 𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] :=
  RingHom.codRestrict
    ((algebraMap K (ChosenFinitePlaceBaseCompletion (K := K) v)).comp
      (algebraMap (𝓞 K) K))
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] (by
      intro x
      rw [finitePlaceCompletion_mem_integers_iff_norm_le_one]
      change ‖((WithAbs.toAbs (HeightOneSpectrum.adicAbv K v) (x : K) :
        WithAbs (HeightOneSpectrum.adicAbv K v)) :
          ChosenFinitePlaceBaseCompletion (K := K) v)‖ ≤ 1
      rw [UniformSpace.Completion.norm_coe, WithAbs.norm_toAbs_eq]
      rw [HeightOneSpectrum.adicAbv_def]
      apply (WithZeroMulInt.toNNReal_le_one_iff
        (HeightOneSpectrum.one_lt_absNorm_nnreal v)).2
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact v.intValuation_le_one x)

@[simp]
theorem finitePlaceIntegerToCompletion_coe
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    ((finitePlaceIntegerToCompletion v x :
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]) :
        ChosenFinitePlaceBaseCompletion (K := K) v) =
      algebraMap K (ChosenFinitePlaceBaseCompletion (K := K) v) (x : K) :=
  rfl

/-- The comparison with the adic model takes a global element to its
standard finite-place embedding. -/
@[simp]
theorem finitePlaceCompletionRingEquiv_toCompletion
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    finitePlaceCompletionRingEquiv v
        (algebraMap K (ChosenFinitePlaceBaseCompletion (K := K) v) x) =
      FinitePlace.embedding v x := by
  change finitePlaceCompletionRingHom v
    ((WithAbs.toAbs (HeightOneSpectrum.adicAbv K v) x :
      WithAbs (HeightOneSpectrum.adicAbv K v)) :
        ChosenFinitePlaceBaseCompletion (K := K) v) = _
  rw [finitePlaceCompletionRingHom_coe,
    finitePlaceCompletionBaseMap_apply]
  rfl

/-- The residue field at a finite prime is canonically the residue field of
its normalized absolute-value completion. -/
noncomputable def finitePlaceIdealResidueEquivCompletion
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 K ⧸ v.asIdeal) ≃+*
      𝓀[ChosenFinitePlaceBaseCompletion (K := K) v] := by
  let a := HeightOneSpectrum.adicAbv K v
  let ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat a).1
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v)
  let aC := AbsoluteValue.completionAbsoluteValue a
  let haC : LubinTate.Valuations.NonarchimedeanAbsoluteValue aC :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat aC).1
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean a
        (HeightOneSpectrum.isNonarchimedean_adicAbv K v))
  let eBase :
      (v.valuationSubringAtPrime K) ≃+*
        LubinTate.Valuations.exponentialValuationSubring
          (absoluteValueExponentialValuation a ha) :=
    RingEquiv.restrict (RingEquiv.refl K)
      (v.valuationSubringAtPrime K)
      (LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation a ha)) (by
          intro x
          rw [v.valuationSubringAtPrime_eq_valuationSubring]
          change (v.valuation K) x ≤ 1 ↔
            x ∈ LubinTate.Valuations.exponentialValuationSubring
              (absoluteValueExponentialValuation a ha)
          rw [mem_absoluteValueExponentialSubring_iff]
          rw [HeightOneSpectrum.adicAbv_def]
          exact (WithZeroMulInt.toNNReal_le_one_iff
            (HeightOneSpectrum.one_lt_absNorm_nnreal v)).symm)
  let eCompletion :
      LubinTate.Valuations.exponentialValuationSubring
          (absoluteValueExponentialValuation aC haC) ≃+*
        𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] :=
    RingEquiv.restrict (RingEquiv.refl a.Completion)
      (LubinTate.Valuations.exponentialValuationSubring
        (absoluteValueExponentialValuation aC haC))
      𝒪[ChosenFinitePlaceBaseCompletion (K := K) v] (by
        intro x
        rw [mem_absoluteValueExponentialSubring_iff]
        rw [finitePlaceCompletion_mem_integers_iff_norm_le_one]
        rfl)
  exact (finitePlaceIdealResidueEquivLocalization v).trans
    ((IsLocalRing.ResidueField.mapEquiv eBase).trans
      ((completionResidueEquiv a ha).trans
        (IsLocalRing.ResidueField.mapEquiv eCompletion)))

@[simp]
theorem finitePlaceIdealResidueEquivCompletion_apply_mk
    {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    finitePlaceIdealResidueEquivCompletion v
        (Ideal.Quotient.mk v.asIdeal x) =
      IsLocalRing.residue
        𝒪[ChosenFinitePlaceBaseCompletion (K := K) v]
        (finitePlaceIntegerToCompletion v x) := by
  unfold finitePlaceIdealResidueEquivCompletion
    finitePlaceIdealResidueEquivLocalization
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_UnramifiedComparison_IdealToCompletion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# From ideal-theoretic to completed unramifiedness

This file proves that ideal-theoretic unramifiedness at the centre of the
actual chosen finite-place extension implies unramifiedness of its localized
completion.
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

/-- A uniformizer of a finite-place completion induced by an element of the
global integer ring, together with its valuation and comparison properties. -/
structure FinitePlaceCompletionIntegralUniformizer
    {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) where
  /-- The inducing element of the global integer ring. -/
  integer : 𝓞 F
  /-- The corresponding element of the completion integer ring. -/
  completionInteger :
    𝒪[ChosenFinitePlaceBaseCompletion (K := F) v]
  /-- The inducing global integer has normalized valuation `-1`. -/
  intValuation_eq_exp_neg_one :
    v.intValuation integer = WithZero.exp (-1 : ℤ)
  /-- The completion element is the image of the global integer. -/
  coe_completionInteger :
    (completionInteger :
        ChosenFinitePlaceBaseCompletion (K := F) v) =
      algebraMap F
        (ChosenFinitePlaceBaseCompletion (K := F) v)
        (integer : F)
  /-- The completion element is a uniformizer for the intrinsic valuation. -/
  completionInteger_isUniformizer :
    (ValuativeRel.valuation
        (ChosenFinitePlaceBaseCompletion (K := F) v)).IsUniformizer
      (completionInteger :
        ChosenFinitePlaceBaseCompletion (K := F) v)
  /-- The completion element lies in the completion's maximal ideal. -/
  completionInteger_mem_maximalIdeal :
    completionInteger ∈
      (𝓂[ChosenFinitePlaceBaseCompletion (K := F) v] :
        Ideal
          𝒪[ChosenFinitePlaceBaseCompletion (K := F) v])
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_NormLocalOrder
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.chosenFinitePlaceBaseValuationCompatible
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

/-- A surjective standard integer valuation gives the same normalized
integer value as the intrinsic local-field valuation. -/
theorem normalizedValue_eq_withZeroLog_of_surjective
    (F : Type w)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (ν : Valuation F (WithZero (Multiplicative ℤ)))
    [ν.Compatible]
    (hν : Function.Surjective ν)
    (x : Fˣ) :
    LocalFieldTheory.IsNonarchimedeanLocalField.v F
        (Additive.ofMul x) =
      WithZero.log (ν (x : F)) := by
  let ν₀ := ValuativeRel.valuation F
  have hEquiv : ν₀.IsEquiv ν :=
    ValuativeRel.isEquiv ν₀ ν
  obtain ⟨π, hπ⟩ :=
    hν (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  let ϖ : Fˣ := Units.mk0 π hπ0
  have hπlt : ν π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hπIntrinsicLt : ν₀ π < 1 :=
    hEquiv.lt_one_iff_lt_one.mpr hπlt
  have hπIntrinsicMax :
      ∀ γ : ValuativeRel.ValueGroupWithZero F,
        γ < 1 → γ ≤ ν₀ π := by
    intro γ hγ
    obtain ⟨y, hy⟩ :=
      ValuativeRel.valuation_surjective γ
    have hylt : ν y < 1 := by
      apply hEquiv.lt_one_iff_lt_one.mp
      simpa [ν₀, hy]
    have hyle : ν y ≤ ν π := by
      rw [hπ]
      exact
        withZeroMultiplicativeInt_le_exp_neg_one_of_lt_one
          (ν y) hylt
    have hyle' : ν₀ y ≤ ν₀ π :=
      hEquiv.le_iff_le.mpr hyle
    simpa [ν₀, hy] using hyle'
  let φ :=
    _root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hφπ :
      φ (ν₀ π) = WithZero.exp (-1 : ℤ) := by
    apply le_antisymm
    · exact
        withZeroMultiplicativeInt_le_exp_neg_one_of_lt_one
          (φ (ν₀ π)) (by
            have h := φ.strictMono hπIntrinsicLt
            simpa [φ] using h)
    · let γ : ValuativeRel.ValueGroupWithZero F :=
        φ.symm (WithZero.exp (-1 : ℤ))
      have hγlt : γ < 1 := by
        have hneg :
            WithZero.exp (-1 : ℤ) <
              (1 : WithZero (Multiplicative ℤ)) := by
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
          omega
        have h := φ.symm.strictMono hneg
        simpa [γ, φ] using h
      have hγle := hπIntrinsicMax γ hγlt
      have hmap := φ.toOrderIso.monotone hγle
      rw [← φ.apply_symm_apply (WithZero.exp (-1 : ℤ))]
      exact hmap
  have hϖValue :
      LocalFieldTheory.IsNonarchimedeanLocalField.v F
          (Additive.ofMul ϖ) = -1 := by
    rw [LocalFieldTheory.IsNonarchimedeanLocalField.v_apply]
    apply (WithZero.toAdd_unzero_eq_iff _ (-1 : ℤ)).2
    change
      φ (ν₀ ((ϖ : Fˣ) : F)) =
        ((Multiplicative.ofAdd (-1 : ℤ) :
            Multiplicative ℤ) :
          WithZero (Multiplicative ℤ))
    change
      φ (ν₀ π) =
        ((Multiplicative.ofAdd (-1 : ℤ) :
            Multiplicative ℤ) :
          WithZero (Multiplicative ℤ))
    simpa only [WithZero.exp_eq_coe_ofAdd] using hφπ
  let n : ℤ := WithZero.log (ν (x : F))
  let y : Fˣ := x * ϖ ^ n
  have hxν0 : ν (x : F) ≠ 0 :=
    (Valuation.ne_zero_iff ν).2 x.ne_zero
  have hyν : ν (y : F) = 1 := by
    have hϖν : ν (ϖ : F) = WithZero.exp (-1 : ℤ) := by
      simpa [ϖ] using hπ
    calc
      ν (y : F) =
          ν (x : F) * ν (ϖ : F) ^ n := by
            simp [y]
      _ =
          WithZero.exp n * WithZero.exp (-1 : ℤ) ^ n := by
            rw [← WithZero.exp_log hxν0]
            rw [hϖν]
      _ =
          WithZero.exp n *
            WithZero.exp (n • (-1 : ℤ)) := by
              rw [WithZero.exp_zsmul]
      _ = WithZero.exp (n + n • (-1 : ℤ)) := by
            rw [WithZero.exp_add]
      _ = 1 := by
            simp
  have hyInvν : ν ((y⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hyν, inv_one]
  have hyMem : (y : F) ∈ 𝒪[F] := by
    change ν₀ (y : F) ≤ 1
    exact hEquiv.le_one_iff_le_one.mpr (by rw [hyν])
  have hyInvMem : ((y⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
    change ν₀ ((y⁻¹ : Fˣ) : F) ≤ 1
    exact hEquiv.le_one_iff_le_one.mpr (by rw [hyInvν])
  let yInteger : 𝒪[F]ˣ :=
    { val := ⟨(y : F), hyMem⟩
      inv := ⟨((y⁻¹ : Fˣ) : F), hyInvMem⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  have hyField :
      LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
          F yInteger =
        y := by
    apply Units.ext
    rfl
  have hyValue :
      LocalFieldTheory.IsNonarchimedeanLocalField.v F
          (Additive.ofMul y) = 0 := by
    rw [← hyField]
    exact
      LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits
        F yInteger
  have hdecomp : y * ϖ ^ (-n) = x := by
    rw [show y = x * ϖ ^ n by rfl, mul_assoc, zpow_neg,
      mul_inv_cancel, mul_one]
  have hdecompValue :=
    congrArg
      (fun z : Fˣ =>
        LocalFieldTheory.IsNonarchimedeanLocalField.v F
          (Additive.ofMul z))
      hdecomp
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.v_mul,
    hyValue,
    LocalFieldTheory.IsNonarchimedeanLocalField.v_zpow,
    hϖValue] at hdecompValue
  dsimp [n] at hdecompValue ⊢
  linarith

end FiniteIdeleGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Ramification_Splitting_NormalClosure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Complete splitting and normal closures

This file formalizes the normal-closure reduction for complete splitting.
For a finite Galois extension `M / K`, an intermediate field `L`, a
nontrivial absolute value `v` of `K`, and an extension `w` to `M`, put

* `G = Gal(M / K)`,
* `H = Gal(M / L)`, and
* `D = D(w / v)`.

Restriction of the conjugates of `w` gives an equivalence

`H \ G / D ≃ { extensions of v to L }`.

Thus the intrinsic complete-splitting condition for the possibly
non-Galois extension `L / K` is exactly the equality between the number
of double cosets and the number of left cosets.  If `M` is generated by
the `K`-conjugates of `L`, then `H` has trivial normal core.
`SplittingGroupTheory` consequently forces `D = 1`, so the place splits
completely already in `M`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification

section CompleteSplitting

variable {K E : Type}
    [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E]

variable [NumberField K]

/-- Intrinsic complete splitting of a finite place in a possibly
non-Galois finite extension. -/
def FinitePlaceSplitsCompletelyInExtension
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  AbsoluteValueSplitsCompletelyInExtension
    (E := E)
    (NumberField.HeightOneSpectrum.adicAbv K v)

end CompleteSplitting
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_BinaryProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Low-degree Tate cohomology of binary products

This specializes the dependent-product calculation to two possibly
different coefficient groups.  It is used to join the unrestricted and
integral parts of a supported idele group.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA

variable {G : Type uG} [Group G] [Fintype G]
variable (A B : Type uA)
variable [CommGroup A] [CommGroup B]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]

/-- Degree-minus-one Tate cohomology commutes with a binary product. -/
noncomputable def herbrandHMinusOneProdEquiv
    (σ : G) :
    HerbrandHMinusOne G (A × B) σ ≃*
      HerbrandHMinusOne G A σ ×
        HerbrandHMinusOne G B σ := by
  letI familyAction : ∀ i, MulDistribMulAction G
      (BinaryCoefficientFamily A B i) :=
    binaryCoefficientFamilyAction A B
  letI piAction : MulDistribMulAction G
      (∀ i, BinaryCoefficientFamily A B i) :=
    piMulDistribMulAction G
      (BinaryCoefficientFamily A B)
  exact
    (herbrandHMinusOneEquivariantMulEquiv
      (prodEquivBinaryCoefficientFamily A B)
      (prodEquivBinaryCoefficientFamily_smul A B) σ).trans
      ((herbrandHMinusOnePiEquiv
        (G := G) (BinaryCoefficientFamily A B) σ).trans
        (piHerbrandHMinusOneEquivProd A B σ))

/-- Finiteness of degree minus one is preserved by a binary product. -/
theorem herbrandHMinusOneProdFinite
    (σ : G)
    [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandHMinusOne G B σ)] :
    Finite (HerbrandHMinusOne G (A × B) σ) :=
  Finite.of_equiv
    (HerbrandHMinusOne G A σ ×
      HerbrandHMinusOne G B σ)
    (herbrandHMinusOneProdEquiv A B σ).symm.toEquiv

/-- Cardinality of degree-minus-one Tate cohomology for a binary
product. -/
theorem herbrandHMinusOneProd_card
    (σ : G)
    [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandHMinusOne G B σ)] :
    letI : Finite (HerbrandHMinusOne G (A × B) σ) :=
      herbrandHMinusOneProdFinite A B σ
    Nat.card (HerbrandHMinusOne G (A × B) σ) =
      Nat.card (HerbrandHMinusOne G A σ) *
        Nat.card (HerbrandHMinusOne G B σ) := by
  rw [Nat.card_congr
      (herbrandHMinusOneProdEquiv A B σ).toEquiv,
    Nat.card_prod]

/-- The Herbrand quotient of a binary product is the product of the
two Herbrand quotients. -/
theorem herbrandQuotient_prod
    (σ : G)
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)]
    [Finite (HerbrandHMinusOne G B σ)] :
    letI : Finite (HerbrandH0 G (A × B)) :=
      herbrandH0ProdFinite A B
    letI : Finite (HerbrandHMinusOne G (A × B) σ) :=
      herbrandHMinusOneProdFinite A B σ
    herbrandQuotient (G := G) (A := A × B) σ =
      herbrandQuotient (G := G) (A := A) σ *
        herbrandQuotient (G := G) (A := B) σ := by
  let : Finite (HerbrandH0 G (A × B)) :=
    herbrandH0ProdFinite A B
  let : Finite (HerbrandHMinusOne G (A × B) σ) :=
    herbrandHMinusOneProdFinite A B σ
  rw [herbrandQuotient_eq_card_ratio,
    herbrandQuotient_eq_card_ratio,
    herbrandQuotient_eq_card_ratio,
    herbrandH0Prod_card A B,
    herbrandHMinusOneProd_card A B σ]
  simp only [Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

end CyclicCohomology
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

abbrev B_p2 (K : Type) [Field K] : ClosedSubgroup (G_p3 K) :=
  intrinsicAbstractBase K

end LocalClassFieldTheory
end
end


