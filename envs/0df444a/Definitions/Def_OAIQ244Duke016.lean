-- Prove2me | Definitions.Def_OAIQ244Duke016
-- name    : OAIQ244Duke016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:17:50.224376+00:00
-- url     : https://prove2.me/theorems/0ed4d3ff-1273-471c-8c3d-97237ba4e4af
-- title:
--   Definitions bundle OAIQ244Duke016 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 243 declarations of OpenAI's Lean: 73 definitions, 1 inductive type or structure, 13 instances and 156 theorems. The definitions and types are `ClassFormation.FiniteAbelianSubextension`, `ClassFormation.FiniteAbelianSubextension.baseChange`, `ClassFormation.FiniteAbelianSubextension.below`, `ClassFormation.FiniteAbelianSubextension.extensionQuotient`, `ClassFormation.FiniteAbelianSubextension.extensionQuotientMk`, `ClassFormation.FiniteAbelianSubextension.extensionQuotientMulEquiv`, `ClassFormation.FiniteAbelianSubextension.field`, `ClassFormation.FiniteAbelianSubextension.finite`, `ClassFormation.FiniteAbelianSubextension.normSubgroup`, `ClassFormation.FiniteAbelianSubextension.normal`, `ClassFormation.FiniteCyclicSubextension.IsTotallyRamified`, `ClassFormation.FiniteGaloisSubextension.baseChange`, `ClassFormation.FiniteGaloisSubextension.classFieldCandidate`, `ClassFormation.FiniteGaloisSubextension.compositum`, `ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe`, `ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbstractExtension`, `ClassFormation.FiniteGaloisSubextension.normQuotientSubgroup`, `ClassFormation.FiniteGaloisSubextension.normSubgroup`, `ClassFormation.FiniteGaloisSubextension.reciprocityAbelianizedClassHom`, `ClassFormation.FiniteGaloisSubextension.reciprocityAbelianizedSubgroup`, `ClassFormation.FiniteGaloisSubextension.reciprocityPreimageSubgroup`, `ClassFormation.FiniteGaloisSubextension.toFiniteAbstractFieldExtension`, `ClassFormation.IsNormOpen`, `ClassFormation.cyclicConcreteEquivTateHZero`, `ClassFormation.cyclicFiniteNormQuotientEquivConcrete`, `ClassFormation.cyclicFiniteNormQuotientEquivTateHZero`, `ClassFormation.cyclicFixedCycleEquiv`, `ClassFormation.cyclicNormClassHom`, `ClassFormation.normFilterBasis`, `ClassFormation.normTopology`, `ClassFormation.padicCyclicClosure`, `ClassFormation.padicCyclicClosureGenerator`, `ClassFormation.zHatContinuousAddEquivPrimeProduct`, `ClassFormation.zHatContinuousMulEquivPrimeProduct`, `ClassFormation.zHatPadicReduction`, `ClassFormation.zHatReductionRingHom`, `ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct`, `ClassFormation.zHatToPadicInt`, `ClassFormation.zHatToProfiniteIntegerPrimeProduct`, `ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct` and 34 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AbstractClassFieldTheory_Degree_FrobeniusFixedField`, `AbstractClassFieldTheory_Degree_Indices`, `AbstractClassFieldTheory_Degree_PadicCyclicClosure`, `AbstractClassFieldTheory_Degree_Valuation`, `AbstractClassFieldTheory_Reciprocity_ClassFieldAxiom`, `AbstractClassFieldTheory_Reciprocity_ClassFieldCandidate`, `AbstractClassFieldTheory_Reciprocity_Construction_FiniteNormQuotient`, `AbstractClassFieldTheory_Reciprocity_Construction_UnitCohomologyAxiom`, `AbstractClassFieldTheory_Reciprocity_CyclicNormQuotient`, `AbstractClassFieldTheory_Reciprocity_FieldRepresentation`, `AbstractClassFieldTheory_Reciprocity_FiniteAbelianSubextension`, `AbstractClassFieldTheory_Reciprocity_FiniteGaloisSubextension`, `AbstractClassFieldTheory_Reciprocity_IntermediateExtension`, `AbstractClassFieldTheory_Reciprocity_NormTopology`, `AlgebraicNumberTheory_Completion_ChosenLocalization`, `Cyclic_Herbrand_HerbrandFiniteness`, `Cyclic_Herbrand_HerbrandLowDegree_Basic`, `Cyclic_Herbrand_HerbrandLowDegree_Cardinality`, `Cyclic_Herbrand_HerbrandLowDegree_Core`, `Cyclic_Herbrand_HerbrandLowDegree_EquivariantEquiv`, `Cyclic_Herbrand_HerbrandLowDegree_TateComparison`, `Cyclic_Herbrand_NormalBasisLattice`, `Cyclic_Herbrand_Permutation_Module`, `Cyclic_Herbrand_PrincipalUnits_QuotientReps`, `Cyclic_TateH0_NormImage`, `LocalField_DiscreteValuationField_FieldNorm`, `ProfiniteIntegers_CyclotomicTorsionQuotient`, `ProfiniteIntegers_ProfiniteIntegerCore`, `ProfiniteIntegers_ProfiniteIntegerPrimeProduct`, `ProfiniteIntegers_ProfiniteIntegerUnits`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke002`, `OAIQ244Duke003`, `OAIQ244Duke004` and `OAIQ244Duke005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke026`, `OAIQ244Duke027`, `OAIQ244Duke028`, `OAIQ244Duke030`, `OAIQ244Duke031`, `OAIQ244Duke033` and `OAIQ244Duke034`.
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
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
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
import Mathlib.Data.ZMod.QuotientRing
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
import Mathlib.GroupTheory.Torsion
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
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Quotient.Pi
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
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
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
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Pointwise
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
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.WithTopology
import Definitions.Def_OAIQ244Duke002
import Definitions.Def_OAIQ244Duke003
import Definitions.Def_OAIQ244Duke004
import Definitions.Def_OAIQ244Duke005

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_Indices
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

/-!
# Relative indices

This file isolates the group-theoretic index calculation used in abstract valuation theory.
For a homomorphism `d`, an inclusion `L ≤ K` splits its relative index into the index of
the images under `d` and the relative index inside `ker d`.
-/

open scoped Pointwise

universe u v

variable {G : Type u} {D : Type v} [Group G] [Group D]

/-! ## Cardinal-valued relative indices

The natural-valued `Subgroup.relIndex` is useful only after finiteness is
known: it represents every infinite index by zero.  The following API keeps
the actual coset cardinality and is therefore the source for general tower
and image--kernel laws.  Chosen representatives occur only in private
equivalences used to prove these canonical equalities. -/

/-- At an explicitly finite boundary, the cardinal relative index specializes
to Mathlib's natural-valued relative index. -/
theorem relativeIndexCardinal_eq_index_of_finite {L K : Subgroup G} (hLK : L ≤ K)
    [Finite (K ⧸ L.subgroupOf K)] :
    relativeIndexCardinal hLK = (L.relIndex K : Cardinal) := by
  rw [relativeIndexCardinal, intersectionIndexCardinal, Subgroup.relIndex, Subgroup.index]
  exact Nat.cast_card.symm

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.ProfiniteIntegers_ProfiniteIntegerCore
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

/-!
# Profinite completion of the integers

We construct `ℤ̂` as the topological closure of the diagonal image of `ℤ`
inside the product of all positive cyclic quotients `ZMod n`.  This realizes
the canonical reduction maps and the dense integer embedding directly in
Mathlib.
-/

open scoped Topology

/-- The profinite integer model is totally disconnected. -/
instance instTotallyDisconnectedSpaceZHat : TotallyDisconnectedSpace ZHat := by
  change TotallyDisconnectedSpace ZHatClosureModel
  infer_instance

/-- The multiplicative presentation of `ZHat` remains totally disconnected. -/
instance instTotallyDisconnectedSpaceMultiplicativeZHat : TotallyDisconnectedSpace (Multiplicative ZHat) := by
  change TotallyDisconnectedSpace ZHat
  infer_instance

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_FrobeniusFixedField
attribute [-instance] _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.orbitQuotientClosedCyclicEquiv_mk _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# normalized degree and Frobenius theory: the fixed field of a Frobenius lift

This file gives the group-dual form of the Frobenius fixed-field theorem.  If `σ` is a
Frobenius lift in `G(\widetilde L | K)`, the subgroup `Γ` fixing the
field `Σ` is the closed subgroup topologically generated by `σ`.
-/

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The cardinal comparison used in the classical proof of the Frobenius fixed-field theorem:
a continuous map from a profinite procyclic group to `ℤ̂` which sends a
topological generator to `1` is injective. -/
theorem injective_of_topologicallyGenerates_zHat_one
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [CompactSpace A] [T2Space A]
    [TotallyDisconnectedSpace A]
    (f : A →ₜ* ZHatMul) (x : A)
    (hxgen : TopologicallyGenerates ({x} : Set A))
    (hfx : f x = Multiplicative.ofAdd (1 : ZHat)) :
    Function.Injective f := by
  intro a b hab
  suffices h : a⁻¹ * b = 1 by
    exact inv_mul_eq_one.mp h
  let y := a⁻¹ * b
  have hfy : f y = 1 := by
    dsimp [y]
    rw [map_mul, map_inv, hab, inv_mul_cancel]
  by_contra hy
  obtain ⟨U, hyU⟩ := exists_openNormalSubgroup_not_mem hy
  let : Finite (A ⧸ (U : Subgroup A)) :=
    Subgroup.quotient_finite_of_isOpen (U : Subgroup A)
      U.toOpenSubgroup.isOpen'
  let : DiscreteTopology (A ⧸ (U : Subgroup A)) :=
    QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen'
  let m := Nat.card (A ⧸ (U : Subgroup A))
  have hm : 0 < m := by
    dsimp [m]
    exact Nat.card_pos
  let : NeZero m := ⟨hm.ne'⟩
  let q : A →ₜ* (A ⧸ (U : Subgroup A)) :=
    continuousQuotientMk (U : Subgroup A)
  have hqx :
      q x = QuotientGroup.mk' (U : Subgroup A) x := rfl
  have hqgen : TopologicallyGenerates ({q x} : Set
      (A ⧸ (U : Subgroup A))) := by
    have h := topologicallyGenerates_quotient_image (U : Subgroup A) hxgen
    simpa only [Set.image_singleton, hqx] using h
  have hqpow : (q x) ^ m = 1 := by
    exact pow_card_eq_one'
  let H : ClosedSubgroup A :=
    closedSubgroupGenerated ({x ^ m} : Set A)
  have hHU : H.toSubgroup ≤ (U : Subgroup A) := by
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      apply (QuotientGroup.eq_one_iff (x ^ m)).mp
      change q (x ^ m) = 1
      rw [map_pow]
      simpa only [hqx] using hqpow
    · exact Subgroup.isClosed_of_isOpen (U : Subgroup A) U.isOpen'
  let : IsClosed (H.toSubgroup : Set A) := H.isClosed'
  let B := A ⧸ H.toSubgroup
  let qH : A →ₜ* B := continuousQuotientMk H.toSubgroup
  have hqHx :
      qH x = QuotientGroup.mk' H.toSubgroup x := rfl
  have hqHgen : TopologicallyGenerates ({qH x} : Set B) := by
    have h := topologicallyGenerates_quotient_image H.toSubgroup hxgen
    simpa only [Set.image_singleton, hqHx] using h
  have hqHpow : (qH x) ^ m = 1 := by
    rw [← map_pow]
    change (QuotientGroup.mk' H.toSubgroup) (x ^ m) = 1
    apply (QuotientGroup.eq_one_iff (N := H.toSubgroup) (x ^ m)).2
    change x ^ m ∈
      (closedSubgroupGenerated ({x ^ m} : Set A) : Subgroup A)
    exact Subgroup.le_topologicalClosure _
      (Subgroup.subset_closure (by simp))
  have hqHfiniteOrder : IsOfFinOrder (qH x) := by
    rw [← orderOf_pos_iff]
    have hdvd : orderOf (qH x) ∣ m :=
      orderOf_dvd_of_pow_eq_one hqHpow
    exact Nat.pos_of_dvd_of_pos hdvd hm
  have hzpowersClosed :
      IsClosed ((Subgroup.zpowers (qH x) : Subgroup B) : Set B) :=
    (Set.finite_coe_iff.mp (finite_zpowers.mpr hqHfiniteOrder)).isClosed
  have hzpowersTopologicalClosure :
      (Subgroup.zpowers (qH x)).topologicalClosure =
        Subgroup.zpowers (qH x) := by
    apply SetLike.ext'
    rw [Subgroup.topologicalClosure_coe]
    rw [hzpowersClosed.closure_eq]
  have hzpowersTop : Subgroup.zpowers (qH x) = ⊤ := by
    rw [TopologicallyGenerates, ← Subgroup.zpowers_eq_closure,
      hzpowersTopologicalClosure] at hqHgen
    exact hqHgen
  let : Finite (Subgroup.zpowers (qH x)) :=
    finite_zpowers.mpr hqHfiniteOrder
  let : Finite B :=
    Finite.of_injective
      (fun b : B =>
        (⟨b, by rw [hzpowersTop]; trivial⟩ : Subgroup.zpowers (qH x)))
      (by
        intro a b hab
        exact congrArg Subtype.val hab)
  have hcardB : Nat.card B = orderOf (qH x) :=
    (orderOf_eq_card_of_zpowers_eq_top hzpowersTop).symm
  have hcardBle : Nat.card B ≤ m := by
    rw [hcardB]
    exact orderOf_le_of_pow_eq_one hm hqHpow
  let r : A →ₜ* Multiplicative (ZMod m) :=
    (zHatReductionMul m hm).comp f
  have hrx : r x = Multiplicative.ofAdd (1 : ZMod m) := by
    apply Multiplicative.ext
    change zHatReduction m hm (f x).toAdd = 1
    rw [hfx]
    simp
  have hHker : H.toSubgroup ≤ r.toMonoidHom.ker := by
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      change r (x ^ m) = 1
      rw [map_pow, hrx]
      apply Multiplicative.ext
      simp
    · change IsClosed {z : A | r z = 1}
      let : T2Space (Multiplicative (ZMod m)) := by
        change T2Space (ZMod m)
        infer_instance
      exact isClosed_eq r.continuous_toFun continuous_const
  let rbar : B →ₜ* Multiplicative (ZMod m) :=
    continuousQuotientLift H.toSubgroup r hHker
  have hrbarSurj : Function.Surjective rbar := by
    intro z
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective z.toAdd
    refine ⟨(qH x) ^ k, ?_⟩
    apply Multiplicative.ext
    rw [map_zpow]
    change ((r x) ^ k).toAdd = z.toAdd
    rw [hrx]
    simpa using hk
  have hcodCard : Nat.card (Multiplicative (ZMod m)) = m := by
    calc
      Nat.card (Multiplicative (ZMod m)) =
          Nat.card (ZMod m) :=
        Nat.card_congr Multiplicative.toAdd
      _ = m := Nat.card_zmod m
  have hcardLower : m ≤ Nat.card B := by
    rw [← hcodCard]
    exact Nat.card_le_card_of_surjective rbar hrbarSurj
  have hcardEq : Nat.card B =
      Nat.card (Multiplicative (ZMod m)) := by
    rw [hcodCard]
    exact le_antisymm hcardBle hcardLower
  have hrbarInj : Function.Injective rbar :=
    (Nat.bijective_iff_surjective_and_card rbar).mpr
      ⟨hrbarSurj, hcardEq⟩ |>.1
  have hry : r y = 1 := by
    change zHatReductionMul m hm (f y) = 1
    rw [hfy, map_one]
  have hqy : qH y = 1 := by
    apply hrbarInj
    change r y = r 1
    rw [hry, map_one]
  change (QuotientGroup.mk' H.toSubgroup) y = 1 at hqy
  have hyH : y ∈ H.toSubgroup :=
    (QuotientGroup.eq_one_iff (N := H.toSubgroup) y).mp hqy
  exact hyU (hHU hyH)

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_PadicCyclicClosure
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Cyclic closures detected by a p-adic degree

This file isolates the topological group argument used in the
finite-place Frobenius construction.  A continuous `ℤ_p`-degree with
finite kernel detects openness of the closed subgroup generated by
any element of nonzero degree.
-/

open scoped Topology

namespace ClassFormation

noncomputable section

universe u

variable
    {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G]

/-- The closed subgroup topologically generated by one element. -/
def padicCyclicClosure (τ : G) : ClosedSubgroup G :=
  closedSubgroupGenerated (Set.range (fun _ : Unit => τ))

/-- The distinguished element belongs to its p-adic cyclic closure. -/
def padicCyclicClosureGenerator (τ : G) :
    padicCyclicClosure τ :=
  closedSubgroupGeneratedMap (fun _ : Unit => τ) ()

/-- A continuous p-adic degree with finite kernel makes the cyclic
closure of every element of nonzero degree open.

The degree image of the cyclic closure is compact, hence closed in
`ℤ_p`; it contains a nonzero element, hence is open.  Its relative
index in the full degree image is therefore finite.  The remaining
relative-index factor lies in the finite degree kernel. -/
theorem padicCyclicClosure_isOpen_of_degree_ne_one
    (p : ℕ) [Fact p.Prime]
    (degree : G →ₜ* Multiplicative ℤ_[p])
    [Finite degree.toMonoidHom.ker]
    (τ : G)
    (hτ : degree τ ≠ 1) :
    IsOpen ((padicCyclicClosure τ : Subgroup G) : Set G) := by
  let Γ : ClosedSubgroup G :=
    padicCyclicClosure τ
  let inclusion : Γ →ₜ* G :=
    { toMonoidHom := Γ.toSubgroup.subtype
      continuous_toFun := continuous_subtype_val }
  let restrictedDegree : Γ →ₜ* Multiplicative ℤ_[p] :=
    degree.comp inclusion
  let R : Subgroup (Multiplicative ℤ_[p]) :=
    restrictedDegree.toMonoidHom.range
  let H : AddSubgroup ℤ_[p] :=
    R.toAddSubgroup'
  have hRclosed :
      IsClosed (R : Set (Multiplicative ℤ_[p])) := by
    change
      IsClosed (Set.range restrictedDegree)
    exact
      (isCompact_range
        restrictedDegree.continuous_toFun).isClosed
  have hHclosed :
      IsClosed (H : Set ℤ_[p]) := by
    change
      IsClosed
        ((fun z : ℤ_[p] => Multiplicative.ofAdd z) ⁻¹'
          (R : Set (Multiplicative ℤ_[p])))
    exact hRclosed.preimage continuous_ofAdd
  have hHne : H ≠ ⊥ := by
    intro hbot
    let γ : Γ :=
      padicCyclicClosureGenerator τ
    have hdegreeMem :
        degree τ ∈ R := by
      exact ⟨γ, rfl⟩
    have hdegreeAddMem :
        Multiplicative.toAdd (degree τ) ∈ H := by
      rw [Subgroup.mem_toAddSubgroup']
      exact hdegreeMem
    rw [hbot] at hdegreeAddMem
    have hdegreeAddZero :
        Multiplicative.toAdd (degree τ) = 0 := by
      simpa only [AddSubgroup.mem_bot] using hdegreeAddMem
    apply hτ
    apply Multiplicative.ext
    change Multiplicative.toAdd (degree τ) = 0
    exact hdegreeAddZero
  have hHopen :
      IsOpen (H : Set ℤ_[p]) :=
    PadicInt.addSubgroup_isOpen_of_isClosed_of_ne_bot
      p H hHclosed hHne
  have hRopen :
      IsOpen (R : Set (Multiplicative ℤ_[p])) := by
    change
      IsOpen
        ((fun z : Multiplicative ℤ_[p] =>
          Multiplicative.toAdd z) ⁻¹' (H : Set ℤ_[p]))
    exact hHopen.preimage continuous_toAdd
  have hRle :
      R ≤ degree.toMonoidHom.range := by
    rintro y ⟨γ, rfl⟩
    exact ⟨γ.1, rfl⟩
  have hDegreeRangeOpen :
      IsOpen
        (degree.toMonoidHom.range :
          Set (Multiplicative ℤ_[p])) :=
    Subgroup.isOpen_mono hRle hRopen
  have hRsubgroupOpen :
      IsOpen
        (R.subgroupOf degree.toMonoidHom.range :
          Set degree.toMonoidHom.range) :=
    Subgroup.subgroupOf_isOpen
      degree.toMonoidHom.range R hRopen
  let :
      Finite
        (degree.toMonoidHom.range ⧸
          R.subgroupOf degree.toMonoidHom.range) :=
    Subgroup.quotient_finite_of_isOpen'
      degree.toMonoidHom.range
      (R.subgroupOf degree.toMonoidHom.range)
      hDegreeRangeOpen hRsubgroupOpen
  have hΓmap :
      Γ.toSubgroup.map degree.toMonoidHom = R := by
    ext z
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨⟨γ, hγ⟩, rfl⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨γ.1, γ.2, rfl⟩
  have htopmap :
      (⊤ : Subgroup G).map degree.toMonoidHom =
        degree.toMonoidHom.range := by
    ext z
    constructor
    · rintro ⟨g, _, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, Subgroup.mem_top g, rfl⟩
  have himage :
      (Γ.toSubgroup.map degree.toMonoidHom).relIndex
          ((⊤ : Subgroup G).map degree.toMonoidHom) ≠ 0 := by
    rw [hΓmap, htopmap, Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  let T : Subgroup G :=
    (⊤ : Subgroup G) ⊓ degree.toMonoidHom.ker
  let toKernel : T → degree.toMonoidHom.ker :=
    fun x => ⟨x.1, x.2.2⟩
  let : Finite T :=
    Finite.of_injective toKernel (by
      intro x y hxy
      apply Subtype.ext
      simpa [toKernel] using
        congrArg (fun z : degree.toMonoidHom.ker => (z : G)) hxy)
  have hkernel :
      (Γ.toSubgroup ⊓ degree.toMonoidHom.ker).relIndex
          ((⊤ : Subgroup G) ⊓ degree.toMonoidHom.ker) ≠ 0 := by
    rw [Subgroup.relIndex]
    change
      ((Γ.toSubgroup ⊓ degree.toMonoidHom.ker).subgroupOf T).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have hrel :
      Γ.toSubgroup.relIndex (⊤ : Subgroup G) ≠ 0 := by
    rw [
      relIndex_eq_map_relIndex_mul_inf_ker_relIndex
        degree.toMonoidHom le_top]
    exact Nat.mul_ne_zero himage hkernel
  have hindex : Γ.toSubgroup.index ≠ 0 := by
    simpa only [Subgroup.relIndex_top_right] using hrel
  let : Γ.toSubgroup.FiniteIndex :=
    ⟨hindex⟩
  exact
    Γ.toSubgroup.isOpen_of_isClosed_of_finiteIndex
      Γ.isClosed'

omit [CompactSpace G] in
/-- On the cyclic closure of an element whose finite coordinate has
`p`-power order and whose `p`-adic degree is a positive integer, the
`p`-adic degree is injective.

The proof uses one carefully chosen open neighborhood.  If a limit of
integral powers has trivial `p`-adic degree, approximate it by a power
whose degree lies in `(n * p^m)ℤ_p`.  Cancellation of the nonzero
integer `n` forces the exponent to be divisible by `p^m`, so its finite
coordinate is trivial as well. -/
theorem padicCyclicClosure_degree_injective_of_primePower_finiteCoordinate
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (p : ℕ) [Fact p.Prime]
    (finiteCoordinate : G →ₜ* Q)
    (degree : G →ₜ* Multiplicative ℤ_[p])
    (hjoint :
      Function.Injective
        (fun g : G => (finiteCoordinate g, degree g)))
    (γ : G)
    (m n : ℕ)
    (hn : 0 < n)
    (hfinite : (finiteCoordinate γ) ^ (p ^ m) = 1)
    (hdegree :
      degree γ =
        (Multiplicative.ofAdd (1 : ℤ_[p])) ^ n) :
    Function.Injective
      ((degree.toMonoidHom.comp
        (padicCyclicClosure γ).toSubgroup.subtype) :
        padicCyclicClosure γ →
          Multiplicative ℤ_[p]) := by
  let Γ : ClosedSubgroup G :=
    padicCyclicClosure γ
  let inclusion : Γ.toSubgroup →ₜ* G :=
    { toMonoidHom := Γ.toSubgroup.subtype
      continuous_toFun := continuous_subtype_val }
  let restrictedDegree :
      Γ.toSubgroup →ₜ* Multiplicative ℤ_[p] :=
    degree.comp inclusion
  have hkernel :
      ∀ z : Γ.toSubgroup,
        restrictedDegree z = 1 →
          z = 1 := by
    intro z hzdegree
    let c : ℕ :=
      n * p ^ m
    let J : AddSubgroup ℤ_[p] :=
      (Ideal.span ({(c : ℤ_[p])} : Set ℤ_[p])).toAddSubgroup
    have hcne : c ≠ 0 := by
      exact
        Nat.mul_ne_zero (Nat.ne_of_gt hn)
          (pow_ne_zero m (Fact.out : p.Prime).ne_zero)
    have hJrange :
        (J : Set ℤ_[p]) =
          Set.range (fun a : ℤ_[p] => a * (c : ℤ_[p])) := by
      ext x
      constructor
      · intro hx
        change
          x ∈ Ideal.span
            ({(c : ℤ_[p])} : Set ℤ_[p]) at hx
        rw [Ideal.mem_span_singleton] at hx
        obtain ⟨a, rfl⟩ := hx
        exact ⟨a, mul_comm _ _⟩
      · rintro ⟨a, rfl⟩
        change
          a * (c : ℤ_[p]) ∈
            Ideal.span ({(c : ℤ_[p])} : Set ℤ_[p])
        rw [Ideal.mem_span_singleton]
        exact ⟨a, mul_comm _ _⟩
    have hJclosed : IsClosed (J : Set ℤ_[p]) := by
      rw [hJrange]
      exact
        (isCompact_range
          (continuous_id.mul continuous_const)).isClosed
    have hJne : J ≠ ⊥ := by
      intro hbot
      have hcMem : (c : ℤ_[p]) ∈ J := by
        change
          (c : ℤ_[p]) ∈
            Ideal.span ({(c : ℤ_[p])} : Set ℤ_[p])
        exact Ideal.subset_span (by simp)
      rw [hbot] at hcMem
      have hc0 : (c : ℤ_[p]) = 0 := by
        simpa only [AddSubgroup.mem_bot] using hcMem
      have hc0' : c = 0 := by
        exact_mod_cast hc0
      exact hcne hc0'
    have hJopen : IsOpen (J : Set ℤ_[p]) :=
      PadicInt.addSubgroup_isOpen_of_isClosed_of_ne_bot
        p J hJclosed hJne
    let O : Set G :=
      finiteCoordinate ⁻¹' {finiteCoordinate z.1} ∩
        (fun g : G =>
          Multiplicative.toAdd (degree g)) ⁻¹'
            (J : Set ℤ_[p])
    have hOopen : IsOpen O := by
      exact
        ((isOpen_discrete
          ({finiteCoordinate z.1} : Set Q)).preimage
            finiteCoordinate.continuous_toFun).inter
          (hJopen.preimage
            (continuous_toAdd.comp
              degree.continuous_toFun))
    have hzO : z.1 ∈ O := by
      refine ⟨rfl, ?_⟩
      change
        Multiplicative.toAdd (restrictedDegree z) ∈ J
      rw [hzdegree]
      exact J.zero_mem
    have hzclosure :
        z.1 ∈
          closure
            (((Subgroup.closure
              (Set.range (fun _ : Unit => γ))) :
                Subgroup G) :
              Set G) := by
      exact z.2
    obtain ⟨y, hyO, hyGenerated⟩ :=
      mem_closure_iff.mp hzclosure O hOopen hzO
    have hrange :
        Set.range (fun _ : Unit => γ) =
          ({γ} : Set G) := by
      ext x
      constructor
      · rintro ⟨u, rfl⟩
        simp
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        exact ⟨(), hx.symm⟩
    have hyZPowers :
        y ∈ Subgroup.zpowers γ := by
      rw [Subgroup.zpowers_eq_closure, ← hrange]
      exact hyGenerated
    obtain ⟨k, hk⟩ :=
      Subgroup.mem_zpowers_iff.mp hyZPowers
    have hyJ :
        Multiplicative.toAdd (degree y) ∈ J :=
      hyO.2
    have hyJ' :
        (k : ℤ_[p]) * (n : ℤ_[p]) ∈ J := by
      rw [← hk, map_zpow, hdegree] at hyJ
      simpa using hyJ
    change
      (k : ℤ_[p]) * (n : ℤ_[p]) ∈
        Ideal.span ({(c : ℤ_[p])} : Set ℤ_[p]) at hyJ'
    rw [Ideal.mem_span_singleton] at hyJ'
    obtain ⟨a, ha⟩ := hyJ'
    have hnZ : (n : ℤ_[p]) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    have hcancel :
        a * (p : ℤ_[p]) ^ m =
          (k : ℤ_[p]) := by
      apply mul_left_cancel₀ hnZ
      calc
        (n : ℤ_[p]) *
            (a * (p : ℤ_[p]) ^ m) =
            a * (c : ℤ_[p]) := by
              simp only [c, Nat.cast_mul, Nat.cast_pow]
              ring
        _ = (k : ℤ_[p]) * (n : ℤ_[p]) := by
          simpa [mul_comm] using ha.symm
        _ = (n : ℤ_[p]) * (k : ℤ_[p]) := mul_comm _ _
    have hkSpan :
        (k : ℤ_[p]) ∈
          Ideal.span
            ({(p : ℤ_[p]) ^ m} : Set ℤ_[p]) := by
      rw [Ideal.mem_span_singleton]
      exact ⟨a, by simpa [mul_comm] using hcancel.symm⟩
    have hkMod :
        PadicInt.toZModPow m (k : ℤ_[p]) = 0 := by
      rw [← PadicInt.ker_toZModPow m,
        RingHom.mem_ker] at hkSpan
      exact hkSpan
    have hkMod' :
        (k : ZMod (p ^ m)) = 0 := by
      simpa only [map_intCast] using hkMod
    have hkdiv :
        ((p ^ m : ℕ) : ℤ) ∣ k :=
      (CharP.intCast_eq_zero_iff
        (ZMod (p ^ m)) (p ^ m) k).1 hkMod'
    obtain ⟨l, hl⟩ := hkdiv
    have hfinitePower :
        finiteCoordinate y = 1 := by
      rw [← hk, map_zpow, hl]
      calc
        finiteCoordinate γ ^
              (((p ^ m : ℕ) : ℤ) * l) =
            (finiteCoordinate γ ^
              ((p ^ m : ℕ) : ℤ)) ^ l := by
                rw [zpow_mul]
        _ = 1 := by
          rw [zpow_natCast, hfinite, one_zpow]
    have hzfinite :
        finiteCoordinate z.1 = 1 := by
      exact hyO.1.symm.trans hfinitePower
    have hzG : z.1 = (1 : G) := by
      apply hjoint
      apply Prod.ext
      · simpa only [map_one] using hzfinite
      · have hzdegree' : degree z.1 = 1 := by
          dsimp [restrictedDegree, inclusion] at hzdegree
          exact hzdegree
        simpa only [map_one] using hzdegree'
    exact Subtype.ext hzG
  intro x y hxy
  have hxy' : restrictedDegree x = restrictedDegree y := by
    change degree (x : G) = degree (y : G)
    change degree (x : G) = degree (y : G) at hxy
    exact hxy
  have hquotient :
      restrictedDegree (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy', mul_inv_cancel]
  have hunit :
      x * y⁻¹ = 1 :=
    hkernel (x * y⁻¹) hquotient
  exact mul_inv_eq_one.mp hunit

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_Valuation
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
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
# normalized degree and Frobenius theory: henselian valuations

The multiplicative coefficient module is represented additively, as
in .  Accordingly a valuation and a norm are additive homomorphisms.  This
file formalizes the valuation-quotient axiom and constructs the normalized valuations of
normalized-valuation functoriality.
-/

noncomputable section

universe u

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- For the full profinite-integer value group, the canonical
inclusion-and-reduction quotient map is bijective. -/
theorem canonicalValueQuotientMap_top_bijective
    (n : ℕ) (hn : 0 < n) :
    Function.Bijective
      (canonicalValueQuotientMap
        (⊤ : AddSubgroup ZHat) n hn) := by
  constructor
  · intro q₁ q₂
    refine Quotient.inductionOn' q₁ ?_
    intro z₁
    refine Quotient.inductionOn' q₂ ?_
    intro z₂ h
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have hz :
        zHatReduction n hn
            ((z₁ : ZHat) - (z₂ : ZHat)) =
          0 := by
      rw [map_sub]
      change
        zHatReduction n hn (z₁ : ZHat) =
          zHatReduction n hn (z₂ : ZHat) at h
      rw [h, sub_self]
    have hrange :
        (z₁ : ZHat) - (z₂ : ZHat) ∈
          (zHatMulNat n).toAddMonoidHom.range := by
      rw [zHatMulNat_range_eq_ker_reduction n hn]
      exact hz
    obtain ⟨w, hw⟩ := hrange
    refine ⟨⟨w, AddSubgroup.mem_top w⟩, ?_⟩
    apply Subtype.ext
    exact hw
  · intro a
    obtain ⟨z, hz⟩ :=
      zHatReduction_surjective n hn a
    exact
      ⟨QuotientAddGroup.mk'
          (nsmulWithin (⊤ : AddSubgroup ZHat) n)
          ⟨z, AddSubgroup.mem_top z⟩,
        hz⟩

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_UnitCohomologyAxiom
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.infiniteNormQuotientAddCommGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
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
# The abstract reciprocity construction: the unit-cohomology axiom

The coefficient group in the unit-cohomology axiom is the actual unit subgroup `U_L`, with
the action of the actual quotient `G_K / G_L`.  The two Tate groups are the
homology objects of the finite-cyclic norm complexes.
-/

noncomputable section

open CategoryTheory

universe u

section Generic

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteCyclicSubextension

variable {K : FiniteAbstractField G}

/-- Structural total ramification of the underlying finite extension. -/
def IsTotallyRamified (E : FiniteCyclicSubextension K)
    (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsTotallyRamified D

end FiniteCyclicSubextension

end Generic

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace FiniteUnramifiedCyclicExtension

variable {K : FiniteAbstractField G}

/-- The absolute quotient attached to a finite unramified cyclic extension is finite. -/
noncomputable instance instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField (E : FiniteUnramifiedCyclicExtension D K) :
    Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.field (le_baseField E.field)) :=
  relativeTowerQuotientFinite (baseField G) K.field E.field E.below
    (le_baseField K.field)

end FiniteUnramifiedCyclicExtension

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_ClassFieldAxiom
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.infiniteNormQuotientAddCommGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.maximalUnramifiedNormClass_eq_zero_iff _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.mem_maximalUnramifiedNormSubgroup_iff _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.infiniteNormClass_eq_zero_iff _root_.ClassFormation.infiniteNormQuotientConcreteEquiv_infiniteNormClass _root_.ClassFormation.infiniteNormQuotientLift_infiniteNormClass _root_.ClassFormation.mem_infiniteNormSubgroup_iff _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# Abstract reciprocity: the class field axiom

The coefficient group for a finite cyclic extension `L / K` is the actual
fixed module `A_L`, descended to the actual quotient `G_K / G_L`.  Thus the
two numbers below are the orders of the Tate groups occurring in the
original statement the class-field axiom, rather than cardinality data attached to an
auxiliary reciprocity map.
-/

noncomputable section

open CategoryTheory

/-! `Representation.Rep` places its coefficient ring and acting group in the
same universe.  The shared `IntegralRepGroupType` boundary records the
universe forced by the coefficient ring `ℤ` without scattering raw
universe-zero declarations through the reciprocity API. -/

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace SatisfiesClassFieldAxiom

variable {A : Rep ℤ G}

/-- The degree-minus-one half of the class-field axiom for a bundled cyclic
extension. -/
theorem tateHMinusOne_card
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1 :=
  (hcf K E).tateHMinusOne_card

/-- The order-one assertion in the class-field axiom gives actual vanishing of
`H⁻¹(G(L/K), A_L)`. -/
theorem tateHMinusOne_isZero
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    Limits.IsZero (tateCohomology (E.fixedRepresentation A) (-1)) := by
  let H := tateCohomology (E.fixedRepresentation A) (-1)
  let : Finite H := (hcf K E).finiteTateHMinusOne
  have hcard : Nat.card H = 1 := by
    simpa [H] using hcf.tateHMinusOne_card K E
  let : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact ModuleCat.isZero_of_subsingleton H

end SatisfiesClassFieldAxiom

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FiniteNormQuotient
attribute [-instance] _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
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
# The abstract reciprocity construction: passage to a finite norm quotient

For finite `L | K`, the universal norm subgroup from `\widetilde L` is
contained in the single norm image from `L`.  Hence the reciprocity construction descends
canonically to `A_K / N_{L|K}A_L`, the target in the finite reciprocity equivalence.
-/

noncomputable section

section finiteNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Every class in the finite norm quotient is killed by `[L : K]`.
This is the actual norm identity
`N_{L/K}(a) = [L : K] a` for an element already fixed by `G_K`. -/
theorem finiteNormQuotient_degree_nsmul_eq_zero
    (A : Rep ℤ G) (E : DegreeData.FiniteAbstractExtension G)
    (q : FiniteNormQuotient A E.base E.field E.below) :
    (E.degree : ℕ) • q = 0 := by
  refine FiniteNormQuotient.induction_on A E.base E.field E.below q ?_
  intro a
  unfold finiteNormClass
  rw [← map_nsmul]
  apply (finiteNormClass_eq_zero_iff A E.base E.field E.below _).2
  refine ⟨fixedFieldInclusion A E.base E.field E.below a, ?_⟩
  exact relativeNorm_fixedFieldInclusion A E a

end finiteNorms

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_FiniteGaloisSubextension
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.upperQuotient_groupInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.FiniteGaloisSubextension.lowerQuotientEquiv_mk _root_.ClassFormation.FiniteGaloisSubextension.lowerQuotientEquiv_mk_coe _root_.ClassFormation.FiniteGaloisSubextension.lowerRestrictionHom_apply_coe _root_.ClassFormation.FiniteGaloisSubextension.mem_intermediateSubgroup_iff _root_.ClassFormation.FiniteGaloisSubextension.upperQuotientEquiv_mk_mk _root_.ClassFormation.FiniteGaloisSubextension.upperQuotientMk_apply _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
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
# Finite Galois extensions above an abstract field

The norm topology is indexed by the actual finite Galois extensions
of a fixed abstract field.  This file packages those extensions and their
composita contravariantly as intersections of closed subgroups.
-/

noncomputable section

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- Eliminate a finite Galois quotient without exposing a chosen
representative. -/
protected theorem extensionQuotient_inductionOn
    (L : FiniteGaloisSubextension K) {motive : L.extensionQuotient → Prop}
    (q : L.extensionQuotient)
    (mk : ∀ k : K.toSubgroup, motive (L.extensionQuotientMk k)) :
    motive q := by
  exact @Quotient.inductionOn' K.toSubgroup
    (QuotientGroup.leftRel (extensionSubgroup K L.field L.below))
    motive q mk

/-- Transport an unramifiedness proof through the finite-to-Galois
forgetful map. -/
theorem isUnramified_toGaloisSubextension
    (L : FiniteGaloisSubextension K) (D : DegreeData G)
    (hL : L.IsUnramified D) :
    L.toGaloisSubextension.IsUnramified D :=
  (L.toGaloisSubextension_isUnramified_iff D).2 hL

/-- Unramifiedness is the canonical inertia-containment condition. -/
theorem isUnramified_iff_inertia_le (L : FiniteGaloisSubextension K)
    (D : DegreeData G) :
    L.IsUnramified D ↔
      K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup :=
  L.toFiniteAbstractExtension.isUnramified_iff_inertia_le D

/-- Retain the finite-over-base endpoint bundles of a finite Galois
subextension of an abstract field which is finite over the distinguished
base. -/
noncomputable def toFiniteAbstractFieldExtension
    {K : FiniteAbstractField G} (L : FiniteGaloisSubextension K.field) :
    FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) :=
    L.finite
  exact FiniteAbstractFieldExtension.ofInclusion L.field K L.below

/-- Base change of a finite Galois extension `M / K` to an arbitrary
intermediate field `L / K`.  Contravariantly, the compositum `ML` is the
intersection `G_M ∩ G_L`; normality and finite index are pulled back from
`G_M ◁ G_K`. -/
def baseChange (M : FiniteGaloisSubextension K) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) : FiniteGaloisSubextension L where
  field := L ⊓ M.field
  below := inf_le_left
  normal := by
    let f : L.toSubgroup →* K.toSubgroup := Subgroup.inclusion hLK
    have heq : extensionSubgroup L (L ⊓ M.field) inf_le_left =
        (extensionSubgroup K M.field M.below).comap f := by
      ext x
      rw [mem_extensionSubgroup_iff, Subgroup.mem_comap,
        mem_extensionSubgroup_iff]
      change (x : G) ∈ L ⊓ M.field ↔ (x : G) ∈ M.field
      exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
    rw [heq]
    let : (extensionSubgroup K M.field M.below).Normal := M.normal
    infer_instance
  finite := by
    let f : L.toSubgroup →* K.toSubgroup := Subgroup.inclusion hLK
    let E := extensionSubgroup K M.field M.below
    have heq : extensionSubgroup L (L ⊓ M.field) inf_le_left = E.comap f := by
      ext x
      rw [mem_extensionSubgroup_iff, Subgroup.mem_comap]
      dsimp only [E, f, Subgroup.inclusion]
      rw [mem_extensionSubgroup_iff]
      change (x : G) ∈ L ⊓ M.field ↔ (x : G) ∈ M.field
      exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
    let : Finite (K.toSubgroup ⧸ E) := M.finite
    let : E.Normal := M.normal
    have hE0 : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hrel0 : E.relIndex f.range ≠ 0 := by
      intro hzero
      have hdvd : E.relIndex f.range ∣ E.index :=
        E.relIndex_dvd_index_of_normal f.range
      rw [hzero, zero_dvd_iff] at hdvd
      exact hE0 hdvd
    apply Nat.finite_of_card_ne_zero
    change (extensionSubgroup L (L ⊓ M.field) inf_le_left).index ≠ 0
    rw [heq, E.index_comap f]
    exact hrel0

/-- The compositum `L₁L₂`, represented by `G_{L₁} ∩ G_{L₂}`. -/
def compositum (L₁ L₂ : FiniteGaloisSubextension K) :
    FiniteGaloisSubextension K where
  field := L₁.field ⊓ L₂.field
  below := fun _ h => L₁.below h.1
  normal := by
    have heq : extensionSubgroup K (L₁.field ⊓ L₂.field)
        (fun _ h => L₁.below h.1) =
        extensionSubgroup K L₁.field L₁.below ⊓
          extensionSubgroup K L₂.field L₂.below := by
      ext k
      simp only [Subgroup.mem_inf, mem_extensionSubgroup_iff]
      constructor
      · intro hk
        exact ⟨hk.1, hk.2⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₂⟩
    rw [heq]
    let : (extensionSubgroup K L₁.field L₁.below).Normal := L₁.normal
    let : (extensionSubgroup K L₂.field L₂.below).Normal := L₂.normal
    infer_instance
  finite := by
    have heq : extensionSubgroup K (L₁.field ⊓ L₂.field)
        (fun _ h => L₁.below h.1) =
        extensionSubgroup K L₁.field L₁.below ⊓
          extensionSubgroup K L₂.field L₂.below := by
      ext k
      simp only [Subgroup.mem_inf, mem_extensionSubgroup_iff]
      constructor
      · intro hk
        exact ⟨hk.1, hk.2⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₂⟩
    let : (extensionSubgroup K L₁.field L₁.below).FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
        (extensionSubgroup K L₁.field L₁.below) L₁.finite
    let : (extensionSubgroup K L₂.field L₂.below).FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
        (extensionSubgroup K L₂.field L₂.below) L₂.finite
    rw [heq]
    exact Subgroup.finite_quotient_of_finiteIndex

/-- The constructed Galois compositum satisfies the left comparison bound. -/
theorem compositum_le_left (L₁ L₂ : FiniteGaloisSubextension K) :
    (L₁.compositum L₂).field.toSubgroup ≤ L₁.field.toSubgroup :=
  inf_le_left

end FiniteGaloisSubextension

end GroupOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The norm group from a compositum is contained in the norm group from
its first factor. -/
theorem finiteNormSubgroup_compositum_le_left
    (A : Rep ℤ G) (L₁ L₂ : FiniteGaloisSubextension K) :
    letI := (L₁.compositum L₂).finite
    letI := L₁.finite
    finiteNormSubgroup A K (L₁.compositum L₂).field
        (L₁.compositum L₂).below ≤
      finiteNormSubgroup A K L₁.field L₁.below := by
  let P := L₁.compositum L₂
  let hPL₁ := L₁.compositum_le_left L₂
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K P.field P.below) := P.finite
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K L₁.field L₁.below) := L₁.finite
  have hPKindex : P.field.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hPLindex : P.field.toSubgroup.relIndex L₁.field.toSubgroup ≠ 0 := by
    intro hzero
    have hmul := Subgroup.relIndex_mul_relIndex
      P.field.toSubgroup L₁.field.toSubgroup K.toSubgroup hPL₁ L₁.below
    rw [hzero, zero_mul] at hmul
    exact hPKindex hmul.symm
  let hPLfinite : Finite (L₁.field.toSubgroup ⧸
      extensionSubgroup L₁.field P.field hPL₁) := by
    apply Nat.finite_of_card_ne_zero
    change (extensionSubgroup L₁.field P.field hPL₁).index ≠ 0
    simpa [Subgroup.relIndex] using hPLindex
  let T : DegreeData.FiniteTower G := {
    top := P.field
    middle := L₁.field
    base := K
    top_le_middle := hPL₁
    middle_le_base := L₁.below
    finiteTopQuotient := hPLfinite
    finiteBaseQuotient := L₁.finite }
  rintro x ⟨a, rfl⟩
  refine ⟨relativeNorm A L₁.field P.field hPL₁ a, ?_⟩
  exact T.norm_trans_apply A a

/-- The symmetric norm-group containment for the second factor. -/
theorem finiteNormSubgroup_compositum_le_right
    (A : Rep ℤ G) (L₁ L₂ : FiniteGaloisSubextension K) :
    letI := (L₁.compositum L₂).finite
    letI := L₂.finite
    finiteNormSubgroup A K (L₁.compositum L₂).field
        (L₁.compositum L₂).below ≤
      finiteNormSubgroup A K L₂.field L₂.below := by
  simpa [compositum, inf_comm] using
    finiteNormSubgroup_compositum_le_left A L₂ L₁

end FiniteGaloisSubextension

end Representation

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_FiniteAbelianSubextension
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.upperQuotient_groupInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite abelian extensions in abstract reciprocity

the finite abelian class-field classification classifies finite abelian extensions `L | K` by
their norm subgroups.  This file builds the extension side of that
correspondence independently of the reciprocity isomorphism:

* a finite Galois extension whose actual quotient is commutative;
* the field-inclusion order (opposite to inclusion of closed subgroups);
* compositum and intersection operations;
* the actual assignment `L ↦ N_{L/K} A_L` and its unconditional order
  relations.

The reverse inclusions in the two norm formulas, and hence the classification
bijection itself, require the abstract reciprocity theorem and are deliberately not postulated.
-/

noncomputable section

namespace ClassFormation

open CyclicCohomology KummerTheory

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A finite abelian extension `L | K`: a finite Galois extension together
with commutativity of its actual quotient `G_K/G_L`. -/
structure FiniteAbelianSubextension (K : ClosedSubgroup G) where
  /-- The underlying finite Galois subextension. -/
  toFiniteGaloisExtension : FiniteGaloisSubextension K
  /-- Commutativity of the relative Galois quotient. -/
  commutative : IsMulCommutative toFiniteGaloisExtension.extensionQuotient

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- Introduces the abbreviation `field`. -/
abbrev field (L : FiniteAbelianSubextension K) : ClosedSubgroup G :=
  L.toFiniteGaloisExtension.field

/-- Introduces the abbreviation `below`. -/
abbrev below (L : FiniteAbelianSubextension K) :
    L.field.toSubgroup ≤ K.toSubgroup :=
  L.toFiniteGaloisExtension.below

/-- Introduces the abbreviation `normal`. -/
abbrev normal (L : FiniteAbelianSubextension K) :
    (extensionSubgroup K L.field L.below).Normal :=
  L.toFiniteGaloisExtension.normal

/-- Introduces the abbreviation `finite`. -/
abbrev finite (L : FiniteAbelianSubextension K) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  L.toFiniteGaloisExtension.finite

/-- The finite abelian quotient carried by the extension.  Its representation
is inherited through the finite Galois extension boundary rather than exposed
as a transparent quotient abbreviation. -/
@[implicit_reducible]
def extensionQuotient (L : FiniteAbelianSubextension K) : Type u :=
  L.toFiniteGaloisExtension.extensionQuotient

/-- The quotient attached to a finite abelian subextension is a commutative group. -/
@[implicit_reducible]
instance extensionQuotient_commGroup (L : FiniteAbelianSubextension K) :
    CommGroup L.extensionQuotient := by
  unfold extensionQuotient
  letI : IsMulCommutative
      L.toFiniteGaloisExtension.extensionQuotient := L.commutative
  exact
    { (inferInstance :
        Group L.toFiniteGaloisExtension.extensionQuotient) with
      mul_comm := L.commutative.is_comm.comm }

/-- The quotient attached to a finite abelian subextension is finite. -/
instance extensionQuotient_finite (L : FiniteAbelianSubextension K) :
    Finite L.extensionQuotient := by
  unfold extensionQuotient
  infer_instance

/-- Comparison with the quotient presentation used by the underlying group
library. -/
def extensionQuotientMulEquiv (L : FiniteAbelianSubextension K) :
    L.extensionQuotient ≃*
      (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  L.toFiniteGaloisExtension.extensionQuotientMulEquiv

/-- The canonical quotient projection for a finite abelian extension. -/
def extensionQuotientMk (L : FiniteAbelianSubextension K) :
    K.toSubgroup →* L.extensionQuotient :=
  L.toFiniteGaloisExtension.extensionQuotientMk

/-- The named abelian quotient projection agrees with the underlying quotient map. -/
@[simp]
theorem extensionQuotientMk_apply (L : FiniteAbelianSubextension K)
    (k : K.toSubgroup) :
    L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k :
        K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  L.toFiniteGaloisExtension.extensionQuotientMk_apply k

/-- Two packages with the same closed subgroup represent the same finite
abelian extension. -/
@[ext]
theorem ext {L₁ L₂ : FiniteAbelianSubextension K}
    (h : L₁.field = L₂.field) : L₁ = L₂ := by
  cases L₁ with
  | mk L₁ h₁ =>
      cases L₂ with
      | mk L₂ h₂ =>
          cases L₁ with
          | mk F₁ b₁ n₁ f₁ =>
              cases L₂ with
              | mk F₂ b₂ n₂ f₂ =>
                  dsimp only [field] at h
                  cases h
                  rfl

/-- The order is field inclusion.  Since fields are represented by their
absolute Galois subgroups, it is the opposite subgroup order. -/
instance instPartialOrder : PartialOrder (FiniteAbelianSubextension K) where
  le L₁ L₂ := L₂.field.toSubgroup ≤ L₁.field.toSubgroup
  le_refl _ := le_rfl
  le_trans _ _ _ h₁₂ h₂₃ := h₂₃.trans h₁₂
  le_antisymm L₁ L₂ h₁₂ h₂₁ := by
    apply ext
    apply ClosedSubgroup.ext
    have hs : L₁.field.toSubgroup = L₂.field.toSubgroup :=
      le_antisymm h₂₁ h₁₂
    exact congrArg (fun H : Subgroup G => H.carrier) hs

/-- Base change of a finite abelian extension to an arbitrary
intermediate abstract field.  Contravariantly the new top subgroup is
the intersection with the new base subgroup. -/
def baseChange (M : FiniteAbelianSubextension K)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    FiniteAbelianSubextension L where
  toFiniteGaloisExtension :=
    M.toFiniteGaloisExtension.baseChange L hLK
  commutative := by
    let P :=
      M.toFiniteGaloisExtension.baseChange L hLK
    let :
        (extensionSubgroup K M.field M.below).Normal :=
      M.normal
    let :
        (extensionSubgroup L P.field P.below).Normal :=
      P.normal
    refine ⟨⟨?_⟩⟩
    intro x y
    refine P.extensionQuotient_inductionOn
      (motive := fun x => x * y = y * x) x ?_
    intro a
    refine P.extensionQuotient_inductionOn
      (motive := fun y =>
        P.extensionQuotientMk a * y =
          y * P.extensionQuotientMk a) y ?_
    intro b
    apply P.extensionQuotientMulEquiv.injective
    simp only [map_mul, P.extensionQuotientMk_apply]
    apply QuotientGroup.eq.mpr
    apply (mem_extensionSubgroup_iff L P.field P.below _).2
    constructor
    · exact ((a * b)⁻¹ * (b * a)).property
    · let aK : K.toSubgroup :=
        Subgroup.inclusion hLK a
      let bK : K.toSubgroup :=
        Subgroup.inclusion hLK b
      have hcomm :=
        M.commutative.is_comm.comm
          (M.extensionQuotientMk aK)
          (M.extensionQuotientMk bK)
      have hcommRaw :=
        congrArg M.extensionQuotientMulEquiv hcomm
      simp only [map_mul, M.extensionQuotientMk_apply] at hcommRaw
      exact
        (mem_extensionSubgroup_iff
          K M.field M.below _).1
          (QuotientGroup.eq.mp hcommRaw)

end FiniteAbelianSubextension

end GroupOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The norm subgroup assigned to a finite abelian extension,
`N_L = N_{L/K} A_L` in the finite abelian class-field classification. -/
def normSubgroup (A : Rep ℤ G) (L : FiniteAbelianSubextension K) :
    AddSubgroup (ambientFixedAddSubgroup A K) := by
  letI : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  exact finiteNormSubgroup A K L.field L.below


end FiniteAbelianSubextension

end Representation

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_IntermediateExtension
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
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
# Intermediate extensions from actual quotient subgroups

For the three reductions in the proof of the abstract reciprocity theorem, this file supplies the finite Galois correspondence in the
direction used by the construction.  If `L / K` is a packaged finite Galois extension
and `S ≤ G(L/K)`, its inverse image in `G_K` is realized as an actual closed
intermediate field `M`.

Closedness is proved from the explicit decomposition of the inverse image
as the finite union of right `G_L`-cosets.  The two Galois-group
identifications are then obtained from the actual restriction map and the
first and third isomorphism theorems; no correspondence certificate is
assumed.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The generally non-Galois finite extension `L^S/K` attached to an
arbitrary subgroup `S ≤ G(L/K)`.  Normality is deliberately absent from this
bundle; clients that only need finite-extension invariants should use this
rather than forcing `S` through `intermediateFiniteGalois`. -/
def intermediateFiniteAbstractExtension
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    DegreeData.FiniteAbstractExtension G where
  field := L.intermediateField S
  base := K
  below := L.intermediateField_le_base S
  finiteQuotient := L.intermediateField_finite S

/-- The subgroup attached to the intermediate extension is normal. -/
instance intermediateSubgroup_normalInstance
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    [hS : S.Normal] : (L.intermediateSubgroup S).Normal :=
  L.intermediateSubgroup_normal S hS

end FiniteGaloisSubextension

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_NormTopology
attribute [-instance] _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.upperQuotient_groupInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.FiniteGaloisSubextension.lowerQuotientEquiv_mk _root_.ClassFormation.FiniteGaloisSubextension.lowerQuotientEquiv_mk_coe _root_.ClassFormation.FiniteGaloisSubextension.lowerRestrictionHom_apply_coe _root_.ClassFormation.FiniteGaloisSubextension.mem_intermediateSubgroup_iff _root_.ClassFormation.FiniteGaloisSubextension.upperQuotientEquiv_mk_mk _root_.ClassFormation.FiniteGaloisSubextension.upperQuotientMk_apply _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Abstract reciprocity: the norm topology

The neighbourhood basis at zero consists literally of the norm subgroups
`N_{L/K} A_L` as `L / K` ranges over finite Galois extensions.  Composita
make this family downward directed.
-/

noncomputable section

namespace ClassFormation

open CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The actual norm subgroup belonging to a packaged finite Galois
extension. -/
def normSubgroup (A : Rep ℤ G) (L : FiniteGaloisSubextension K) :
    AddSubgroup (ambientFixedAddSubgroup A K) := by
  letI := L.finite
  exact finiteNormSubgroup A K L.field L.below

/-- Proves the bound `normSubgroup A (L₁.compositum L₂) ≤ normSubgroup A L₁`. -/
theorem normSubgroup_compositum_le_left
    (A : Rep ℤ G) (L₁ L₂ : FiniteGaloisSubextension K) :
    normSubgroup A (L₁.compositum L₂) ≤ normSubgroup A L₁ := by
  simpa [normSubgroup] using
    ClassFormation.FiniteGaloisSubextension.finiteNormSubgroup_compositum_le_left A L₁ L₂

/-- Proves the bound `normSubgroup A (L₁.compositum L₂) ≤ normSubgroup A L₂`. -/
theorem normSubgroup_compositum_le_right
    (A : Rep ℤ G) (L₁ L₂ : FiniteGaloisSubextension K) :
    normSubgroup A (L₁.compositum L₂) ≤ normSubgroup A L₂ := by
  simpa [normSubgroup] using
    ClassFormation.FiniteGaloisSubextension.finiteNormSubgroup_compositum_le_right A L₁ L₂

end FiniteGaloisSubextension

open FiniteGaloisSubextension

/-- The additive-group filter basis formed by all finite Galois norm
subgroups. -/
@[implicit_reducible]
def normFilterBasis (A : Rep ℤ G) (K : ClosedSubgroup G) :
    AddGroupFilterBasis (ambientFixedAddSubgroup A K) :=
  addGroupFilterBasisOfComm
    {U | ∃ L : FiniteGaloisSubextension K,
      U = (normSubgroup A L : Set (ambientFixedAddSubgroup A K))}
    (by
      refine ⟨(normSubgroup A (FiniteGaloisSubextension.refl K) :
        Set (ambientFixedAddSubgroup A K)), ?_⟩
      exact ⟨FiniteGaloisSubextension.refl K, rfl⟩)
    (by
      rintro U V ⟨L₁, rfl⟩ ⟨L₂, rfl⟩
      refine ⟨(normSubgroup A (L₁.compositum L₂) :
        Set (ambientFixedAddSubgroup A K)),
        ⟨L₁.compositum L₂, rfl⟩, ?_⟩
      intro x hx
      exact ⟨normSubgroup_compositum_le_left A L₁ L₂ hx,
        normSubgroup_compositum_le_right A L₁ L₂ hx⟩)
    (by
      rintro _ ⟨L, rfl⟩
      exact (normSubgroup A L).zero_mem)
    (by
      rintro _ ⟨L, rfl⟩
      refine ⟨(normSubgroup A L : Set (ambientFixedAddSubgroup A K)),
        ⟨L, rfl⟩, ?_⟩
      rintro x ⟨a, ha, b, hb, rfl⟩
      exact (normSubgroup A L).add_mem ha hb)
    (by
      rintro _ ⟨L, rfl⟩
      refine ⟨(normSubgroup A L : Set (ambientFixedAddSubgroup A K)),
        ⟨L, rfl⟩, ?_⟩
      intro x hx
      exact (normSubgroup A L).neg_mem hx)

/-- The norm topology: norm subgroups form a basis at zero. -/
@[implicit_reducible]
def normTopology (A : Rep ℤ G) (K : ClosedSubgroup G) :
    TopologicalSpace (ambientFixedAddSubgroup A K) :=
  (normFilterBasis A K).topology

/-- Openness in the norm topology, expressed through the type-level norm
topology model. -/
def IsNormOpen (A : Rep ℤ G) (K : ClosedSubgroup G)
    (s : Set (ambientFixedAddSubgroup A K)) : Prop :=
  @IsOpen (ambientFixedAddSubgroup A K) (normTopology A K) s

theorem isNormOpen_iff_raw
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    (s : Set (ambientFixedAddSubgroup A K)) :
    IsNormOpen A K s ↔
      @IsOpen (ambientFixedAddSubgroup A K) (normTopology A K) s := by
  rfl

/-- A set belongs to the defining filter basis exactly when it is one of
the finite Galois norm subgroups. -/
@[simp]
theorem mem_normFilterBasis_iff
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    (U : Set (ambientFixedAddSubgroup A K)) :
    U ∈ normFilterBasis A K ↔
      ∃ L : FiniteGaloisSubextension K,
        U = (normSubgroup A L : Set (ambientFixedAddSubgroup A K)) :=
  Iff.rfl

/-- A subgroup is open in the norm topology exactly when it contains one
finite Galois norm subgroup. -/
theorem normTopology_addSubgroup_isOpen_iff
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    (H : AddSubgroup (ambientFixedAddSubgroup A K)) :
    IsNormOpen A K H ↔
      ∃ L : FiniteGaloisSubextension K, normSubgroup A L ≤ H := by
  rw [isNormOpen_iff_raw]
  let : TopologicalSpace (ambientFixedAddSubgroup A K) := normTopology A K
  let : IsTopologicalAddGroup (ambientFixedAddSubgroup A K) :=
    (normFilterBasis A K).isTopologicalAddGroup
  constructor
  · intro hH
    have hnh : (H : Set (ambientFixedAddSubgroup A K)) ∈ nhds 0 :=
      hH.mem_nhds H.zero_mem
    rcases (normFilterBasis A K).nhds_zero_hasBasis.mem_iff.mp hnh with
      ⟨U, hU, hUH⟩
    rcases hU with ⟨L, rfl⟩
    exact ⟨L, hUH⟩
  · rintro ⟨L, hLH⟩
    apply H.isOpen_of_mem_nhds
    exact Filter.mem_of_superset
      ((normFilterBasis A K).mem_nhds_zero ⟨L, rfl⟩) hLH

/-- Every defining norm subgroup is open. -/
theorem normSubgroup_isOpen
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    (L : FiniteGaloisSubextension K) :
    IsNormOpen A K (normSubgroup A L) := by
  rw [normTopology_addSubgroup_isOpen_iff]
  exact ⟨L, le_rfl⟩

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_ClassFieldCandidate
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# A finite class-field candidate from a norm-open subgroup

This file isolates the source-producing part of finite-classification surjectivity.
An open subgroup `H ≤ A_K` contains an actual finite Galois
norm subgroup.  Modulo that norm subgroup, `H` gives a concrete subgroup.
Transporting this subgroup to the additive abelianization and pulling it
back along `Q → Qᵃᵇ` gives a subgroup of the actual finite Galois quotient
which contains its commutator.  The finite Galois correspondence then cuts
out an actual finite abelian intermediate extension.

The equivalence used for the transport is an explicit argument of the
construction. A later specialization supplies it from finite reciprocity for
the reciprocity map.  No existence statement, norm-kernel equality, or
classification conclusion depending on that specialization is
asserted here.
-/

noncomputable section

namespace ClassFormation

open CyclicCohomology KummerTheory
open scoped commutatorElement

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ## The finite level beneath an open norm-topology subgroup -/

omit [IsTopologicalGroup G] in
/-- The first step in the proof of the finite abelian classification theorem: an open subgroup in the
norm topology contains the norm subgroup of an actual finite Galois
extension. -/
theorem normOpenAddSubgroup_contains_finiteNormSubgroup
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hH : IsNormOpen A K H) :
    ∃ E : FiniteGaloisSubextension K, ClassFormation.FiniteGaloisSubextension.normSubgroup A E ≤ H :=
  (normTopology_addSubgroup_isOpen_iff A K H).1 hH

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

local instance normQuotient_extensionQuotient_finite
    (E : FiniteGaloisSubextension K) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K E.field E.below) :=
  E.finite

/-- The subgroup `H / N_E` of the actual norm quotient, represented as
the image of `H` under the quotient map. -/
def normQuotientSubgroup
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K)) :
    AddSubgroup (FiniteNormQuotient A K E.field E.below) := by
  letI : Finite (K.toSubgroup ⧸
      extensionSubgroup K E.field E.below) := E.finite
  exact H.map (finiteNormClassHom A K E.field E.below)

omit [IsTopologicalGroup G] in
/-- If `N_E ⊆ H`, then `H` is exactly the full inverse image of
`H / N_E`.  This is the group-theoretic fact used in the middle of the
finite-classification surjectivity proof. -/
theorem finiteNormClass_mem_normQuotientSubgroup_iff
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hEH : ClassFormation.FiniteGaloisSubextension.normSubgroup A E ≤ H)
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K E.field E.below) := E.finite
    finiteNormClass A K E.field E.below a ∈
        normQuotientSubgroup A E H ↔
      a ∈ H := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K E.field E.below) := E.finite
  constructor
  · rintro ⟨b, hb, hba⟩
    have hba' : finiteNormClass A K E.field E.below b =
        finiteNormClass A K E.field E.below a := by
      simpa [finiteNormClass] using hba
    have hzero : finiteNormClass A K E.field E.below (b - a) = 0 := by
      rw [finiteNormClass_sub, hba', sub_self]
    have hsub : b - a ∈ ClassFormation.FiniteGaloisSubextension.normSubgroup A E :=
      (finiteNormClass_eq_zero_iff A K E.field E.below (b - a)).1 hzero
    have hsubH : b - a ∈ H := hEH hsub
    have ha : a = b - (b - a) := by abel
    rw [ha]
    exact H.sub_mem hb hsubH
  · intro ha
    exact ⟨a, ha, rfl⟩

/-! ## Transport to the abelianized finite quotient -/

/-- Transport `H / N_E` through a specified finite reciprocity
equivalence and forget additive notation.  This is a genuine subgroup of
the actual abelianization `G(E/K)ᵃᵇ`.

The argument `rE` is kept explicit: this definition does not construct the
finite reciprocity equivalence. -/
def reciprocityAbelianizedSubgroup
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    Subgroup (Abelianization E.extensionQuotient) := by
  letI : Finite (K.toSubgroup ⧸
      extensionSubgroup K E.field E.below) := E.finite
  exact AddSubgroup.toSubgroup'
    ((normQuotientSubgroup A E H).map rE.toAddMonoidHom)

/-- The representative-level abelianized class map obtained by first
passing to `A_K / N_E` and then applying the specified equivalence. -/
def reciprocityAbelianizedClassHom
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    ambientFixedAddSubgroup A K →+
      Additive (Abelianization E.extensionQuotient) :=
  rE.toAddMonoidHom.comp (finiteNormClassHom A K E.field E.below)

omit [IsTopologicalGroup G] in
/-- If `N_E ⊆ H`, the transported subgroup has exactly `H` as its
inverse image under the abelianized class map.  This is the precise
full-preimage statement used before taking the fixed field in the finite classification argument. -/
theorem reciprocityClass_mem_abelianizedSubgroup_iff
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hEH : ClassFormation.FiniteGaloisSubextension.normSubgroup A E ≤ H)
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (a : ambientFixedAddSubgroup A K) :
    Additive.toMul (reciprocityAbelianizedClassHom A E rE a) ∈
        reciprocityAbelianizedSubgroup A E H rE ↔
      a ∈ H := by
  change rE (finiteNormClass A K E.field E.below a) ∈
      (normQuotientSubgroup A E H).map rE.toAddMonoidHom ↔
    a ∈ H
  constructor
  · rintro ⟨z, hz, hza⟩
    have hzEq : z = finiteNormClass A K E.field E.below a :=
      rE.injective hza
    rw [hzEq] at hz
    exact (finiteNormClass_mem_normQuotientSubgroup_iff A E H hEH a).1 hz
  · intro ha
    refine ⟨finiteNormClass A K E.field E.below a, ?_, rfl⟩
    exact (finiteNormClass_mem_normQuotientSubgroup_iff A E H hEH a).2 ha

end FiniteGaloisSubextension

/-! ## From a subgroup above the commutator to an abelian field -/

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

local instance candidate_extensionQuotient_finite
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : ClosedSubgroup G} (E : FiniteGaloisSubextension K) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K E.field E.below) :=
  E.finite

/-- The actual finite abelian intermediate extension cut out by a subgroup
`S ≤ G(E/K)` containing the commutator. -/
def intermediateFiniteAbelianOfCommutatorLe
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : ClosedSubgroup G}
    (E : FiniteGaloisSubextension K)
    (S : Subgroup E.extensionQuotient)
    (hS : commutator E.extensionQuotient ≤ S) :
    FiniteAbelianSubextension K := by
  let hnormal : S.Normal :=
    Subgroup.Normal.of_commutator_le E.extensionQuotient hS
  letI : S.Normal := hnormal
  let M := E.intermediateFiniteGalois S hnormal
  refine
    { toFiniteGaloisExtension := M
      commutative := ?_ }
  let e := E.upperQuotientEquiv S
  let : IsMulCommutative (E.extensionQuotient ⧸ S) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hS
  refine ⟨⟨?_⟩⟩
  intro x y
  obtain ⟨x', rfl⟩ := e.surjective x
  obtain ⟨y', rfl⟩ := e.surjective y
  calc
    e x' * e y' = e (x' * y') := (map_mul e x' y').symm
    _ = e (y' * x') := congrArg e
      (Std.Commutative.comm
        (op := fun a b : E.extensionQuotient ⧸ S => a * b) x' y')
    _ = e y' * e x' := map_mul e y' x'

/-- The field underlying the preceding package is the literal fixed field
of `S`. -/
@[simp]
theorem intermediateFiniteAbelianOfCommutatorLe_field
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : ClosedSubgroup G}
    (E : FiniteGaloisSubextension K)
    (S : Subgroup E.extensionQuotient)
    (hS : commutator E.extensionQuotient ≤ S) :
    (intermediateFiniteAbelianOfCommutatorLe E S hS).field =
      E.intermediateField S :=
  rfl

/-- The subgroup obtained from `H / N_E` on the abelianization side,
pulled back to the actual finite Galois quotient. -/
def reciprocityPreimageSubgroup
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    Subgroup E.extensionQuotient :=
  abelianizationPreimageSubgroup
    (reciprocityAbelianizedSubgroup A E H rE)

omit [IsTopologicalGroup G] in
/-- The actual subgroup used to define the intermediate field contains
the commutator, independently of any kernel assertion for `rE`. -/
theorem commutator_le_reciprocityPreimageSubgroup
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    commutator E.extensionQuotient ≤
      reciprocityPreimageSubgroup A E H rE :=
  commutator_le_abelianizationPreimageSubgroup _

omit [IsTopologicalGroup G] in
/-- The pulled-back subgroup has exactly `H` as the inverse image of the
representative-level reciprocity class.  This is the group-side form of the
full-preimage assertion used in the finite-classification surjectivity proof. -/
theorem reciprocityClass_mem_preimageSubgroup_iff
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hEH : ClassFormation.FiniteGaloisSubextension.normSubgroup A E ≤ H)
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (a : ambientFixedAddSubgroup A K) :
    Quotient.out (Additive.toMul
        (reciprocityAbelianizedClassHom A E rE a)) ∈
        reciprocityPreimageSubgroup A E H rE ↔
      a ∈ H := by
  change Abelianization.of (Quotient.out (Additive.toMul
      (reciprocityAbelianizedClassHom A E rE a))) ∈
        reciprocityAbelianizedSubgroup A E H rE ↔ a ∈ H
  rw [show Abelianization.of (Quotient.out (Additive.toMul
      (reciprocityAbelianizedClassHom A E rE a))) =
        Additive.toMul (reciprocityAbelianizedClassHom A E rE a) by
      exact Quotient.out_eq' _]
  exact reciprocityClass_mem_abelianizedSubgroup_iff A E H hEH rE a

/-- The finite abelian intermediate extension determined by the subgroup
transported from `H / N_E`.  This is the field candidate in the
surjectivity proof of the finite abelian classification theorem.  No claim that its norm subgroup equals
`H` is made before finite reciprocity is available. -/
def classFieldCandidate
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    FiniteAbelianSubextension K :=
  intermediateFiniteAbelianOfCommutatorLe E
    (reciprocityPreimageSubgroup A E H rE)
    (commutator_le_reciprocityPreimageSubgroup A E H rE)

/-- The candidate is cut out by the explicit pulled-back subgroup, not by
an opaque correspondence object. -/
@[simp]
theorem classFieldCandidate_field
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    (classFieldCandidate A E H rE).field =
      E.intermediateField
        (reciprocityPreimageSubgroup A E H rE) :=
  by
    exact intermediateFiniteAbelianOfCommutatorLe_field E
      (reciprocityPreimageSubgroup A E H rE)
      (commutator_le_reciprocityPreimageSubgroup A E H rE)

end FiniteGaloisSubextension

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_FieldRepresentation
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.infiniteNormQuotientAddCommGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
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
# Actual coefficient representation for an abstract extension

This file identifies the invariant carrier used by
`extensionFixedRepresentation A K L` with the actual fixed group
`A_L`, and compares the representation norm with `N_{L/K}`.
-/

noncomputable section

open scoped BigOperators

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The norm in the descended representation is the actual relative norm
on the underlying fixed coefficient. -/
theorem extensionFixedRepresentation_norm_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) :
    letI := hnormal
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    ((extensionFixedRepresentation A K L hLK hnormal).norm.hom a).1 =
      ((relativeNorm A K L hLK
        (extensionFixedRepresentationEquiv A K L hLK hnormal a) :
          ambientFixedAddSubgroup A K) : A.V) := by
  let := hnormal
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  rw [relativeNorm_apply_coe]
  simp only [Rep.norm, Representation.norm, relativeNormValue]
  let M := extensionFixedRepresentation A K L hLK hnormal
  let : Module ℤ M.V := M.hV2
  change ((∑ q, M.ρ q) a).1 =
    ∑ q, relativeCosetAction A K L hLK
      (extensionFixedRepresentationEquiv A K L hLK hnormal a) q
  rw [LinearMap.sum_apply]
  let coeToAmbient :
      (extensionFixedRepresentation A K L hLK hnormal).V →+ A.V :=
    { toFun := fun x => x.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change coeToAmbient (∑ q, M.ρ q a) =
    ∑ q, relativeCosetAction A K L hLK
      (extensionFixedRepresentationEquiv A K L hLK hnormal a) q
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact extensionFixedRepresentation_action_coe A K L hLK hnormal q a

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_CyclicNormQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.conjugateExtension_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.mem_normFilterBasis_iff _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
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
# Cyclic norm quotients as degree-zero Tate cohomology

For a finite cyclic abstract extension `L / K`, this file identifies the
actual quotient `A_K / N_{L/K} A_L` with the degree-zero Tate homology
object used in the class-field axiom.  This is the source comparison needed before the
cardinality assertion of the class field axiom can be applied to the
reciprocity map.
-/

noncomputable section

open CategoryTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The actual fixed group `A_K` is the kernel of `ρ(g)-1` on `A_L`
when `g` generates `G(L/K)`. -/
def cyclicFixedCycleEquiv
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    ambientFixedAddSubgroup A K ≃+
      T.moduleCatLeftHomologyData.K := by
  dsimp only
  letI := hnormal
  letI := hfinite
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  letI : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  letI : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A K L hLK hnormal
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  let toCycle : ambientFixedAddSubgroup A K →
      T.moduleCatLeftHomologyData.K := fun a => by
    let aL := fixedFieldInclusion A K L hLK a
    let aM : M.V :=
      (extensionFixedRepresentationEquiv A K L hLK hnormal).symm aL
    refine ⟨aM, sub_eq_zero.mpr ?_⟩
    refine Quotient.inductionOn' g ?_
    intro k
    apply Subtype.ext
    change A.ρ k.1 a.1 = a.1
    exact a.2 k
  let fromCycle : T.moduleCatLeftHomologyData.K →
      ambientFixedAddSubgroup A K := fun x => by
    let aM : M.V := x.1
    let aL : ambientFixedAddSubgroup A L :=
      extensionFixedRepresentationEquiv A K L hLK hnormal aM
    have hxzero : T.g.hom aM = 0 := x.2
    have hxg : M.ρ g aM = aM := by
      apply sub_eq_zero.mp
      exact hxzero
    have hxall : ∀ q, M.ρ q aM = aM := by
      let : Module ℤ M := M.hV2
      exact (Representation.mem_invariants_iff_of_forall_mem_zpowers
        M.ρ g hg aM).2 hxg
    refine ⟨aL.1, ?_⟩
    intro k
    have hk := hxall
      ((QuotientGroup.mk' (extensionSubgroup K L hLK)) k)
    have haction := extensionFixedRepresentation_action_coe
      A K L hLK hnormal
      ((QuotientGroup.mk' (extensionSubgroup K L hLK)) k) aM
    have haction' :
        (M.ρ ((QuotientGroup.mk'
          (extensionSubgroup K L hLK)) k) aM).1 =
          A.ρ k.1 aL.1 := by
      calc
        _ = relativeCosetAction A K L hLK aL
              ((QuotientGroup.mk'
                (extensionSubgroup K L hLK)) k) := haction
        _ = A.ρ k.1 aL.1 :=
          relativeCosetAction_mk A K L hLK aL k
    exact haction'.symm.trans ((congrArg Subtype.val hk).trans rfl)
  exact
    { toFun := toCycle
      invFun := fromCycle
      left_inv := by
        intro a
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl
      map_add' := by
        intro a b
        apply Subtype.ext
        apply Subtype.ext
        rfl }

/-- The canonical map from `A_K` to the concrete kernel/range quotient
computing degree-zero Tate cohomology. -/
def cyclicNormClassHom
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    ambientFixedAddSubgroup A K →+
      T.moduleCatLeftHomologyData.H := by
  dsimp only
  letI := hnormal
  letI := hfinite
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  letI : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  letI : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A K L hLK hnormal
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  let e := cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg
  exact
    { toFun := fun a => T.moduleCatLeftHomologyData.π (e a)
      map_zero' := by simp
      map_add' := by
        intro a b
        simp }

/--
The cyclic norm-class map evaluates by applying the fixed-cycle equivalence and projecting to
cyclic homology.
-/
@[simp]
theorem cyclicNormClassHom_apply
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (a : ambientFixedAddSubgroup A K) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    cyclicNormClassHom A K L hLK hnormal hfinite g hg a =
      T.moduleCatLeftHomologyData.π
        (cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg a) := by
  rfl

/-- Under the fixed-cycle equivalence, the actual relative norm is the
first differential in the cyclic Tate complex. -/
theorem cyclicFixedCycleEquiv_relativeNorm
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (a : ambientFixedAddSubgroup A L) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg
        (relativeNorm A K L hLK a) =
      T.moduleCatToCycles
        ((extensionFixedRepresentationEquiv A K L hLK hnormal).symm a) := by
  dsimp only
  let := hnormal
  let := hfinite
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  let : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A K L hLK hnormal
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  apply Subtype.ext
  apply Subtype.ext
  exact (extensionFixedRepresentation_norm_coe
    A K L hLK hnormal
      ((extensionFixedRepresentationEquiv A K L hLK hnormal).symm a)).symm

/-- The kernel of the concrete Tate-class map is exactly the actual norm
subgroup `N_{L/K} A_L`. -/
theorem cyclicNormClassHom_ker
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    (cyclicNormClassHom A K L hLK hnormal hfinite g hg).ker =
      finiteNormSubgroup A K L hLK := by
  let := hnormal
  let := hfinite
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  let : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A K L hLK hnormal
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  let : Module ℤ T.X₁ := T.X₁.isModule
  let : Module ℤ (LinearMap.ker T.g.hom) :=
    (LinearMap.ker T.g.hom).module
  let e := cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg
  ext a
  constructor
  · intro ha
    change cyclicNormClassHom A K L hLK hnormal hfinite g hg a = 0 at ha
    rw [cyclicNormClassHom_apply] at ha
    let ea : T.moduleCatLeftHomologyData.K := e a
    have ha' :
        Submodule.mkQ (LinearMap.range T.moduleCatToCycles) ea = 0 := by
      exact ha
    have harange : ea ∈ LinearMap.range T.moduleCatToCycles :=
      (Submodule.Quotient.mk_eq_zero _).1 ha'
    obtain ⟨y, hy⟩ := harange
    change a ∈ (relativeNorm A K L hLK).range
    let b : ambientFixedAddSubgroup A L :=
      extensionFixedRepresentationEquiv A K L hLK hnormal y
    refine ⟨b, ?_⟩
    apply Subtype.ext
    calc
      (relativeNorm A K L hLK b).1 = (M.norm.hom y).1 :=
        (extensionFixedRepresentation_norm_coe
          A K L hLK hnormal y).symm
      _ = ea.1.1 :=
        congrArg Subtype.val (congrArg Subtype.val hy)
      _ = a.1 := rfl
  · intro ha
    change a ∈ (relativeNorm A K L hLK).range at ha
    obtain ⟨b, rfl⟩ := ha
    change cyclicNormClassHom A K L hLK hnormal hfinite g hg
      (relativeNorm A K L hLK b) = 0
    rw [cyclicNormClassHom_apply]
    let eb : T.moduleCatLeftHomologyData.K :=
      e (relativeNorm A K L hLK b)
    change Submodule.mkQ (LinearMap.range T.moduleCatToCycles)
      eb = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    refine ⟨(extensionFixedRepresentationEquiv
      A K L hLK hnormal).symm b, ?_⟩
    exact (cyclicFixedCycleEquiv_relativeNorm
      A K L hLK hnormal hfinite g hg b).symm

/-- Every concrete Tate class has a representative in the actual fixed
group `A_K`. -/
theorem cyclicNormClassHom_surjective
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    Function.Surjective
      (cyclicNormClassHom A K L hLK hnormal hfinite g hg) := by
  let := hnormal
  let := hfinite
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  let : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A K L hLK hnormal
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  let e := cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg
  have hπ : Function.Surjective T.moduleCatLeftHomologyData.π :=
    (ModuleCat.epi_iff_surjective
      T.moduleCatLeftHomologyData.π).1 inferInstance
  intro z
  obtain ⟨x, hx⟩ := hπ z
  refine ⟨e.symm x, ?_⟩
  rw [cyclicNormClassHom_apply, e.apply_symm_apply]
  exact hx

/-- The actual finite norm quotient is the concrete kernel/range quotient
which computes degree-zero Tate cohomology. -/
def cyclicFiniteNormQuotientEquivConcrete
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    FiniteNormQuotient A K L hLK ≃+
      T.moduleCatLeftHomologyData.H := by
  dsimp only
  letI := hnormal
  letI := hfinite
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  letI : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  letI : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let f := cyclicNormClassHom A K L hLK hnormal hfinite g hg
  exact
    (finiteNormQuotientConcreteEquiv A K L hLK).trans
      ((QuotientAddGroup.quotientAddEquivOfEq
        (cyclicNormClassHom_ker A K L hLK hnormal hfinite g hg).symm).trans
        (QuotientAddGroup.quotientKerEquivOfSurjective f
          (cyclicNormClassHom_surjective
            A K L hLK hnormal hfinite g hg)))

/-- The concrete kernel/range quotient is the homology object used in the
definition of `tateHZero`. -/
def cyclicConcreteEquivTateHZero
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    T.moduleCatLeftHomologyData.H ≃+ tateCohomology M 0 := by
  dsimp only
  letI := hnormal
  letI := hfinite
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  letI : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  letI : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A K L hLK hnormal
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  exact
    (T.moduleCatHomologyIso.symm ≪≫
      (TateCohomology.isoFiniteCyclicZero M g hg).symm).toLinearEquiv.toAddEquiv

/-- Canonical identification of the actual norm quotient with
degree-zero Tate cohomology for a finite cyclic extension. -/
def cyclicFiniteNormQuotientEquivTateHZero
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    let M := extensionFixedRepresentation A K L hLK hnormal
    FiniteNormQuotient A K L hLK ≃+ tateCohomology M 0 := by
  dsimp only
  letI := hnormal
  letI := hfinite
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  exact
    (cyclicFiniteNormQuotientEquivConcrete
      A K L hLK hnormal hfinite g hg).trans
      (cyclicConcreteEquivTateHZero
        A K L hLK hnormal hfinite g hg)

/-- The class-field axiom first gives genuine finiteness of the actual norm
quotient, transported from finite degree-zero Tate cohomology. -/
theorem finiteNormQuotientFiniteOfClassFieldAxiom
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [hKfinite : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Finite (FiniteNormQuotient A E.base E.field E.below) := by
  let := hnormal
  let := E.finiteQuotient
  let := Fintype.ofFinite
    (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below)
  let M := extensionFixedRepresentation A E.base E.field E.below hnormal
  let Kcf : FiniteAbstractField G := ⟨E.base, hKfinite⟩
  let Ecf : FiniteCyclicSubextension Kcf :=
    { field := E.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }
  let : Finite (tateCohomology (Ecf.fixedRepresentation A) 0) :=
    (hcf Kcf Ecf).finiteTateHZero
  exact Finite.of_equiv (tateCohomology (Ecf.fixedRepresentation A) 0) (by
    simpa [Kcf, Ecf, FiniteCyclicSubextension.fixedRepresentation] using
        (cyclicFiniteNormQuotientEquivTateHZero
          A E.base E.field E.below hnormal E.finiteQuotient g hg).symm.toEquiv)

/-- The class-field axiom gives the exact order of the actual norm quotient in the
cyclic case. -/
theorem finiteNormQuotient_card_of_classFieldAxiom
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [hKfinite : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card (FiniteNormQuotient A E.base E.field E.below) =
      (E.degree : ℕ) := by
  let := hnormal
  let := E.finiteQuotient
  let := Fintype.ofFinite
    (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below)
  let M := extensionFixedRepresentation A E.base E.field E.below hnormal
  let Kcf : FiniteAbstractField G := ⟨E.base, hKfinite⟩
  let Ecf : FiniteCyclicSubextension Kcf :=
    { field := E.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }
  let : Finite (tateCohomology (Ecf.fixedRepresentation A) 0) :=
    (hcf Kcf Ecf).finiteTateHZero
  let : Finite (tateCohomology M 0) := by
    simpa [M, Kcf, Ecf,
      FiniteCyclicSubextension.fixedRepresentation] using
        (inferInstance :
          Finite (tateCohomology (Ecf.fixedRepresentation A) 0))
  let : Finite (FiniteNormQuotient A E.base E.field E.below) :=
    finiteNormQuotientFiniteOfClassFieldAxiom A hcf E hnormal g hg
  calc
    Nat.card (FiniteNormQuotient A E.base E.field E.below) =
        Nat.card (tateCohomology M 0) :=
      Nat.card_congr
        (cyclicFiniteNormQuotientEquivTateHZero
          A E.base E.field E.below hnormal E.finiteQuotient g hg).toEquiv
    _ = (E.degree : ℕ) :=
      by
        simpa [Kcf, Ecf,
          FiniteCyclicSubextension.fixedRepresentation,
          FiniteCyclicSubextension.toFiniteAbstractExtension] using
            hcf.tateHZero_card Kcf Ecf

/-- The additive Galois quotient has the extension degree as its order. -/
theorem additiveExtensionQuotient_card
    (E : DegreeData.FiniteAbstractExtension G) :
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below)) =
      (E.degree : ℕ) := by
  calc
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below)) =
        Nat.card
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below) :=
      (Nat.card_congr
        (Additive.ofMul :
          (E.base.toSubgroup ⧸
              extensionSubgroup E.base E.field E.below) ≃
            Additive
              (E.base.toSubgroup ⧸
                extensionSubgroup E.base E.field E.below))).symm
    _ = (extensionSubgroup E.base E.field E.below).index :=
      (Subgroup.index_eq_card
        (extensionSubgroup E.base E.field E.below)).symm
    _ = (E.degree : ℕ) := E.extensionSubgroup_index_eq_degree

/-- Under the class-field axiom, the cyclic Galois quotient and its actual norm
quotient have the same finite order. -/
theorem cyclicReciprocity_card_equality
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below)) =
      Nat.card (FiniteNormQuotient A E.base E.field E.below) := by
  rw [additiveExtensionQuotient_card E,
    finiteNormQuotient_card_of_classFieldAxiom
      A hcf E hnormal g hg]

/-- The cyclic norm quotient is finite as an actual type under the class-field axiom. -/
theorem finiteNormQuotient_finite_of_classFieldAxiom
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Finite (FiniteNormQuotient A E.base E.field E.below) :=
  finiteNormQuotientFiniteOfClassFieldAxiom A hcf E hnormal g hg

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_Basic
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.inducedFixedEquiv_apply_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace CyclicCohomology

/-!
# Low-degree Herbrand quotients

This reusable implementation supplies the low-degree cyclic cohomology used
by the class-formation and local class field theory layers.
-/

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA uB uC

variable {G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]

omit [Fintype G] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- A `σ`-coboundary equal to `1` makes every element of the cyclic subgroup
generated by `σ` fix the point. -/
theorem smul_eq_of_mem_zpowers_of_sigmaMinusOne_eq_one
    {σ g : G} {a : A} (hg : g ∈ Subgroup.zpowers σ)
    (hσ : sigmaMinusOne G A σ a = 1) :
    g • a = a := by
  have hσa : σ • a = a := by
    exact mul_inv_eq_one.mp (by simpa [sigmaMinusOne] using hσ)
  exact smul_eq_self_of_mem_zpowers hg hσa

omit [Fintype G] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- If `σ` generates `G`, then a trivial `σ`-coboundary is genuinely fixed by
all of `G`. -/
theorem fixed_of_forall_mem_zpowers_of_sigmaMinusOne_eq_one
    {σ : G} {a : A} (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hσ : sigmaMinusOne G A σ a = 1) :
    ∀ g : G, g • a = a := by
  intro g
  exact smul_eq_of_mem_zpowers_of_sigmaMinusOne_eq_one
    (G := G) (A := A) (g := g) (hg := hgen g) hσ

/-- An equivariant homomorphism commutes with the Tate norm. -/
theorem map_tateNorm (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (a : A) :
    f (tateNorm G A a) = tateNorm G B (f a) := by
  simp only [tateNorm, map_prod]
  exact Finset.prod_congr rfl (fun g _hg => hf g a)

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The Tate norm of an inverse is the inverse Tate norm. -/
theorem tateNorm_inv (a : A) : tateNorm G A a⁻¹ = (tateNorm G A a)⁻¹ :=
  map_inv (tateNormHom (G := G) (A := A)) a

omit [Fintype G] [CommGroup C] [MulDistribMulAction G C] in
/-- An equivariant homomorphism commutes with the sigma-minus-one operator. -/
theorem map_sigmaMinusOne (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (σ : G) (a : A) :
    f (sigmaMinusOne G A σ a) = sigmaMinusOne G B σ (f a) := by
  simp [sigmaMinusOne, hf σ a]

omit [Fintype G] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- If `σ` generates `G`, the kernel of `a ↦ a^(σ-1)` is the fixed subgroup. -/
theorem sigmaMinusOneHom_ker_eq_fixedSubgroup
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    MonoidHom.ker (sigmaMinusOneHom (G := G) (A := A) σ) = fixedSubgroup G A := by
  ext a
  constructor
  · intro ha
    exact fixed_of_forall_mem_zpowers_of_sigmaMinusOne_eq_one
      (G := G) (A := A) (σ := σ) hgen (by simpa using ha)
  · intro ha
    change sigmaMinusOne G A σ a = 1
    simp [sigmaMinusOne, ha σ]

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Finite-module source: the norm homomorphism factors the cardinality of
`A` into norm-kernel and norm-image cardinalities. -/
theorem card_eq_card_normKernelSubgroup_mul_card_tateNormSubgroup [Finite A] :
    Nat.card A = Nat.card (normKernelSubgroup G A) * Nat.card (tateNormSubgroup G A) := by
  simpa [normKernelSubgroup, tateNormSubgroup] using
    monoidHom_card_eq_card_ker_mul_card_range (tateNormHom (G := G) (A := A))

omit [Fintype G] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Finite-module source: for a cyclic generator `σ`, the coboundary
homomorphism factors the cardinality of `A` into fixed and augmentation
cardinalities. -/
theorem card_eq_card_fixedSubgroup_mul_card_augmentationSubgroup
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    Nat.card A = Nat.card (fixedSubgroup G A) * Nat.card (augmentationSubgroup G A σ) := by
  simpa [sigmaMinusOneHom_ker_eq_fixedSubgroup (G := G) (A := A) σ hgen,
    augmentationSubgroup] using
    monoidHom_card_eq_card_ker_mul_card_range
      (sigmaMinusOneHom (G := G) (A := A) σ)

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Finite-module cardinality balance behind `h(G,A)=1`: for a finite cyclic
group action, the product `#A^G · #I_G A` equals `#ker N_G · #N_G A`. -/
theorem herbrand_finite_module_cardinality_balance
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    Nat.card (fixedSubgroup G A) * Nat.card (augmentationSubgroup G A σ) =
      Nat.card (normKernelSubgroup G A) * Nat.card (tateNormSubgroup G A) := by
  rw [← card_eq_card_fixedSubgroup_mul_card_augmentationSubgroup
      (G := G) (A := A) σ hgen,
    ← card_eq_card_normKernelSubgroup_mul_card_tateNormSubgroup (G := G) (A := A)]

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Every degree-zero Herbrand class has a fixed-point representative. -/
theorem HerbrandH0.mk_surjective :
    Function.Surjective (HerbrandH0.mk (G := G) (A := A)) := by
  intro q
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    ((tateNormSubgroup G A).subgroupOf (fixedSubgroup G A))
    (HerbrandH0.equiv (G := G) (A := A) q)
  refine ⟨a, (HerbrandH0.equiv (G := G) (A := A)).injective ?_⟩
  rw [HerbrandH0.equiv_mk]
  exact ha

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Every degree-minus-one Herbrand class has a norm-kernel representative. -/
theorem HerbrandHMinusOne.mk_surjective (σ : G) :
    Function.Surjective (HerbrandHMinusOne.mk (G := G) (A := A) σ) := by
  intro q
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    ((augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A))
    (HerbrandHMinusOne.equiv (G := G) (A := A) σ q)
  refine ⟨a, (HerbrandHMinusOne.equiv (G := G) (A := A) σ).injective ?_⟩
  rw [HerbrandHMinusOne.equiv_mk]
  exact ha

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- A norm-kernel representative gives the trivial degree-minus-one class
exactly when it is an augmentation. -/
@[simp]
theorem HerbrandHMinusOne.mk_eq_one_iff (σ : G)
    (a : normKernelSubgroup G A) :
    HerbrandHMinusOne.mk σ a = 1 ↔
      (a : A) ∈ augmentationSubgroup G A σ := by
  constructor
  · intro h
    have hraw :
        (QuotientGroup.mk a :
          normKernelSubgroup G A ⧸
            (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)) = 1 := by
      simpa only [HerbrandHMinusOne.equiv_mk, map_one] using
        congrArg (HerbrandHMinusOne.equiv (G := G) (A := A) σ) h
    simpa only [Subgroup.mem_subgroupOf] using
      (QuotientGroup.eq_one_iff a).1 hraw
  · intro h
    apply (HerbrandHMinusOne.equiv (G := G) (A := A) σ).injective
    rw [HerbrandHMinusOne.equiv_mk, map_one]
    apply (QuotientGroup.eq_one_iff a).2
    simpa only [Subgroup.mem_subgroupOf] using h

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Eliminate a degree-zero Herbrand class through an arbitrary fixed-point
representative and the canonical class map. -/
protected theorem HerbrandH0.inductionOn
    {motive : HerbrandH0 G A → Prop} (q : HerbrandH0 G A)
    (h : ∀ a : fixedSubgroup G A, motive (HerbrandH0.mk a)) : motive q := by
  obtain ⟨a, rfl⟩ := HerbrandH0.mk_surjective (G := G) (A := A) q
  exact h a

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Eliminate a degree-minus-one Herbrand class through an arbitrary
norm-kernel representative and the canonical class map. -/
protected theorem HerbrandHMinusOne.inductionOn (σ : G)
    {motive : HerbrandHMinusOne G A σ → Prop}
    (q : HerbrandHMinusOne G A σ)
    (h : ∀ a : normKernelSubgroup G A,
      motive (HerbrandHMinusOne.mk σ a)) : motive q := by
  obtain ⟨a, rfl⟩ :=
    HerbrandHMinusOne.mk_surjective (G := G) (A := A) σ q
  exact h a

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Descend a homomorphism on the norm kernel through `H⁻¹(G,A)`. -/
def HerbrandHMinusOne.lift {M : Type*} [Group M] (σ : G)
    (f : normKernelSubgroup G A →* M)
    (h : (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A) ≤
      f.ker) : HerbrandHMinusOne G A σ →* M := by
  unfold HerbrandHMinusOne
  exact QuotientGroup.lift
    ((augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)) f h

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- A homomorphism descended through degree-minus-one Herbrand cohomology agrees
on representatives. -/
@[simp]
theorem HerbrandHMinusOne.lift_mk {M : Type*} [Group M] (σ : G)
    (f : normKernelSubgroup G A →* M)
    (h : (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A) ≤
      f.ker) (a : normKernelSubgroup G A) :
    HerbrandHMinusOne.lift σ f h (HerbrandHMinusOne.mk σ a) = f a := by
  rfl

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Degree-zero Herbrand cohomology is finite when the coefficient group is finite. -/
noncomputable instance herbrandH0FiniteOfFinite [Finite A] :
    Finite (HerbrandH0 G A) := by
  exact Finite.of_equiv
    (fixedSubgroup G A ⧸
      (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A))
    (HerbrandH0.equiv (G := G) (A := A)).symm.toEquiv

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Degree-minus-one Herbrand cohomology is finite when the coefficient group is finite. -/
noncomputable instance herbrandHMinusOneFiniteOfFinite (σ : G) [Finite A] :
    Finite (HerbrandHMinusOne G A σ) := by
  exact Finite.of_equiv
    (normKernelSubgroup G A ⧸
      (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A))
    (HerbrandHMinusOne.equiv (G := G) (A := A) σ).symm.toEquiv

omit [Fintype G] [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- Fixed subgroup of the right-regular multiplicative induced module. -/
abbrev rightRegularFunctionFixedSubgroup : Subgroup (G → B) := by
  letI := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  exact fixedSubgroup G (G → B)

omit [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- Norm image subgroup of the right-regular multiplicative induced module. -/
abbrev rightRegularFunctionTateNormSubgroup : Subgroup (G → B) := by
  letI := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  exact tateNormSubgroup G (G → B)

omit [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- Norm-kernel subgroup of the right-regular multiplicative induced module. -/
abbrev rightRegularFunctionNormKernelSubgroup : Subgroup (G → B) := by
  letI := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  exact normKernelSubgroup G (G → B)

omit [Fintype G] [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- Augmentation subgroup of the right-regular multiplicative induced module. -/
abbrev rightRegularFunctionAugmentationSubgroup (σ : G) : Subgroup (G → B) := by
  letI := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  exact augmentationSubgroup G (G → B) σ

/-- The norm of a multiplicative coboundary is trivial. This is the calculation
`N_G(b^(σ-1)) = 1` used in the low-degree cyclic-cohomology exact sequence. -/
theorem tateNorm_sigmaMinusOne_eq_one (σ : G) (a : A) :
    tateNorm G A (sigmaMinusOne G A σ a) = 1 := by
  have hshift : (∏ g : G, (g * σ) • a) = ∏ g : G, g • a := by
    exact Fintype.prod_equiv (Equiv.mulRight σ)
      (fun g : G => (g * σ) • a) (fun g : G => g • a) (by intro g; rfl)
  calc
    tateNorm G A (sigmaMinusOne G A σ a) = ∏ g : G, ((g * σ) • a) * (g • a)⁻¹ := by
      unfold tateNorm sigmaMinusOne
      apply Finset.prod_congr rfl
      intro g _hg
      calc
        g • (σ • a * a⁻¹) = g • (σ • a) * g • a⁻¹ :=
          MulDistribMulAction.smul_mul g (σ • a) a⁻¹
        _ = (g * σ) • a * (g • a)⁻¹ := by
          rw [← SemigroupAction.mul_smul, smul_inv']
    _ = (∏ g : G, (g * σ) • a) * ∏ g : G, (g • a)⁻¹ := by
      exact Finset.prod_mul_distrib
    _ = 1 := by
      rw [hshift, Finset.prod_inv_distrib, mul_inv_cancel]

/-- The augmentation image lies in the norm kernel. -/
theorem augmentationSubgroup_le_normKernelSubgroup (σ : G) :
    augmentationSubgroup G A σ ≤ normKernelSubgroup G A := by
  intro a ha
  rcases ha with ⟨b, rfl⟩
  exact tateNorm_sigmaMinusOne_eq_one (G := G) (A := A) σ b

/-- The norm is fixed by every group element, placing `N_G b` in `A^G` in the
low-degree cyclic-cohomology exact sequence. -/
theorem smul_tateNorm_eq (h : G) (a : A) :
    h • tateNorm G A a = tateNorm G A a := by
  have hmap : h • (∏ g : G, g • a) = ∏ g : G, h • (g • a) := by
    exact map_prod (MulDistribMulAction.toMonoidHom A h) (fun g : G => g • a) Finset.univ
  have hshift : (∏ g : G, (h * g) • a) = ∏ g : G, g • a := by
    exact Fintype.prod_equiv (Equiv.mulLeft h)
      (fun g : G => (h * g) • a) (fun g : G => g • a) (by intro g; rfl)
  calc
    h • tateNorm G A a = ∏ g : G, h • (g • a) := by
      simpa [tateNorm] using hmap
    _ = ∏ g : G, (h * g) • a := by
      apply Finset.prod_congr rfl
      intro g _hg
      exact (SemigroupAction.mul_smul h g a).symm
    _ = tateNorm G A a := by
      simpa [tateNorm] using hshift

/-- The norm image lies in the fixed subgroup, as in Herbrand-quotient theory. -/
theorem tateNormSubgroup_le_fixedSubgroup :
    tateNormSubgroup G A ≤ fixedSubgroup G A := by
  intro a ha g
  rcases ha with ⟨b, rfl⟩
  exact smul_tateNorm_eq (G := G) (A := A) g b

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- A quotient-level criterion for vanishing of `H⁰`: if every fixed point is
a norm, then the low-degree Herbrand `H⁰` quotient is a subsingleton. -/
theorem herbrandH0_subsingleton_of_fixed_le_tateNormSubgroup
    (h : fixedSubgroup G A ≤ tateNormSubgroup G A) :
    Subsingleton (HerbrandH0 G A) := by
  refine ⟨fun q r => ?_⟩
  have hq : q = 1 := by
    refine HerbrandH0.inductionOn (motive := fun z => z = 1) q ?_
    intro a
    apply (HerbrandH0.mk_eq_one_iff (G := G) (A := A) a).2
    exact h a.2
  have hr : r = 1 := by
    refine HerbrandH0.inductionOn (motive := fun z => z = 1) r ?_
    intro a
    apply (HerbrandH0.mk_eq_one_iff (G := G) (A := A) a).2
    exact h a.2
  rw [hq, hr]

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- A quotient-level criterion for vanishing of `H^{-1}`: if every norm-kernel
element is an augmentation element, then the low-degree Herbrand `H^{-1}`
quotient is a subsingleton. -/
theorem herbrandHMinusOne_subsingleton_of_normKernel_le_augmentationSubgroup
    (σ : G) (h : normKernelSubgroup G A ≤ augmentationSubgroup G A σ) :
    Subsingleton (HerbrandHMinusOne G A σ) := by
  refine ⟨fun q r => ?_⟩
  have hq : q = 1 := by
    refine HerbrandHMinusOne.inductionOn σ
      (motive := fun z => z = 1) q ?_
    intro a
    apply (HerbrandHMinusOne.mk_eq_one_iff (G := G) (A := A) σ a).2
    exact h a.2
  have hr : r = 1 := by
    refine HerbrandHMinusOne.inductionOn σ
      (motive := fun z => z = 1) r ?_
    intro a
    apply (HerbrandHMinusOne.mk_eq_one_iff (G := G) (A := A) σ a).2
    exact h a.2
  rw [hq, hr]

omit [CommGroup C] [MulDistribMulAction G C] in
/-- Transport the `H⁰` vanishing source `A^G ≤ N_G A` across an equivariant
multiplicative equivalence. -/
theorem fixed_le_tateNormSubgroup_of_mulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    (hB : fixedSubgroup G B ≤ tateNormSubgroup G B) :
    fixedSubgroup G A ≤ tateNormSubgroup G A := by
  intro a ha
  have hea : e a ∈ fixedSubgroup G B := by
    intro g
    rw [← he g a, ha g]
  rcases hB hea with ⟨b, hb⟩
  refine ⟨e.symm b, ?_⟩
  apply e.injective
  calc
    e (tateNorm G A (e.symm b)) =
        tateNorm G B (e (e.symm b)) :=
      map_tateNorm (G := G) (A := A) (B := B) e.toMonoidHom
        (fun g a => by simpa using he g a) (e.symm b)
    _ = tateNorm G B b := by rw [e.apply_symm_apply]
    _ = e a := hb

omit [CommGroup C] [MulDistribMulAction G C] in
/-- Transport the `H^{-1}` vanishing source `ker N_G ≤ I_G A` across an
equivariant multiplicative equivalence. -/
theorem normKernel_le_augmentationSubgroup_of_mulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    (σ : G) (hB : normKernelSubgroup G B ≤ augmentationSubgroup G B σ) :
    normKernelSubgroup G A ≤ augmentationSubgroup G A σ := by
  intro a ha
  have haNorm : tateNorm G A a = 1 := by
    simpa [normKernelSubgroup] using ha
  have hea : e a ∈ normKernelSubgroup G B := by
    change tateNorm G B (e a) = 1
    calc
      tateNorm G B (e a) = e (tateNorm G A a) :=
        (map_tateNorm (G := G) (A := A) (B := B) e.toMonoidHom
          (fun g a => by simpa using he g a) a).symm
      _ = e 1 := by rw [haNorm]
      _ = 1 := by simp
  rcases hB hea with ⟨b, hb⟩
  refine ⟨e.symm b, ?_⟩
  apply e.injective
  calc
    e (sigmaMinusOne G A σ (e.symm b)) =
        sigmaMinusOne G B σ (e (e.symm b)) :=
      map_sigmaMinusOne (G := G) (A := A) (B := B) e.toMonoidHom
        (fun g a => by simpa using he g a) σ (e.symm b)
    _ = sigmaMinusOne G B σ b := by rw [e.apply_symm_apply]
    _ = e a := hb

omit [CommGroup C] [MulDistribMulAction G C] in
/-- Transport low-degree `H⁰` triviality across an equivariant multiplicative
equivalence. -/
theorem herbrandH0_subsingleton_of_mulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    (hB : fixedSubgroup G B ≤ tateNormSubgroup G B) :
    Subsingleton (HerbrandH0 G A) :=
  herbrandH0_subsingleton_of_fixed_le_tateNormSubgroup
    (G := G) (A := A)
    (fixed_le_tateNormSubgroup_of_mulEquiv (G := G) (A := A) (B := B) e he hB)

omit [CommGroup C] [MulDistribMulAction G C] in
/-- Transport low-degree `H^{-1}` triviality across an equivariant
multiplicative equivalence. -/
theorem herbrandHMinusOne_subsingleton_of_mulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    (σ : G) (hB : normKernelSubgroup G B ≤ augmentationSubgroup G B σ) :
    Subsingleton (HerbrandHMinusOne G A σ) :=
  herbrandHMinusOne_subsingleton_of_normKernel_le_augmentationSubgroup
    (G := G) (A := A) σ
    (normKernel_le_augmentationSubgroup_of_mulEquiv
      (G := G) (A := A) (B := B) e he σ hB)

omit [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- Membership in the right-regular norm kernel is the single product
condition `∏ g, f g = 1`. -/
theorem rightRegularFunction_mem_normKernelSubgroup_iff (f : G → B) :
    f ∈ rightRegularFunctionNormKernelSubgroup (G := G) (B := B) ↔
      (∏ g : G, f g) = 1 := by
  let := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  have hnorm (x : G) : tateNorm G (G → B) f x = ∏ g : G, f g := by
    calc
      tateNorm G (G → B) f x = ∏ g : G, f (x * g) := by
        unfold tateNorm
        let ev : (G → B) →* B := {
          toFun q := q x
          map_one' := rfl
          map_mul' := by
            intro q r
            rfl
        }
        calc
          ((∏ c : G, c • f) : G → B) x = ev (∏ c : G, c • f) := rfl
          _ = ∏ c : G, ev (c • f) := by rw [map_prod]
          _ = ∏ c : G, f (x * c) := by
            refine Finset.prod_congr rfl ?_
            intro c _hc
            change (c • f) x = f (x * c)
            rfl
      _ = ∏ g : G, f g := by
        exact Fintype.prod_equiv (Equiv.mulLeft x)
          (fun g : G => f (x * g)) (fun g : G => f g) (by intro g; rfl)
  constructor
  · intro hf
    change tateNorm G (G → B) f = 1 at hf
    have hx := congrArg (fun q : G → B => q 1) hf
    calc
      (∏ g : G, f g) = tateNorm G (G → B) f 1 := (hnorm 1).symm
      _ = 1 := by simpa using hx
  · intro hf
    change tateNorm G (G → B) f = 1
    funext x
    calc
      tateNorm G (G → B) f x = ∏ g : G, f g := hnorm x
      _ = 1 := hf

omit [Fintype G] [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- Successor step for the cyclic partial primitive. -/
theorem rightRegularCyclicPartialProduct_succ (σ : G) (f : G → B) (i : ℕ) :
    rightRegularCyclicPartialProduct (G := G) (B := B) σ f (i + 1) =
      rightRegularCyclicPartialProduct (G := G) (B := B) σ f i * f (σ ^ i) := by
  simp [rightRegularCyclicPartialProduct, Finset.prod_range_succ]

omit [Fintype G] [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- The successor step is the desired coboundary equation away from the
wrap-around point. -/
theorem rightRegularCyclicPartialProduct_succ_mul_inv
    (σ : G) (f : G → B) (i : ℕ) :
    rightRegularCyclicPartialProduct (G := G) (B := B) σ f (i + 1) *
        (rightRegularCyclicPartialProduct (G := G) (B := B) σ f i)⁻¹ =
      f (σ ^ i) := by
  rw [rightRegularCyclicPartialProduct_succ]
  simp [mul_comm, mul_assoc]

omit [Fintype G] [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- The product-one condition gives the wrap-around coboundary equation for
the cyclic partial primitive. -/
theorem rightRegularCyclicPartialProduct_wrap_mul_inv_of_eq_one
    (σ : G) (f : G → B) {n : ℕ} (hn : 0 < n)
    (hprod : rightRegularCyclicPartialProduct (G := G) (B := B) σ f n = 1) :
    rightRegularCyclicPartialProduct (G := G) (B := B) σ f 0 *
        (rightRegularCyclicPartialProduct (G := G) (B := B) σ f (n - 1))⁻¹ =
      f (σ ^ (n - 1)) := by
  cases n with
  | zero => cases hn
  | succ n =>
      have hlast :
          rightRegularCyclicPartialProduct (G := G) (B := B) σ f n * f (σ ^ n) = 1 := by
        simpa [rightRegularCyclicPartialProduct_succ] using hprod
      have hinv :
          (rightRegularCyclicPartialProduct (G := G) (B := B) σ f n)⁻¹ = f (σ ^ n) :=
        (mul_eq_one_iff_inv_eq).1 hlast
      simpa [rightRegularCyclicPartialProduct, hinv]

omit [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- The cyclic index represents the original group element. -/
theorem rightRegularCyclicIndex_spec
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (x : G) :
    x = σ ^ (rightRegularCyclicIndex (G := G) σ hgen x).val := by
  simpa [rightRegularCyclicIndex] using
    (Classical.choose_spec (IsCyclic.unique_zpow_zmod (a := σ) hgen x)).1

omit [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- On natural powers in the standard range, the cyclic index has the expected
value. -/
theorem rightRegularCyclicIndex_val_pow_of_lt
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {i : ℕ} (hi : i < Fintype.card G) :
    (rightRegularCyclicIndex (G := G) σ hgen (σ ^ i)).val = i := by
  have hidx :
      rightRegularCyclicIndex (G := G) σ hgen (σ ^ i) =
        (i : ZMod (Fintype.card G)) := by
    apply rightRegularCyclicIndex_eq_of_repr (G := G) σ hgen
    simp [ZMod.val_natCast_of_lt hi]
  rw [hidx, ZMod.val_natCast_of_lt hi]

omit [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- Away from the wrap-around index, the cyclic primitive solves the
right-regular coboundary equation. -/
theorem rightRegularCyclicPrimitive_mul_sigma_mul_inv_of_index_succ_lt
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (f : G → B) (x : G)
    (hix : (rightRegularCyclicIndex (G := G) σ hgen x).val + 1 < Fintype.card G) :
    rightRegularCyclicPrimitive (G := G) (B := B) σ hgen f (x * σ) *
        (rightRegularCyclicPrimitive (G := G) (B := B) σ hgen f x)⁻¹ =
      f x := by
  let i := (rightRegularCyclicIndex (G := G) σ hgen x).val
  have hi : i + 1 < Fintype.card G := by
    simpa [i] using hix
  have hx : x = σ ^ i := by
    simpa [i] using rightRegularCyclicIndex_spec (G := G) σ hgen x
  have hxσ : x * σ = σ ^ (i + 1) := by
    calc
      x * σ = σ ^ i * σ := by rw [hx]
      _ = σ ^ (i + 1) := (pow_succ σ i).symm
  have hidx_xσ :
      (rightRegularCyclicIndex (G := G) σ hgen (x * σ)).val = i + 1 := by
    rw [hxσ]
    exact rightRegularCyclicIndex_val_pow_of_lt (G := G) σ hgen hi
  change rightRegularCyclicPartialProduct (G := G) (B := B) σ f
        (rightRegularCyclicIndex (G := G) σ hgen (x * σ)).val *
      (rightRegularCyclicPartialProduct (G := G) (B := B) σ f
        (rightRegularCyclicIndex (G := G) σ hgen x).val)⁻¹ = f x
  rw [hidx_xσ, show (rightRegularCyclicIndex (G := G) σ hgen x).val = i by rfl, hx]
  exact rightRegularCyclicPartialProduct_succ_mul_inv (G := G) (B := B) σ f i

omit [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- At the wrap-around index, the product-one condition makes the cyclic
primitive solve the right-regular coboundary equation. -/
theorem rightRegularCyclicPrimitive_mul_sigma_mul_inv_of_index_eq_card_sub_one
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (f : G → B) (x : G)
    (hix : (rightRegularCyclicIndex (G := G) σ hgen x).val = Fintype.card G - 1)
    (hprod :
      rightRegularCyclicPartialProduct (G := G) (B := B) σ f (Fintype.card G) = 1) :
    rightRegularCyclicPrimitive (G := G) (B := B) σ hgen f (x * σ) *
        (rightRegularCyclicPrimitive (G := G) (B := B) σ hgen f x)⁻¹ =
      f x := by
  have hcard_pos : 0 < Fintype.card G := Fintype.card_pos
  let i := (rightRegularCyclicIndex (G := G) σ hgen x).val
  have hi : i = Fintype.card G - 1 := by
    simpa [i] using hix
  have hx : x = σ ^ i := by
    simpa [i] using rightRegularCyclicIndex_spec (G := G) σ hgen x
  have horder : orderOf σ = Fintype.card G := by
    simpa [Nat.card_eq_fintype_card] using
      orderOf_eq_card_of_forall_mem_zpowers (g := σ) hgen
  have hpow_card : σ ^ Fintype.card G = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one σ
  have hxσ : x * σ = 1 := by
    calc
      x * σ = σ ^ i * σ := by rw [hx]
      _ = σ ^ (i + 1) := (pow_succ σ i).symm
      _ = σ ^ Fintype.card G := by
        rw [hi, Nat.sub_add_cancel (Nat.succ_le_of_lt hcard_pos)]
      _ = 1 := hpow_card
  have hidx_xσ :
      (rightRegularCyclicIndex (G := G) σ hgen (x * σ)).val = 0 := by
    have hidx :
        rightRegularCyclicIndex (G := G) σ hgen (x * σ) =
          (0 : ZMod (Fintype.card G)) := by
      apply rightRegularCyclicIndex_eq_of_repr (G := G) σ hgen
      simp [hxσ]
    rw [hidx]
    simp
  have hwrap :
      rightRegularCyclicPartialProduct (G := G) (B := B) σ f 0 *
          (rightRegularCyclicPartialProduct (G := G) (B := B) σ f
            (Fintype.card G - 1))⁻¹ =
        f (σ ^ (Fintype.card G - 1)) :=
    rightRegularCyclicPartialProduct_wrap_mul_inv_of_eq_one
      (G := G) (B := B) σ f hcard_pos hprod
  change rightRegularCyclicPartialProduct (G := G) (B := B) σ f
        (rightRegularCyclicIndex (G := G) σ hgen (x * σ)).val *
      (rightRegularCyclicPartialProduct (G := G) (B := B) σ f
        (rightRegularCyclicIndex (G := G) σ hgen x).val)⁻¹ = f x
  rw [hidx_xσ, hix, hx, hi]
  exact hwrap

omit [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- If the cyclic partial product over a full period is `1`, the group-indexed
cyclic primitive solves the right-regular coboundary equation at every point. -/
theorem rightRegularCyclicPrimitive_mul_sigma_mul_inv_of_partialProduct_eq_one
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (f : G → B)
    (hprod :
      rightRegularCyclicPartialProduct (G := G) (B := B) σ f (Fintype.card G) = 1)
    (x : G) :
    rightRegularCyclicPrimitive (G := G) (B := B) σ hgen f (x * σ) *
        (rightRegularCyclicPrimitive (G := G) (B := B) σ hgen f x)⁻¹ =
      f x := by
  have hcard_pos : 0 < Fintype.card G := Fintype.card_pos
  have : NeZero (Fintype.card G) := ⟨hcard_pos.ne'⟩
  let i := (rightRegularCyclicIndex (G := G) σ hgen x).val
  have hi_lt : i < Fintype.card G := by
    simpa [i] using ZMod.val_lt (rightRegularCyclicIndex (G := G) σ hgen x)
  by_cases hsucc : i + 1 < Fintype.card G
  · exact rightRegularCyclicPrimitive_mul_sigma_mul_inv_of_index_succ_lt
      (G := G) (B := B) σ hgen f x (by simpa [i] using hsucc)
  · have hsucc_le : i + 1 ≤ Fintype.card G := Nat.succ_le_of_lt hi_lt
    have hcard_le : Fintype.card G ≤ i + 1 := le_of_not_gt hsucc
    have hsucc_eq : i + 1 = Fintype.card G := le_antisymm hsucc_le hcard_le
    have hlast : i = Fintype.card G - 1 := by
      rw [← hsucc_eq]
      simp
    exact rightRegularCyclicPrimitive_mul_sigma_mul_inv_of_index_eq_card_sub_one
      (G := G) (B := B) σ hgen f x (by simpa [i] using hlast) hprod

omit [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- A right-regular norm-kernel element has product `1` along one full cyclic
enumeration by a generator. -/
theorem rightRegularFunction_prod_powers_eq_one_of_mem_normKernel
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {f : G → B}
    (hf : f ∈ rightRegularFunctionNormKernelSubgroup (G := G) (B := B)) :
    (Finset.range (Nat.card G)).prod (fun i => f (σ ^ i)) = 1 := by
  classical
  have hprod : (∏ g : G, f g) = 1 :=
    (rightRegularFunction_mem_normKernelSubgroup_iff (G := G) (B := B) f).1 hf
  have hcard : orderOf σ = Nat.card G :=
    orderOf_eq_card_of_forall_mem_zpowers (g := σ) hgen
  have hinj : Set.InjOn (fun i : ℕ => σ ^ i) (Finset.range (Nat.card G) : Set ℕ) := by
    intro i hi j hj hij
    have hmod : i ≡ j [MOD orderOf σ] := (pow_eq_pow_iff_modEq (x := σ)).1 hij
    rw [hcard] at hmod
    exact Nat.ModEq.eq_of_lt_of_lt hmod (by simpa using hi) (by simpa using hj)
  have himage :
      Finset.image (fun i : ℕ => σ ^ i) (Finset.range (Nat.card G)) = Finset.univ :=
    IsCyclic.image_range_card (a := σ) hgen
  calc
    (Finset.range (Nat.card G)).prod (fun i => f (σ ^ i)) =
        (Finset.image (fun i : ℕ => σ ^ i) (Finset.range (Nat.card G))).prod
          (fun x => f x) := by
      exact (Finset.prod_image (s := Finset.range (Nat.card G))
        (g := fun i : ℕ => σ ^ i) (f := f) hinj).symm
    _ = ∏ x : G, f x := by
      rw [himage]
    _ = 1 := hprod

omit [Fintype G] [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- Membership in the right-regular augmentation subgroup is the pointwise
difference equation `b (x * σ) * (b x)⁻¹ = f x`. -/
theorem rightRegularFunction_mem_augmentationSubgroup_iff
    (σ : G) (f : G → B) :
    f ∈ rightRegularFunctionAugmentationSubgroup (G := G) (B := B) σ ↔
      ∃ b : G → B, ∀ x : G, b (x * σ) * (b x)⁻¹ = f x := by
  let := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  constructor
  · intro hf
    change f ∈ augmentationSubgroup G (G → B) σ at hf
    rcases hf with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro x
    have hx := congrArg (fun q : G → B => q x) hb
    change b (x * σ) * (b x)⁻¹ = f x at hx
    exact hx
  · rintro ⟨b, hb⟩
    change f ∈ augmentationSubgroup G (G → B) σ
    refine ⟨b, ?_⟩
    funext x
    change b (x * σ) * (b x)⁻¹ = f x
    exact hb x

omit [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- Concrete `H^{-1}` source for the right-regular multiplicative induced
module: every norm-kernel element is an augmentation element. -/
theorem rightRegularFunction_normKernel_le_augmentationSubgroup
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    rightRegularFunctionNormKernelSubgroup (G := G) (B := B) ≤
      rightRegularFunctionAugmentationSubgroup (G := G) (B := B) σ := by
  intro f hf
  have hprod_nat :
      (Finset.range (Nat.card G)).prod (fun i => f (σ ^ i)) = 1 :=
    rightRegularFunction_prod_powers_eq_one_of_mem_normKernel
      (G := G) (B := B) σ hgen hf
  have hprod :
      rightRegularCyclicPartialProduct (G := G) (B := B) σ f (Fintype.card G) = 1 := by
    simpa [rightRegularCyclicPartialProduct, Nat.card_eq_fintype_card] using hprod_nat
  rw [rightRegularFunction_mem_augmentationSubgroup_iff (G := G) (B := B) σ f]
  refine ⟨rightRegularCyclicPrimitive (G := G) (B := B) σ hgen f, ?_⟩
  intro x
  exact rightRegularCyclicPrimitive_mul_sigma_mul_inv_of_partialProduct_eq_one
    (G := G) (B := B) σ hgen f hprod x

omit [CommGroup A] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- Concrete `H⁰` source for induced modules: for the right-regular
multiplicative induced module `G → B`, every fixed point is a norm. -/
theorem rightRegularFunction_fixed_le_tateNormSubgroup :
    rightRegularFunctionFixedSubgroup (G := G) (B := B) ≤
      rightRegularFunctionTateNormSubgroup (G := G) (B := B) := by
  classical
  let := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  intro f hf
  change f ∈ fixedSubgroup G (G → B) at hf
  change f ∈ tateNormSubgroup G (G → B)
  let d : G → B := fun y => if y = 1 then f 1 else 1
  refine ⟨d, ?_⟩
  funext x
  have hfixed_x : f x = f 1 := by
    have hx := congrArg (fun q : G → B => q 1) (hf x)
    change f (1 * x) = f 1 at hx
    simpa using hx
  calc
    tateNorm G (G → B) d x = ∏ g : G, d (x * g) := by
      unfold tateNorm
      let ev : (G → B) →* B := {
        toFun q := q x
        map_one' := rfl
        map_mul' := by
          intro q r
          rfl
      }
      calc
        ((∏ c : G, c • d) : G → B) x = ev (∏ c : G, c • d) := rfl
        _ = ∏ c : G, ev (c • d) := by rw [map_prod]
        _ = ∏ c : G, d (x * c) := by
          refine Finset.prod_congr rfl ?_
          intro c _hc
          change (c • d) x = d (x * c)
          rfl
    _ = f 1 := by
      calc
        (∏ g : G, d (x * g)) = d (x * x⁻¹) := by
          refine Finset.prod_eq_single (s := Finset.univ) x⁻¹ ?_ ?_
          · intro g _hg hg
            have hxg : x * g ≠ 1 := by
              intro hxg_one
              apply hg
              calc
                g = 1 * g := by simp
                _ = (x⁻¹ * x) * g := by simp
                _ = x⁻¹ * (x * g) := by rw [mul_assoc]
                _ = x⁻¹ * 1 := by rw [hxg_one]
                _ = x⁻¹ := by simp
            simp [d, hxg]
          · intro hxinv
            simp at hxinv
        _ = f 1 := by simp [d]
    _ = f x := hfixed_x.symm

omit [CommGroup C] [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Transport `H⁰` vanishing from the right-regular trivial-subgroup model
along an explicit multiplicative equivalence. -/
theorem herbrandH0_subsingleton_of_equiv_rightRegularFunction
    (e : A ≃* (G → B))
    (he : ∀ (g : G) (a : A) (x : G), e (g • a) x = e a (x * g)) :
    Subsingleton (HerbrandH0 G A) := by
  let := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  exact herbrandH0_subsingleton_of_mulEquiv
    (G := G) (A := A) (B := G → B) e
    (by
      intro g a
      funext x
      change e (g • a) x = e a (x * g)
      exact he g a x)
    (rightRegularFunction_fixed_le_tateNormSubgroup (G := G) (B := B))

omit [CommGroup C] [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Transport `H^{-1}` vanishing from the right-regular trivial-subgroup model
along an explicit multiplicative equivalence. -/
theorem herbrandHMinusOne_subsingleton_of_equiv_rightRegularFunction
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (e : A ≃* (G → B))
    (he : ∀ (g : G) (a : A) (x : G), e (g • a) x = e a (x * g)) :
    Subsingleton (HerbrandHMinusOne G A σ) := by
  let := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  exact herbrandHMinusOne_subsingleton_of_mulEquiv
    (G := G) (A := A) (B := G → B) e
    (by
      intro g a
      funext x
      change e (g • a) x = e a (x * g)
      exact he g a x)
    σ
    (rightRegularFunction_normKernel_le_augmentationSubgroup
      (G := G) (B := B) σ hgen)

omit [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- `H⁰` vanishing for a multiplicative wrapper transported from an additive
right-regular equivalence. -/
theorem herbrandH0_subsingleton_of_addEquiv_rightRegularFunction
    {M : Type uA} {D : Type uB}
    [AddCommGroup M] [DistribMulAction G M] [AddCommGroup D]
    (e : M ≃+ (G → D))
    (he : ∀ (g : G) (m : M) (x : G), e (g • m) x = e m (x * g)) :
    letI := multiplicativeMulDistribMulActionOfDistribMulAction G M
    Subsingleton (HerbrandH0 G (Multiplicative M)) := by
  let := multiplicativeMulDistribMulActionOfDistribMulAction G M
  let : MulDistribMulAction G (Multiplicative D) := {
    smul _ d := d
    one_smul := by
      intro d
      rfl
    mul_smul := by
      intro _ _ d
      rfl
    smul_mul := by
      intro _ d e
      rfl
    smul_one := by
      intro _
      rfl
  }
  exact herbrandH0_subsingleton_of_equiv_rightRegularFunction
    (G := G) (A := Multiplicative M) (B := Multiplicative D)
    (mulEquivRightRegularFunctionOfAddEquiv G e)
    (by
      intro g m x
      exact mulEquivRightRegularFunctionOfAddEquiv_commutes
        (G := G) e he g m x)

omit [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C] in
/-- `H^{-1}` vanishing for a multiplicative wrapper transported from an
additive right-regular equivalence. -/
theorem herbrandHMinusOne_subsingleton_of_addEquiv_rightRegularFunction
    {M : Type uA} {D : Type uB}
    [AddCommGroup M] [DistribMulAction G M] [AddCommGroup D]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (e : M ≃+ (G → D))
    (he : ∀ (g : G) (m : M) (x : G), e (g • m) x = e m (x * g)) :
    letI := multiplicativeMulDistribMulActionOfDistribMulAction G M
    Subsingleton (HerbrandHMinusOne G (Multiplicative M) σ) := by
  let := multiplicativeMulDistribMulActionOfDistribMulAction G M
  let : MulDistribMulAction G (Multiplicative D) := {
    smul _ d := d
    one_smul := by
      intro d
      rfl
    mul_smul := by
      intro _ _ d
      rfl
    smul_mul := by
      intro _ d e
      rfl
    smul_one := by
      intro _
      rfl
  }
  exact herbrandHMinusOne_subsingleton_of_equiv_rightRegularFunction
    (G := G) (A := Multiplicative M) (B := Multiplicative D)
    σ hgen (mulEquivRightRegularFunctionOfAddEquiv G e)
    (by
      intro g m x
      exact mulEquivRightRegularFunctionOfAddEquiv_commutes
        (G := G) e he g m x)

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Quotient-cardinality source for `H⁰(G,A)=A^G/N_G A`. -/
theorem card_fixedSubgroup_eq_card_herbrandH0_mul_card_tateNormSubgroup [Finite A] :
    Nat.card (fixedSubgroup G A) =
      Nat.card (HerbrandH0 G A) * Nat.card (tateNormSubgroup G A) := by
  simpa [HerbrandH0,
    card_subgroupOf_eq_card (tateNormSubgroup_le_fixedSubgroup (G := G) (A := A))] using
    (Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)))

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- Quotient-cardinality source for
`H^{-1}(G,A)=ker(N_G)/I_G A`. -/
theorem card_normKernelSubgroup_eq_card_herbrandHMinusOne_mul_card_augmentationSubgroup
    (σ : G) [Finite A] :
    Nat.card (normKernelSubgroup G A) =
      Nat.card (HerbrandHMinusOne G A σ) *
        Nat.card (augmentationSubgroup G A σ) := by
  simpa [HerbrandHMinusOne,
    card_subgroupOf_eq_card (augmentationSubgroup_le_normKernelSubgroup (G := G) (A := A) σ)] using
    (Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)))

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The two low-degree Herbrand quotients of a finite cyclic module have equal
cardinality, the finite-module source for Herbrand-quotient multiplicativity. -/
theorem herbrand_finite_module_card_eq
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    Nat.card (HerbrandH0 G A) = Nat.card (HerbrandHMinusOne G A σ) := by
  have h0 := card_fixedSubgroup_eq_card_herbrandH0_mul_card_tateNormSubgroup
    (G := G) (A := A)
  have hm := card_normKernelSubgroup_eq_card_herbrandHMinusOne_mul_card_augmentationSubgroup
    (G := G) (A := A) σ
  have hbal := herbrand_finite_module_cardinality_balance
    (G := G) (A := A) σ hgen
  rw [h0, hm] at hbal
  have hfactor :
      Nat.card (HerbrandH0 G A) *
          (Nat.card (tateNormSubgroup G A) * Nat.card (augmentationSubgroup G A σ)) =
        Nat.card (HerbrandHMinusOne G A σ) *
          (Nat.card (tateNormSubgroup G A) * Nat.card (augmentationSubgroup G A σ)) := by
    calc
      Nat.card (HerbrandH0 G A) *
          (Nat.card (tateNormSubgroup G A) * Nat.card (augmentationSubgroup G A σ))
          =
          (Nat.card (HerbrandH0 G A) * Nat.card (tateNormSubgroup G A)) *
            Nat.card (augmentationSubgroup G A σ) := by
            ac_rfl
      _ = (Nat.card (HerbrandHMinusOne G A σ) *
            Nat.card (augmentationSubgroup G A σ)) *
            Nat.card (tateNormSubgroup G A) := hbal
      _ = Nat.card (HerbrandHMinusOne G A σ) *
          (Nat.card (tateNormSubgroup G A) * Nat.card (augmentationSubgroup G A σ)) := by
            ac_rfl
  have hNpos : 0 < Nat.card (tateNormSubgroup G A) :=
    Finite.card_pos (α := tateNormSubgroup G A)
  have hIpos : 0 < Nat.card (augmentationSubgroup G A σ) :=
    Finite.card_pos (α := augmentationSubgroup G A σ)
  exact Nat.mul_right_cancel (Nat.mul_pos hNpos hIpos) hfactor

end Herbrand
end ProfiniteCohomology

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_TateComparison
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.inducedFixedEquiv_apply_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-! Comparisons between arithmetic Herbrand quotient presentations and mathlib Tate cohomology. -/

open CategoryTheory

namespace CyclicCohomology.ProfiniteCohomology.Herbrand

noncomputable section

universe u w

variable {G A B C : Type}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

theorem repNorm_toMul (a : Additive A) :
    Additive.toMul
        ((Rep.ofMulDistribMulAction G A).ρ.norm a) =
      tateNorm G A a.toMul := by
  unfold Rep.ofMulDistribMulAction
  change Additive.toMul
      ((Representation.ofMulDistribMulAction G A).norm a) =
    ∏ g : G, g • a.toMul
  exact Representation.norm_ofMulDistribMulAction_eq a

theorem repSigmaMinusOne_toMul
    {G A : Type} [CommGroup G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G) (a : Additive A) :
    Additive.toMul
        ((Rep.toAdditive (M := G) (G := A))
          (((Rep.ofMulDistribMulAction G A).applyAsHom σ -
            𝟙 (Rep.ofMulDistribMulAction G A)).hom a)) =
      sigmaMinusOne G A σ a.toMul := by
  unfold Rep.toAdditive
  unfold Rep.ofMulDistribMulAction
  rw [Rep.sub_hom]
  rw [show
    (Rep.Hom.hom
        ((Rep.of (Representation.ofMulDistribMulAction G A)).applyAsHom σ) -
      Rep.Hom.hom
        (𝟙 (Rep.of (Representation.ofMulDistribMulAction G A)))) a =
        Rep.Hom.hom
            ((Rep.of (Representation.ofMulDistribMulAction G A)).applyAsHom σ) a -
          Rep.Hom.hom
            (𝟙 (Rep.of (Representation.ofMulDistribMulAction G A))) a by
    rfl]
  rw [Rep.applyAsHom_apply]
  rw [show
    Rep.Hom.hom
        (𝟙 (Rep.of (Representation.ofMulDistribMulAction G A))) a = a by
    rfl]
  unfold sigmaMinusOne
  rw [show
    ((Rep.of (Representation.ofMulDistribMulAction G A)).ρ σ) a =
      Additive.ofMul (σ • a.toMul) by
    rfl]
  change Additive.toMul
      (Additive.ofMul (σ • a.toMul) - a) =
    σ • a.toMul * (a.toMul)⁻¹
  rw [toMul_sub]
  exact div_eq_mul_inv _ _

def fixedCyclesAddEquiv :
    LinearMap.ker
        (groupCohomology.d₀₁ (Rep.ofMulDistribMulAction G A)).hom ≃+
      Additive (fixedSubgroup G A) where
  toFun x :=
    Additive.ofMul
      ⟨x.1.toMul, by
        have hx : x.1 ∈ (Rep.ofMulDistribMulAction G A).ρ.invariants := by
          rw [← groupCohomology.d₀₁_ker_eq_invariants]
          exact x.2
        intro g
        apply Additive.ofMul.injective
        exact hx g⟩
  invFun x :=
    ⟨Additive.ofMul x.toMul.1, by
      rw [groupCohomology.d₀₁_ker_eq_invariants]
      intro g
      apply Additive.ofMul.injective
      exact x.toMul.2 g⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    rfl

/-- Mathlib's degree-zero Tate cohomology is the arithmetic fixed-point
quotient by the norm image used by `HerbrandH0`. -/
noncomputable def tateH0IsoHerbrandH0 :
    tateCohomology (Rep.ofMulDistribMulAction G A) 0 ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G A)) := by
  let M := Rep.ofMulDistribMulAction G A
  let S : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk M.norm.toModuleCatHom (groupCohomology.d₀₁ M)
      (Rep.norm_comp_d_eq_zero M)
  let eKOwner :
      S.moduleCatLeftHomologyData.K ≅
        ModuleCat.of ℤ
          (LinearMap.ker
            (groupCohomology.d₀₁ (Rep.ofMulDistribMulAction G A)).hom) :=
    eqToIso (by rfl)
  let eK :=
    (eKOwner ≪≫
      ((fixedCyclesAddEquiv (G := G) (A := A)).toIntLinearEquiv
        (modM := inferInstance) (modM₂ := inferInstance)).toModuleIso).toLinearEquiv
  let q : Additive (fixedSubgroup G A) →+ Additive (HerbrandH0 G A) :=
    MonoidHom.toAdditive (HerbrandH0.mk (G := G) (A := A))
  have hboundary :
      (LinearMap.range S.moduleCatToCycles).map eK.toLinearMap =
        q.ker.toIntSubmodule := by
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha⟩, rfl⟩
      subst y
      change Additive A at a
      change q (eK (S.moduleCatToCycles a)) = 0
      apply Additive.ofMul.injective
      change HerbrandH0.mk _ = 1
      apply (HerbrandH0.mk_eq_one_iff _).2
      refine ⟨a.toMul, ?_⟩
      dsimp [eK, fixedCyclesAddEquiv, S, M]
      exact (repNorm_toMul (G := G) (A := A) a).symm
    · intro hx
      change q x = 0 at hx
      have hx' : HerbrandH0.mk x.toMul = 1 := by
        apply Additive.ofMul.injective
        exact hx
      rcases (HerbrandH0.mk_eq_one_iff x.toMul).1 hx' with ⟨a, ha⟩
      refine ⟨eK.symm x, ?_, eK.apply_symm_apply x⟩
      refine ⟨Additive.ofMul a, ?_⟩
      apply eK.injective
      rw [eK.apply_symm_apply]
      apply Additive.toMul.injective
      apply Subtype.ext
      have hnorm :
          Additive.toMul
              ((Representation.ofMulDistribMulAction G A).norm
                (Additive.ofMul a)) =
            x.toMul.1 :=
        (Representation.norm_ofMulDistribMulAction_eq
          (G := G) (M := A) (Additive.ofMul a)).trans <| by
            rw [show Additive.toMul (Additive.ofMul a) = a by rfl]
            simpa only [tateNormHom_apply, tateNorm] using ha
      dsimp [eK, fixedCyclesAddEquiv, S, M]
      unfold Rep.ofMulDistribMulAction
      exact hnorm
  let eQ :=
    (Submodule.Quotient.equiv (LinearMap.range S.moduleCatToCycles)
      q.ker.toIntSubmodule eK hboundary).trans
      ((QuotientAddGroup.quotientKerEquivOfSurjective q
        (HerbrandH0.mk_surjective (G := G) (A := A))).toIntLinearEquiv
          (modM₂ := inferInstance))
  exact TateCohomology.isoZeroBoundary M ≪≫
    S.moduleCatHomologyIso ≪≫ eQ.toModuleIso

def normKernelCyclesAddEquiv :
    LinearMap.ker
        (Rep.ofMulDistribMulAction G A).norm.toModuleCatHom.hom ≃+
      Additive (normKernelSubgroup G A) where
  toFun x :=
    let a : Additive A := x.1
    Additive.ofMul
      ⟨a.toMul, by
        change tateNorm G A a.toMul = 1
        have hx := x.2
        change (Rep.ofMulDistribMulAction G A).ρ.norm a = 0 at hx
        exact (repNorm_toMul (G := G) (A := A) a).symm.trans <| by
          rw [hx]
          rfl⟩
  invFun x :=
    let a : Additive A := Additive.ofMul x.toMul.1
    ⟨a, by
      have hx0 := x.toMul.2
      change tateNorm G A x.toMul.1 = 1 at hx0
      have hx : tateNorm G A a.toMul = 1 := hx0
      change (Rep.ofMulDistribMulAction G A).ρ.norm a = 0
      unfold Rep.ofMulDistribMulAction
      apply Additive.toMul.injective
      change Additive.toMul
          ((Representation.ofMulDistribMulAction G A).norm a) = (1 : A)
      exact
        (Representation.norm_ofMulDistribMulAction_eq
          (G := G) (M := A) a).trans <| by
            simpa [tateNorm] using hx⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Additive.ofMul.injective
    apply Subtype.ext
    rfl

noncomputable def tateHMinusOneIsoHerbrandHMinusOne_of_commGroup
    {G A : Type} [CommGroup G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    tateCohomology (Rep.ofMulDistribMulAction G A) (-1) ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) := by
  let M := Rep.ofMulDistribMulAction G A
  let S := Rep.FiniteCyclicGroup.subCompNormHom M σ
  let eKOwner :
      S.moduleCatLeftHomologyData.K ≅
        ModuleCat.of ℤ
          (LinearMap.ker
            (Rep.ofMulDistribMulAction G A).norm.toModuleCatHom.hom) :=
    eqToIso (by rfl)
  let eK :=
    (eKOwner ≪≫
      ((normKernelCyclesAddEquiv (G := G) (A := A)).toIntLinearEquiv
        (modM := inferInstance) (modM₂ := inferInstance)).toModuleIso).toLinearEquiv
  let q : Additive (normKernelSubgroup G A) →+
      Additive (HerbrandHMinusOne G A σ) :=
    MonoidHom.toAdditive (HerbrandHMinusOne.mk (G := G) (A := A) σ)
  have hboundary :
      (LinearMap.range S.moduleCatToCycles).map eK.toLinearMap =
        q.ker.toIntSubmodule := by
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha⟩, rfl⟩
      subst y
      change Additive A at a
      change q (eK (S.moduleCatToCycles a)) = 0
      apply Additive.ofMul.injective
      change HerbrandHMinusOne.mk σ _ = 1
      apply (HerbrandHMinusOne.mk_eq_one_iff σ _).2
      refine ⟨a.toMul, ?_⟩
      dsimp [eK, normKernelCyclesAddEquiv, S, M]
      exact (repSigmaMinusOne_toMul
        (G := G) (A := A) σ a).symm
    · intro hx
      change q x = 0 at hx
      have hx' : HerbrandHMinusOne.mk σ x.toMul = 1 := by
        apply Additive.ofMul.injective
        exact hx
      rcases (HerbrandHMinusOne.mk_eq_one_iff σ x.toMul).1 hx' with ⟨a, ha⟩
      refine ⟨eK.symm x, ?_, eK.apply_symm_apply x⟩
      refine ⟨Additive.ofMul a, ?_⟩
      apply eK.injective
      rw [eK.apply_symm_apply]
      apply Additive.toMul.injective
      apply Subtype.ext
      dsimp [eK, normKernelCyclesAddEquiv, S, M]
      have hσ := repSigmaMinusOne_toMul
        (G := G) (A := A) σ (Additive.ofMul a)
      rw [show Additive.toMul (Additive.ofMul a) = a by rfl] at hσ
      exact hσ.trans ha
  let eQ :=
    (Submodule.Quotient.equiv (LinearMap.range S.moduleCatToCycles)
      q.ker.toIntSubmodule eK hboundary).trans
      ((QuotientAddGroup.quotientKerEquivOfSurjective q
        (HerbrandHMinusOne.mk_surjective (G := G) (A := A) σ)).toIntLinearEquiv
          (modM₂ := inferInstance))
  exact TateCohomology.isoFiniteCyclicNegOne M σ hgen ≪≫
    S.moduleCatHomologyIso ≪≫ eQ.toModuleIso

/-- For a chosen generator `σ`, mathlib's degree-minus-one Tate cohomology is
the arithmetic quotient `ker N / im (σ - 1)` used by `HerbrandHMinusOne`. -/
noncomputable def tateHMinusOneIsoHerbrandHMinusOne
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    tateCohomology (Rep.ofMulDistribMulAction G A) (-1) ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) := by
  letI : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  exact tateHMinusOneIsoHerbrandHMinusOne_of_commGroup σ hgen

end

end CyclicCohomology.ProfiniteCohomology.Herbrand
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_Cardinality
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace CyclicCohomology

/-!
# Cardinality identity from the standard Tate exact sequence

For a short exact sequence of finite cyclic modules, this module applies
mathlib's homology long exact sequence to the standard two-periodic cyclic
complex.  The resulting cardinality identity is transported to the
arithmetic `H⁰` and `H⁻¹` presentations.
-/

noncomputable section

namespace ProfiniteCohomology
namespace Herbrand

open CategoryTheory

variable {G A B C : Type}

section

variable [CommGroup G] [Fintype G]
variable [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

noncomputable def periodicEvenHerbrandHMinusOneIso
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {n : ℕ} [NeZero n] (hn : Even n) :
    (Rep.FiniteCyclicGroup.moduleCatChainComplex
        (Rep.ofMulDistribMulAction G A) σ).homology n ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) :=
  periodicHomologyIsoEven (Rep.ofMulDistribMulAction G A) σ hn ≪≫
    (TateCohomology.isoFiniteCyclicNegOne
      (Rep.ofMulDistribMulAction G A) σ hgen).symm ≪≫
    tateHMinusOneIsoHerbrandHMinusOne σ hgen

noncomputable def periodicOddHerbrandHZeroIso
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {n : ℕ} (hn : Odd n) :
    (Rep.FiniteCyclicGroup.moduleCatChainComplex
        (Rep.ofMulDistribMulAction G A) σ).homology n ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G A)) :=
  periodicHomologyIsoOdd (Rep.ofMulDistribMulAction G A) σ hn ≪≫
    (TateCohomology.isoFiniteCyclicZero
      (Rep.ofMulDistribMulAction G A) σ hgen).symm ≪≫
    tateH0IsoHerbrandH0

end

/-- The finite-cardinality identity supplied directly by mathlib's standard
two-periodic Tate exact sequence for a finite cyclic group. -/
theorem herbrand_exact_cardinality_identity
    [Group G] [Fintype G]
    [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C]
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    Nat.card (HerbrandH0 G B) *
        Nat.card (HerbrandHMinusOne G A σ) *
        Nat.card (HerbrandHMinusOne G C σ) =
      Nat.card (HerbrandH0 G A) *
        Nat.card (HerbrandH0 G C) *
        Nat.card (HerbrandHMinusOne G B σ) := by
  let : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  let : CommGroup G := IsCyclic.commGroup
  let S := periodicShortComplex σ i j hi hj hker
  have hS : S.ShortExact :=
    periodicShortComplex_shortExact σ i j hi hj hker hinj hsurj
  let eA4 : S.X₁.homology 4 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := A) (n := 4) σ hgen (⟨2, rfl⟩ : Even 4)
  let eB4 : S.X₂.homology 4 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G B σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := B) (n := 4) σ hgen (⟨2, rfl⟩ : Even 4)
  let eC4 : S.X₃.homology 4 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G C σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := C) (n := 4) σ hgen (⟨2, rfl⟩ : Even 4)
  let eA3 : S.X₁.homology 3 ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G A)) := by
    exact periodicOddHerbrandHZeroIso
      (G := G) (A := A) (n := 3) σ hgen (⟨1, rfl⟩ : Odd 3)
  let eB3 : S.X₂.homology 3 ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G B)) := by
    exact periodicOddHerbrandHZeroIso
      (G := G) (A := B) (n := 3) σ hgen (⟨1, rfl⟩ : Odd 3)
  let eC3 : S.X₃.homology 3 ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G C)) := by
    exact periodicOddHerbrandHZeroIso
      (G := G) (A := C) (n := 3) σ hgen (⟨1, rfl⟩ : Odd 3)
  let eA2 : S.X₁.homology 2 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := A) (n := 2) σ hgen (by simp : Even 2)
  let eB2 : S.X₂.homology 2 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G B σ)) := by
    exact periodicEvenHerbrandHMinusOneIso
      (G := G) (A := B) (n := 2) σ hgen (by simp : Even 2)
  let pA4 : S.X₁.homology 4 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.ofMulDistribMulAction G A) σ).homology := by
    exact periodicHomologyIsoEven
      (Rep.ofMulDistribMulAction G A) σ (⟨2, rfl⟩ : Even 4)
  let pB4 : S.X₂.homology 4 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.ofMulDistribMulAction G B) σ).homology := by
    exact periodicHomologyIsoEven
      (Rep.ofMulDistribMulAction G B) σ (⟨2, rfl⟩ : Even 4)
  let pA2 : S.X₁.homology 2 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.ofMulDistribMulAction G A) σ).homology := by
    exact periodicHomologyIsoEven
      (Rep.ofMulDistribMulAction G A) σ (by simp : Even 2)
  let pB2 : S.X₂.homology 2 ≅
      (Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.ofMulDistribMulAction G B) σ).homology := by
    exact periodicHomologyIsoEven
      (Rep.ofMulDistribMulAction G B) σ (by simp : Even 2)
  let : Finite (S.X₁.homology 4) := finite_source_of_moduleIso eA4
  let : Finite (S.X₂.homology 4) := finite_source_of_moduleIso eB4
  let : Finite (S.X₃.homology 4) := finite_source_of_moduleIso eC4
  let : Finite (S.X₁.homology 3) := finite_source_of_moduleIso eA3
  let : Finite (S.X₂.homology 3) := finite_source_of_moduleIso eB3
  let : Finite (S.X₃.homology 3) := finite_source_of_moduleIso eC3
  let : Finite (S.X₁.homology 2) := finite_source_of_moduleIso eA2
  let f4 := HomologicalComplex.homologyMap S.f 4
  let g4 := HomologicalComplex.homologyMap S.g 4
  let δ43 := hS.δ 4 3 (by simp)
  let f3 := HomologicalComplex.homologyMap S.f 3
  let g3 := HomologicalComplex.homologyMap S.g 3
  let δ32 := hS.δ 3 2 (by simp)
  let f2 := HomologicalComplex.homologyMap S.f 2
  have hexactB4 : Function.Exact f4 g4 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₂ 4)
  have hexactC4 : Function.Exact g4 δ43 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₃ 4 3 (by simp))
  have hexactA3 : Function.Exact δ43 f3 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₁ 4 3 (by simp))
  have hexactB3 : Function.Exact f3 g3 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₂ 3)
  have hexactC3 : Function.Exact g3 δ32 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₃ 3 2 (by simp))
  have hexactA2 : Function.Exact δ32 f2 :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₁ 3 2 (by simp))
  have hB4 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact f4 g4 hexactB4
  have hC4 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact g4 δ43 hexactC4
  have hA3 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact δ43 f3 hexactA3
  have hB3 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact f3 g3 hexactB3
  have hC3 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact g3 δ32 hexactC3
  have hA2 :=
    moduleCat_card_eq_card_range_mul_card_range_of_exact δ32 f2 hexactA2
  let q := ShortComplex.homologyMap (subCompNormMap σ i hi)
  have hf4q :
      Nat.card (MonoidHom.range
          f4.hom.toAddMonoidHom.toMultiplicative) =
        Nat.card (MonoidHom.range
          q.hom.toAddMonoidHom.toMultiplicative) := by
    apply moduleCatRangeCard_eq_of_conjugate f4 q pA4 pB4
    exact periodicHomologyIsoEven_naturality
      σ (⟨2, rfl⟩ : Even 4) i hi
  have hf2q :
      Nat.card (MonoidHom.range
          f2.hom.toAddMonoidHom.toMultiplicative) =
        Nat.card (MonoidHom.range
          q.hom.toAddMonoidHom.toMultiplicative) := by
    apply moduleCatRangeCard_eq_of_conjugate f2 q pA2 pB2
    exact periodicHomologyIsoEven_naturality σ (by simp : Even 2) i hi
  have hrange :
      Nat.card (MonoidHom.range
          f4.hom.toAddMonoidHom.toMultiplicative) =
        Nat.card (MonoidHom.range
          f2.hom.toAddMonoidHom.toMultiplicative) :=
    hf4q.trans hf2q.symm
  have hperiodic :
      Nat.card (S.X₂.homology 3) *
          Nat.card (S.X₁.homology 2) *
          Nat.card (S.X₃.homology 4) =
        Nat.card (S.X₁.homology 3) *
          Nat.card (S.X₃.homology 3) *
          Nat.card (S.X₂.homology 4) := by
    rw [hB3, hA2, hC4, hA3, hC3, hB4, ← hrange]
    ac_rfl
  have hcB4 := moduleCat_card_eq_of_iso eB4
  have hcC4 := moduleCat_card_eq_of_iso eC4
  have hcA3 := moduleCat_card_eq_of_iso eA3
  have hcB3 := moduleCat_card_eq_of_iso eB3
  have hcC3 := moduleCat_card_eq_of_iso eC3
  have hcA2 := moduleCat_card_eq_of_iso eA2
  calc
    _ = Nat.card (S.X₂.homology 3) *
          Nat.card (S.X₁.homology 2) *
          Nat.card (S.X₃.homology 4) := by
      rw [hcB3, hcA2, hcC4]
    _ = Nat.card (S.X₁.homology 3) *
          Nat.card (S.X₃.homology 3) *
          Nat.card (S.X₂.homology 4) :=
      hperiodic
    _ = _ := by
      rw [hcA3, hcC3, hcB4]

end Herbrand
end ProfiniteCohomology

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_Core
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace CyclicCohomology

/-!
# Low-degree Herbrand quotients

The foundational constructions and their comparison with mathlib Tate
cohomology are split into focused modules.  This public module retains the
Herbrand quotient and its multiplicativity result.
-/

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA uB uC

variable {G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

/-- Herbrand-quotient theory the Herbrand-quotient definition: the Herbrand quotient of the actual
low-degree multiplicative Tate quotients.  The finiteness assumptions prevent
`Nat.card` from silently taking the value `0` on infinite quotients. -/
noncomputable def herbrandQuotient (σ : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)] : ℚ :=
  (Nat.card (HerbrandH0 G A) : ℚ) / (Nat.card (HerbrandHMinusOne G A σ) : ℚ)

/-- The Herbrand quotient is definitionally the ratio `#H⁰ / #H^{-1}`. -/
theorem herbrandQuotient_eq_card_ratio (σ : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)] :
    herbrandQuotient (G := G) (A := A) σ =
      (Nat.card (HerbrandH0 G A) : ℚ) /
        (Nat.card (HerbrandHMinusOne G A σ) : ℚ) :=
  rfl

/-- If the actual low-degree quotients have the same finite cardinality, then
the Herbrand quotient is `1`. -/
theorem herbrandQuotient_eq_one_of_card_eq (σ : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    (hcard : Nat.card (HerbrandH0 G A) = Nat.card (HerbrandHMinusOne G A σ)) :
    herbrandQuotient (G := G) (A := A) σ = 1 := by
  have hden : ((Nat.card (HerbrandHMinusOne G A σ) : ℚ) ≠ 0) :=
    Nat.cast_ne_zero.mpr (Finite.card_pos (α := HerbrandHMinusOne G A σ)).ne'
  unfold herbrandQuotient
  rw [hcard]
  exact div_self hden

/-- Herbrand-quotient theory Herbrand-quotient multiplicativity: the Herbrand quotient of a finite
cyclic module is `1`. -/
theorem herbrandQuotient_finite_module_eq_one
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    herbrandQuotient (G := G) (A := A) σ = 1 := by
  exact herbrandQuotient_eq_one_of_card_eq (G := G) (A := A) σ
    (herbrand_finite_module_card_eq (G := G) (A := A) σ hgen)

/-- Herbrand-quotient theory Herbrand-quotient multiplicativity: Herbrand quotient multiplicativity
for a short exact sequence of multiplicative `G`-modules, proved from the
standard two-periodic Tate complex and mathlib's homology long exact
sequence. -/
theorem herbrandQuotient_exact_multiplicative
    {G A B C : Type}
    [Group G] [Fintype G]
    [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C]
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c) (σ : G)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    herbrandQuotient (G := G) (A := B) σ =
      herbrandQuotient (G := G) (A := A) σ *
        herbrandQuotient (G := G) (A := C) σ := by
  have hcard :=
    herbrand_exact_cardinality_identity
      (G := G) (A := A) (B := B) (C := C)
      i j hi hj hker hinj hsurj σ hgen
  have hA :
      ((Nat.card (HerbrandHMinusOne G A σ) : ℚ) ≠ 0) :=
    Nat.cast_ne_zero.mpr
      (Finite.card_pos (α := HerbrandHMinusOne G A σ)).ne'
  have hB :
      ((Nat.card (HerbrandHMinusOne G B σ) : ℚ) ≠ 0) :=
    Nat.cast_ne_zero.mpr
      (Finite.card_pos (α := HerbrandHMinusOne G B σ)).ne'
  have hC :
      ((Nat.card (HerbrandHMinusOne G C σ) : ℚ) ≠ 0) :=
    Nat.cast_ne_zero.mpr
      (Finite.card_pos (α := HerbrandHMinusOne G C σ)).ne'
  unfold herbrandQuotient
  field_simp [hA, hB, hC]
  have hcardQ :
      (Nat.card (HerbrandH0 G B) : ℚ) *
          Nat.card (HerbrandHMinusOne G A σ) *
          Nat.card (HerbrandHMinusOne G C σ) =
        Nat.card (HerbrandH0 G A) *
          Nat.card (HerbrandH0 G C) *
          Nat.card (HerbrandHMinusOne G B σ) := by
    exact_mod_cast hcard
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcardQ

end Herbrand
end ProfiniteCohomology

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandFiniteness
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace CyclicCohomology

/-!
# Finiteness in the Herbrand exact hexagon

This file supplies the finiteness clause in Herbrand-quotient multiplicativity:
for a short exact sequence of modules over a finite cyclic group, if the Herbrand
quotients of any two terms are defined, then the quotient of the third term is
defined as well.
-/

noncomputable section

namespace ProfiniteCohomology
namespace Herbrand

open CategoryTheory

universe uG uA

variable {G A B C : Type}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

/-- The condition that the Herbrand quotient of `A` is defined. -/
def HerbrandQuotientDefined (G : Type uG) (A : Type uA)
    [Group G] [Fintype G] [CommGroup A] [MulDistribMulAction G A]
    (σ : G) : Prop :=
  Finite (HerbrandH0 G A) ∧ Finite (HerbrandHMinusOne G A σ)

noncomputable def tateHOneIsoHerbrandHMinusOne
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    tateCohomology (Rep.ofMulDistribMulAction G A) 1 ≅
      ModuleCat.of ℤ (Additive (HerbrandHMinusOne G A σ)) := by
  letI : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  let M := Rep.ofMulDistribMulAction G A
  exact
    (TateCohomology.isoGroupCohomology 1).app M ≪≫
      Rep.FiniteCyclicGroup.groupCohomologyIsoOdd
        M σ hgen 1 (by simp) ≪≫
      (TateCohomology.isoFiniteCyclicNegOne M σ hgen).symm ≪≫
      tateHMinusOneIsoHerbrandHMinusOne σ hgen

noncomputable def tateHMinusTwoIsoHerbrandH0
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    tateCohomology (Rep.ofMulDistribMulAction G A) (-2) ≅
      ModuleCat.of ℤ (Additive (HerbrandH0 G A)) := by
  classical
  letI : IsCyclic G := ⟨⟨σ, hgen⟩⟩
  letI : CommGroup G := IsCyclic.commGroup
  let M := Rep.ofMulDistribMulAction G A
  exact
    (TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app M ≪≫
      Rep.FiniteCyclicGroup.groupHomologyIsoOdd
        M σ hgen 1 (by simp) ≪≫
      (TateCohomology.isoFiniteCyclicZero M σ hgen).symm ≪≫
      tateH0IsoHerbrandH0

/-- Herbrand-quotient multiplicativity, finiteness transfer from the first and third terms to
the middle term. -/
theorem herbrandQuotientDefined_middle_of_left_right
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hA : HerbrandQuotientDefined G A σ)
    (hC : HerbrandQuotientDefined G C σ) :
    HerbrandQuotientDefined G B σ := by
  let : Finite (HerbrandH0 G A) := hA.1
  let : Finite (HerbrandHMinusOne G A σ) := hA.2
  let : Finite (HerbrandH0 G C) := hC.1
  let : Finite (HerbrandHMinusOne G C σ) := hC.2
  let S := equivariantShortComplex i j hi hj hker
  have hS : S.ShortExact :=
    equivariantShortComplex_shortExact
      i j hi hj hker hinj hsurj
  let : Finite (tateCohomology S.X₁ (-1)) :=
    finite_source_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := A) σ hgen)
  let : Finite (tateCohomology S.X₃ (-1)) :=
    finite_source_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := C) σ hgen)
  have hminusTate : Finite (tateCohomology S.X₂ (-1)) :=
    finite_middle_of_moduleCat_exact
      ((tateCohomologyFunctor (-1)).map S.f)
      ((tateCohomologyFunctor (-1)).map S.g)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        ((TateCohomology.map_tateComplexFunctor_shortExact hS)
          |>.homology_exact₂ (-1)))
  have hminus : Finite (HerbrandHMinusOne G B σ) := by
    let :
        Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction G B) (-1)) := by
      change Finite (tateCohomology S.X₂ (-1))
      exact hminusTate
    exact finite_target_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := B) σ hgen)
  let : Finite (tateCohomology S.X₁ 0) :=
    finite_source_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := A))
  let : Finite (tateCohomology S.X₃ 0) :=
    finite_source_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := C))
  have hzeroTate : Finite (tateCohomology S.X₂ 0) :=
    finite_middle_of_moduleCat_exact
      ((tateCohomologyFunctor 0).map S.f)
      ((tateCohomologyFunctor 0).map S.g)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        ((TateCohomology.map_tateComplexFunctor_shortExact hS)
          |>.homology_exact₂ 0))
  have hzero : Finite (HerbrandH0 G B) := by
    let :
        Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction G B) 0) := by
      change Finite (tateCohomology S.X₂ 0)
      exact hzeroTate
    exact finite_target_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := B))
  exact ⟨hzero, hminus⟩

/-- Herbrand-quotient multiplicativity, finiteness transfer from the first and middle terms to
the third term. -/
theorem herbrandQuotientDefined_right_of_left_middle
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hA : HerbrandQuotientDefined G A σ)
    (hB : HerbrandQuotientDefined G B σ) :
    HerbrandQuotientDefined G C σ := by
  let : Finite (HerbrandH0 G A) := hA.1
  let : Finite (HerbrandHMinusOne G A σ) := hA.2
  let : Finite (HerbrandH0 G B) := hB.1
  let : Finite (HerbrandHMinusOne G B σ) := hB.2
  let S := equivariantShortComplex i j hi hj hker
  have hS : S.ShortExact :=
    equivariantShortComplex_shortExact
      i j hi hj hker hinj hsurj
  let : Finite (tateCohomology S.X₂ (-1)) :=
    finite_source_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := B) σ hgen)
  have hA0 : Finite (tateCohomology S.X₁ 0) :=
    finite_source_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := A))
  let : Finite (tateCohomology S.X₁ ((-1) + 1)) := by
    norm_num
    exact hA0
  have hminusTate : Finite (tateCohomology S.X₃ (-1)) :=
    finite_middle_of_moduleCat_exact
      ((tateCohomologyFunctor (-1)).map S.g)
      (TateCohomology.δ hS (-1))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (TateCohomology.exact₃ hS (-1)))
  have hminus : Finite (HerbrandHMinusOne G C σ) := by
    let :
        Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction G C) (-1)) := by
      change Finite (tateCohomology S.X₃ (-1))
      exact hminusTate
    exact finite_target_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := C) σ hgen)
  let : Finite (tateCohomology S.X₂ 0) :=
    finite_source_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := B))
  have hA1 : Finite (tateCohomology S.X₁ 1) :=
    finite_source_of_moduleIso
      (tateHOneIsoHerbrandHMinusOne
        (G := G) (A := A) σ hgen)
  let : Finite (tateCohomology S.X₁ (0 + 1)) := by
    norm_num
    exact hA1
  have hzeroTate : Finite (tateCohomology S.X₃ 0) :=
    finite_middle_of_moduleCat_exact
      ((tateCohomologyFunctor 0).map S.g)
      (TateCohomology.δ hS 0)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (TateCohomology.exact₃ hS 0))
  have hzero : Finite (HerbrandH0 G C) := by
    let :
        Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction G C) 0) := by
      change Finite (tateCohomology S.X₃ 0)
      exact hzeroTate
    exact finite_target_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := C))
  exact ⟨hzero, hminus⟩

/-- Herbrand-quotient multiplicativity, finiteness transfer from the middle and third terms to
the first term. -/
theorem herbrandQuotientDefined_left_of_middle_right
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hB : HerbrandQuotientDefined G B σ)
    (hC : HerbrandQuotientDefined G C σ) :
    HerbrandQuotientDefined G A σ := by
  let : Finite (HerbrandH0 G B) := hB.1
  let : Finite (HerbrandHMinusOne G B σ) := hB.2
  let : Finite (HerbrandH0 G C) := hC.1
  let : Finite (HerbrandHMinusOne G C σ) := hC.2
  let S := equivariantShortComplex i j hi hj hker
  have hS : S.ShortExact :=
    equivariantShortComplex_shortExact
      i j hi hj hker hinj hsurj
  let : Finite (tateCohomology S.X₃ (-2)) :=
    finite_source_of_moduleIso
      (tateHMinusTwoIsoHerbrandH0
        (G := G) (A := C) σ hgen)
  have hBminus : Finite (tateCohomology S.X₂ (-1)) :=
    finite_source_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := B) σ hgen)
  let : Finite ((tateCohomologyFunctor ((-2) + 1)).obj S.X₂) := by
    norm_num
    exact hBminus
  have hminusTate :
      Finite (tateCohomology S.X₁ ((-2) + 1)) :=
    finite_middle_of_moduleCat_exact
      (TateCohomology.δ hS (-2))
      ((tateCohomologyFunctor ((-2) + 1)).map S.f)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (TateCohomology.exact₁ hS (-2)))
  have hminus : Finite (HerbrandHMinusOne G A σ) := by
    let :
        Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction G A) (-1)) := by
      norm_num at hminusTate ⊢
      exact hminusTate
    exact finite_target_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := A) σ hgen)
  let : Finite (tateCohomology S.X₃ (-1)) :=
    finite_source_of_moduleIso
      (tateHMinusOneIsoHerbrandHMinusOne
        (G := G) (A := C) σ hgen)
  let : Finite (tateCohomology S.X₂ 0) :=
    finite_source_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := B))
  have hzeroTate : Finite (tateCohomology S.X₁ 0) :=
    finite_middle_of_moduleCat_exact
      (TateCohomology.δ hS (-1))
      ((tateCohomologyFunctor 0).map S.f)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (TateCohomology.exact₁ hS (-1)))
  have hzero : Finite (HerbrandH0 G A) := by
    let :
        Finite
          (tateCohomology
            (Rep.ofMulDistribMulAction G A) 0) := by
      change Finite (tateCohomology S.X₁ 0)
      exact hzeroTate
    exact finite_target_of_moduleIso
      (tateH0IsoHerbrandH0 (G := G) (A := A))
  exact ⟨hzero, hminus⟩

/-- Herbrand-quotient multiplicativity, Herbrand-quotient multiplicativity once the three
quotients are defined. -/
theorem herbrandQuotient_multiplicative_of_shortExact
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    herbrandQuotient (G := G) (A := B) σ =
      herbrandQuotient (G := G) (A := A) σ *
        herbrandQuotient (G := G) (A := C) σ :=
  herbrandQuotient_exact_multiplicative
    i j hi hj hker hinj hsurj σ hgen

/-- Herbrand-quotient multiplicativity, the finite-module case. -/
theorem herbrandQuotient_eq_one_of_finite_module
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    herbrandQuotient (G := G) (A := A) σ = 1 :=
  herbrandQuotient_finite_module_eq_one σ hgen

end Herbrand
end ProfiniteCohomology

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_HerbrandLowDegree_EquivariantEquiv
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Low-degree Tate cohomology under equivariant equivalences

An equivariant multiplicative equivalence identifies fixed elements, norm
kernels, norm images, and augmentation images.  Consequently it induces
equivalences on the concrete low-degree Tate cohomology groups and preserves
the Herbrand quotient.

These transport results let calculations made on field units or local
coordinates be applied to their actual images inside idele groups without
introducing comparison assumptions.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA uB

variable {G : Type uG} {A : Type uA} {B : Type uB}
    [Group G] [Fintype G]
    [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A]
    [MulDistribMulAction G B]

/-- An equivariant multiplicative equivalence commutes with the finite
group norm. -/
theorem equivariantMulEquiv_map_tateNorm
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    (a : A) :
    e (tateNorm G A a) =
      tateNorm G B (e a) := by
  simpa using
    map_tateNorm
      (G := G) (A := A) (B := B)
      e.toMonoidHom
      (fun g x ↦ by simpa using he g x) a

omit [Fintype G] in
/-- An equivariant multiplicative equivalence commutes with the
augmentation operator. -/
theorem equivariantMulEquiv_map_sigmaMinusOne
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    (σ : G) (a : A) :
    e (sigmaMinusOne G A σ a) =
      sigmaMinusOne G B σ (e a) := by
  simpa using
    map_sigmaMinusOne
      (G := G) (A := A) (B := B)
      e.toMonoidHom
      (fun g x ↦ by simpa using he g x) σ a

/-- An equivariant multiplicative equivalence restricted to fixed
subgroups. -/
noncomputable def fixedSubgroupEquivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a) :
    fixedSubgroup G A ≃* fixedSubgroup G B where
  toFun a :=
    ⟨e a.1, fun g ↦ by
      rw [← he g a.1, a.2 g]⟩
  invFun b :=
    ⟨e.symm b.1, fun g ↦ by
      rw [← mulEquiv_symm_commutes_smul e he, b.2 g]⟩
  left_inv a := by
    apply Subtype.ext
    exact e.symm_apply_apply a.1
  right_inv b := by
    apply Subtype.ext
    exact e.apply_symm_apply b.1
  map_mul' _ _ := by
    apply Subtype.ext
    exact e.map_mul _ _

/-- An equivariant multiplicative equivalence restricted to norm
kernels. -/
noncomputable def normKernelEquivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a) :
    normKernelSubgroup G A ≃*
      normKernelSubgroup G B where
  toFun a :=
    ⟨e a.1, by
      change tateNorm G B (e a.1) = 1
      calc
        tateNorm G B (e a.1) =
            e (tateNorm G A a.1) :=
          (equivariantMulEquiv_map_tateNorm
            e he a.1).symm
        _ = e 1 := congrArg e a.2
        _ = 1 := e.map_one⟩
  invFun b :=
    ⟨e.symm b.1, by
      change tateNorm G A (e.symm b.1) = 1
      apply e.injective
      calc
        e (tateNorm G A (e.symm b.1)) =
            tateNorm G B (e (e.symm b.1)) :=
          equivariantMulEquiv_map_tateNorm
            e he (e.symm b.1)
        _ = tateNorm G B b.1 := by
          rw [e.apply_symm_apply]
        _ = 1 := b.2
        _ = e 1 := e.map_one.symm⟩
  left_inv a := by
    apply Subtype.ext
    exact e.symm_apply_apply a.1
  right_inv b := by
    apply Subtype.ext
    exact e.apply_symm_apply b.1
  map_mul' _ _ := by
    apply Subtype.ext
    exact e.map_mul _ _

/-- An equivariant multiplicative equivalence induces an equivalence on
degree-zero Tate cohomology. -/
noncomputable def herbrandH0EquivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a) :
    HerbrandH0 G A ≃* HerbrandH0 G B := by
  let f := fixedSubgroupEquivariantMulEquiv e he
  let N :=
    (tateNormSubgroup G A).subgroupOf
      (fixedSubgroup G A)
  let M :=
    (tateNormSubgroup G B).subgroupOf
      (fixedSubgroup G B)
  exact quotientMulEquivOfSplit N M
    f.toMonoidHom f.symm.toMonoidHom
    (fun y ↦ f.apply_symm_apply y)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rcases hx with ⟨a, ha⟩
      refine ⟨e a, ?_⟩
      change tateNorm G B (e a) = e x.1
      calc
        tateNorm G B (e a) =
            e (tateNorm G A a) :=
          (equivariantMulEquiv_map_tateNorm
            e he a).symm
        _ = e x.1 := congrArg e ha)
    (fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      rcases hy with ⟨b, hb⟩
      refine ⟨e.symm b, ?_⟩
      apply e.injective
      change
        e (tateNorm G A (e.symm b)) =
          e (e.symm y.1)
      calc
        e (tateNorm G A (e.symm b)) =
            tateNorm G B (e (e.symm b)) :=
          equivariantMulEquiv_map_tateNorm
            e he (e.symm b)
        _ = tateNorm G B b := by
          rw [e.apply_symm_apply]
        _ = y.1 := hb
        _ = e (e.symm y.1) :=
          (e.apply_symm_apply y.1).symm)
    (fun x hx ↦ by
      have hx1 : x = 1 := by
        apply f.injective
        simpa [f] using hx
      rw [hx1]
      exact N.one_mem)

@[simp]
theorem herbrandH0EquivariantMulEquiv_mk
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    (a : fixedSubgroup G A) :
    herbrandH0EquivariantMulEquiv e he (HerbrandH0.mk a) =
      HerbrandH0.mk (fixedSubgroupEquivariantMulEquiv e he a) := by
  rfl

/-- An equivariant multiplicative equivalence induces an equivalence on
degree-minus-one Tate cohomology. -/
noncomputable def herbrandHMinusOneEquivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    (σ : G) :
    HerbrandHMinusOne G A σ ≃*
      HerbrandHMinusOne G B σ := by
  let f := normKernelEquivariantMulEquiv e he
  let N :=
    (augmentationSubgroup G A σ).subgroupOf
      (normKernelSubgroup G A)
  let M :=
    (augmentationSubgroup G B σ).subgroupOf
      (normKernelSubgroup G B)
  exact quotientMulEquivOfSplit N M
    f.toMonoidHom f.symm.toMonoidHom
    (fun y ↦ f.apply_symm_apply y)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rcases hx with ⟨a, ha⟩
      refine ⟨e a, ?_⟩
      change sigmaMinusOne G B σ (e a) = e x.1
      calc
        sigmaMinusOne G B σ (e a) =
            e (sigmaMinusOne G A σ a) :=
          (equivariantMulEquiv_map_sigmaMinusOne
            e he σ a).symm
        _ = e x.1 := congrArg e ha)
    (fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      rcases hy with ⟨b, hb⟩
      refine ⟨e.symm b, ?_⟩
      apply e.injective
      change
        e (sigmaMinusOne G A σ (e.symm b)) =
          e (e.symm y.1)
      calc
        e (sigmaMinusOne G A σ (e.symm b)) =
            sigmaMinusOne G B σ (e (e.symm b)) :=
          equivariantMulEquiv_map_sigmaMinusOne
            e he σ (e.symm b)
        _ = sigmaMinusOne G B σ b := by
          rw [e.apply_symm_apply]
        _ = y.1 := hb
        _ = e (e.symm y.1) :=
          (e.apply_symm_apply y.1).symm)
    (fun x hx ↦ by
      have hx1 : x = 1 := by
        apply f.injective
        simpa [f] using hx
      rw [hx1]
      exact N.one_mem)

/-- Finiteness of `H⁰` transports through an equivariant
multiplicative equivalence. -/
theorem herbrandH0Finite_of_equivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    [Finite (HerbrandH0 G A)] :
    Finite (HerbrandH0 G B) :=
  Finite.of_equiv
    (HerbrandH0 G A)
    (herbrandH0EquivariantMulEquiv e he).toEquiv

/-- Finiteness of `H⁻¹` transports through an equivariant
multiplicative equivalence. -/
theorem herbrandHMinusOneFinite_of_equivariantMulEquiv
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A),
      e (g • a) = g • e a)
    (σ : G)
    [Finite (HerbrandHMinusOne G A σ)] :
    Finite (HerbrandHMinusOne G B σ) :=
  Finite.of_equiv
    (HerbrandHMinusOne G A σ)
    (herbrandHMinusOneEquivariantMulEquiv
      e he σ).toEquiv

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_Permutation_Module
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace
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

section TransitivePermutationLattice

variable {G : Type uG} [Group G] [Fintype G]

/-- A transitive permutation lattice in orbit coordinates: the stabilizer
`H` acts trivially on `ℤ`, and induction gives the integer-valued
functions on the corresponding orbit. -/
abbrev TransitivePermutationLattice
    (H : Subgroup G)
    [MulDistribMulAction H (Multiplicative ℤ)] :=
  InducedModule (G := G)
    (B := Multiplicative ℤ) H

end TransitivePermutationLattice

section PermutationLatticeOrbits

variable {G : Type uG} [Group G] [Fintype G]
variable {ι : Type uι} [Fintype ι]

/-- A finite permutation lattice presented by chosen orbit representatives:
`H i` is the stabilizer of the representative of orbit `i`. -/
abbrev PermutationLatticeOrbitFamily
    (H : ι → Subgroup G)
    [∀ i,
      MulDistribMulAction (H i)
        (Multiplicative ℤ)] :=
  ∀ i, TransitivePermutationLattice (H i)

end PermutationLatticeOrbits

section FiniteIndexStableSubgroupFiniteness

variable {G A : Type}
    [Group G] [CommGroup A]
    [MulDistribMulAction G A]

variable [Fintype G]

/-- If the Herbrand quotient is defined on a stable finite-index
subgroup, then it is defined on the ambient module.  Finiteness of the
quotient supplies the third term of the exact-sequence argument. -/
theorem finiteIndexStableSubgroup_ambientHerbrandQuotientDefined
    (B : Subgroup A)
    (hstable : ∀ (g : G) (x : A),
      x ∈ B → g • x ∈ B)
    (σ : G)
    (hgen : ∀ g : G,
      g ∈ Subgroup.zpowers σ)
    (hB :
      letI :=
        stableSubgroupMulDistribMulAction
          B hstable
      HerbrandQuotientDefined G B σ)
    [Finite (A ⧸ B)] :
    letI _subgroupAction :=
      stableSubgroupMulDistribMulAction
        B hstable
    letI _quotientAction :=
      stableQuotientMulDistribMulAction
        B hstable
    HerbrandQuotientDefined G A σ := by
  let subgroupAction :=
    stableSubgroupMulDistribMulAction
      B hstable
  let quotientAction :=
    stableQuotientMulDistribMulAction
      B hstable
  let hQ :
      HerbrandQuotientDefined
        G (A ⧸ B) σ :=
    ⟨inferInstance, inferInstance⟩
  exact
    herbrandQuotientDefined_middle_of_left_right
      B.subtype (QuotientGroup.mk' B)
      (stableSubgroup_subtype_equivariant
        B hstable)
      (stableSubgroup_quotientMap_equivariant
        B hstable)
      (stableSubgroup_quotientMap_exact B)
      B.subtype_injective
      (QuotientGroup.mk'_surjective B)
      σ hgen hB hQ

end FiniteIndexStableSubgroupFiniteness

end CyclicCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_FieldNorm
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
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

/-- The norm subgroup of `Kˣ` attached to `L/K`. -/
noncomputable def fieldNormSubgroup : Subgroup Kˣ :=
  (normUnits K L).range

/-- First-isomorphism-theorem form for the field norm on unit groups:
`Lˣ / ker(N)` is the norm subgroup of `Kˣ`. -/
noncomputable def fieldNormUnitsQuotientKerEquivFieldNormSubgroup :
    Lˣ ⧸ MonoidHom.ker (normUnits K L) ≃*
      fieldNormSubgroup K L :=
  QuotientGroup.quotientKerEquivRange (normUnits K L)

end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_TateH0_NormImage
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace
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

/-- The standard degree-zero Tate object, expressed as the arithmetic quotient
of invariant units by the representation norm image. -/
def tateUnitsH0IsoInvariantsQuotient (K L : Type)
    [Field K] [Field L] [Algebra K L] [Fintype Gal(L/K)] :
    tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0 ≅
      ModuleCat.of ℤ
        (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) := by
  let A := Rep.ofAlgebraAutOnUnits K L
  let S : ShortComplex (ModuleCat ℤ) :=
    .mk A.norm.toModuleCatHom (groupCohomology.d₀₁ A)
      (Rep.norm_comp_d_eq_zero A)
  have hker :
      LinearMap.ker S.g.hom = unitsInvariantSubmodule K L := by
    exact groupCohomology.d₀₁_ker_eq_invariants A
  let eK : LinearMap.ker S.g.hom ≃ₗ[ℤ] unitsInvariantSubmodule K L :=
    LinearEquiv.ofEq _ _ hker
  have hboundary :
      (LinearMap.range S.moduleCatToCycles).map eK.toLinearMap =
        unitsTateH0NormSubmodule K L := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      rfl
    · rintro ⟨z, rfl⟩
      refine ⟨S.moduleCatToCycles z, ⟨z, rfl⟩, ?_⟩
      apply Subtype.ext
      rfl
  let eQ :
      S.moduleCatLeftHomologyData.H ≅
        ModuleCat.of ℤ
          (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) :=
    (Submodule.Quotient.equiv _ _ eK hboundary).toModuleIso
  exact TateCohomology.isoZeroBoundary A ≪≫
    S.moduleCatHomologyIso ≪≫ eQ

/-- The invariant-unit equivalence sends the additive unit norm to the field norm. -/
lemma invariantsUnitsAddEquivBaseUnits_unitsNorm_apply (K L : Type)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (x : Lˣ) :
    (letI := AlgEquiv.fintype K L
     invariantsUnitsAddEquivBaseUnits K L
        (unitsNormToInvariantsLinearMap K L (Additive.ofMul x))) =
      Additive.ofMul (normUnits K L x) := by
  let := AlgEquiv.fintype K L
  apply Additive.toMul.injective
  ext
  apply FaithfulSMul.algebraMap_injective K L
  rw [invariantsUnitsAddEquivBaseUnits_spec]
  exact (unitsNormLinearMap_apply_val K L x).trans (by rfl)

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_PrincipalUnits_QuotientReps
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsConcreteEquiv_mk _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsLift_mk _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `CyclicCohomology.Herbrand.PrincipalUnits.QuotientReps` Lean module. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Integer units modulo the `n`-th principal-unit subgroup.

This named type is the representation boundary: downstream code uses its
quotient interface rather than unfolding the concrete quotient. -/
def IntegerUnitsModPrincipalUnitsAtLevel
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) : Type u :=
  𝒪[K]ˣ ⧸ principalUnits K n

/-- Integer units modulo level principal units form a commutative group. -/
instance integerUnitsModPrincipalUnitsAtLevelCommGroup
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    CommGroup (IntegerUnitsModPrincipalUnitsAtLevel K n) := by
  change CommGroup (𝒪[K]ˣ ⧸ principalUnits K n)
  infer_instance

/-- Explicit comparison with the concrete quotient implementation. -/
def integerUnitsModPrincipalUnitsAtLevelConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    IntegerUnitsModPrincipalUnitsAtLevel K n ≃*
      (𝒪[K]ˣ ⧸ principalUnits K n) := by
  change (𝒪[K]ˣ ⧸ principalUnits K n) ≃*
    (𝒪[K]ˣ ⧸ principalUnits K n)
  exact MulEquiv.refl _

/-- The canonical class of an integer unit modulo `U_K^n`. -/
def integerUnitsModPrincipalUnitsAtLevelMk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    𝒪[K]ˣ →* IntegerUnitsModPrincipalUnitsAtLevel K n := by
  change 𝒪[K]ˣ →* (𝒪[K]ˣ ⧸ principalUnits K n)
  exact QuotientGroup.mk' (principalUnits K n)

/-- The concrete quotient equivalence sends a unit to its canonical class. -/
@[simp]
theorem integerUnitsModPrincipalUnitsAtLevelConcreteEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelConcreteEquiv K n
        (integerUnitsModPrincipalUnitsAtLevelMk K n x) =
      QuotientGroup.mk x :=
  rfl

/-- Eliminate a level quotient through its canonical representatives. -/
protected theorem IntegerUnitsModPrincipalUnitsAtLevel.inductionOn
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : IntegerUnitsModPrincipalUnitsAtLevel K n → Prop}
    (q : IntegerUnitsModPrincipalUnitsAtLevel K n)
    (h : ∀ x : 𝒪[K]ˣ,
      motive (integerUnitsModPrincipalUnitsAtLevelMk K n x)) :
    motive q := by
  change motive (show 𝒪[K]ˣ ⧸ principalUnits K n from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

end

end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_Herbrand_NormalBasisLattice
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction_smul _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe _root_.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-! Provides the public normal-basis lattice declarations used in Herbrand computations. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable [ValuativeRel K]

/-- Public characterization of the chosen normal-basis lattice as the span of
the chosen generator's Galois orbit. -/
theorem chosenNormalBasisIntegerLattice_eq_span :
    chosenNormalBasisIntegerLattice K L =
      Submodule.span 𝒪[K]
        (Set.range (fun σ : Gal(L / K) =>
          σ (IsGalois.normalBasis K L (1 : Gal(L / K))))) :=
  rfl

/-- After extending scalars back to `K`, the normal-basis lattice spans all of
`L`. -/
theorem chosenNormalBasisIntegerLattice_field_span_eq_top :
    Submodule.span K ((chosenNormalBasisIntegerLattice K L : Submodule 𝒪[K] L) : Set L) =
      ⊤ := by
  refine le_antisymm le_top ?_
  rw [← normalBasisConjugates_span_eq_top (K := K) (L := L)]
  refine Submodule.span_mono ?_
  intro x hx
  exact Submodule.subset_span hx

/-- The normal-basis lattice `M` is finitely generated over `𝒪_K`. -/
theorem chosenNormalBasisIntegerLattice_fg :
    (chosenNormalBasisIntegerLattice K L).FG := by
  dsimp [chosenNormalBasisIntegerLattice]
  exact Submodule.fg_span (Set.finite_range _)

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Increasing the base-uniformizer exponent preserves membership after
denominator clearing. -/
theorem chosenBaseUniformizerPow_mul_mem_mono
    {M : Submodule 𝒪[K] L} {m n : Nat} {x : L} (hmn : m ≤ n)
    (hx : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * x ∈ M) :
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * x ∈ M := by
  rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
  rw [hd]
  have hscaled :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) *
          (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * x) ∈ M := by
    simpa [Algebra.smul_def, mul_assoc] using
      M.smul_mem (chosenIntegerRingUniformizer K ^ d) hx
  simpa [pow_add, map_mul, mul_assoc, mul_comm, mul_left_comm] using hscaled

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The lattices `π_K^n N` form a descending filtration. -/
theorem chosenBaseUniformizerPowSubmodule_antitone
    (N : Submodule 𝒪[K] L) {m n : Nat} (hmn : m ≤ n) :
    chosenBaseUniformizerPowSubmodule K L n N ≤
      chosenBaseUniformizerPowSubmodule K L m N := by
  intro x hx
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n N x).1 hx with
    ⟨y, hyN, rfl⟩
  rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
  refine (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) m N _).2 ?_
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) * y, ?_, ?_⟩
  · simpa [Algebra.smul_def, mul_assoc] using
      N.smul_mem (chosenIntegerRingUniformizer K ^ d) hyN
  · simp [hd, pow_add, map_mul, mul_comm, mul_left_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Successive chosen uniformizer-power submodules form a descending chain. -/
theorem chosenBaseUniformizerPowSubmodule_succ_le
    (n : Nat) (N : Submodule 𝒪[K] L) :
    chosenBaseUniformizerPowSubmodule K L (n + 1) N ≤
      chosenBaseUniformizerPowSubmodule K L n N :=
  chosenBaseUniformizerPowSubmodule_antitone (K := K) (L := L) N (Nat.le_succ n)

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Powers of an element stay in a multiplicatively closed additive lattice.

This is the finite algebraic input to the geometric-series inverse argument; completeness supplies the limit of these finite approximations. -/
theorem submodule_pow_succ_mem_of_mul_closed
    {E : Submodule 𝒪[K] L}
    (hmul : ∀ x : L, x ∈ E → ∀ y : L, y ∈ E → x * y ∈ E)
    {x : L} (hx : x ∈ E) :
    ∀ m : Nat, x ^ (m + 1) ∈ E := by
  intro m
  induction m with
  | zero =>
      simpa using hx
  | succ m ih =>
      have hmul_mem : x ^ (m + 1) * x ∈ E := hmul (x ^ (m + 1)) ih x hx
      simpa [pow_add, mul_assoc, mul_comm, mul_left_comm] using hmul_mem

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The zeroth inverse-correction partial sum is its initial term. -/
@[simp]
theorem inverseCorrectionPartialSum_zero (x : L) :
    inverseCorrectionPartialSum (L := L) x 0 = 0 := by
  simp [inverseCorrectionPartialSum]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Expands the inverse-correction partial sum at a successor index. -/
theorem inverseCorrectionPartialSum_succ (x : L) (d : Nat) :
    inverseCorrectionPartialSum (L := L) x (d + 1) =
      inverseCorrectionPartialSum (L := L) x d + (-x) ^ (d + 1) := by
  simp [inverseCorrectionPartialSum, Finset.sum_range_succ]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Adding `1` turns the inverse-correction sum into the usual finite
geometric sum with ratio `-x`. -/
theorem one_add_inverseCorrectionPartialSum_eq_geom_sum (x : L) (d : Nat) :
    1 + inverseCorrectionPartialSum (L := L) x d =
      (Finset.range (d + 1)).sum fun i => (-x) ^ i := by
  induction d with
  | zero =>
      simp [inverseCorrectionPartialSum]
  | succ d ih =>
      rw [inverseCorrectionPartialSum_succ, Finset.sum_range_succ, ← ih]
      simp [add_assoc]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Finite geometric inverse identity for the approximants to `(1+x)⁻¹`. -/
theorem one_add_mul_one_add_inverseCorrectionPartialSum (x : L) (d : Nat) :
    (1 + x) * (1 + inverseCorrectionPartialSum (L := L) x d) =
      1 - (-x) ^ (d + 1) := by
  rw [one_add_inverseCorrectionPartialSum_eq_geom_sum]
  simpa [sub_neg_eq_add] using
    (mul_neg_geom_sum (x := (-x : L)) (n := d + 1))

omit [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Inverse-correction partial sums remain in any additive set closed under multiplication. -/
theorem inverseCorrectionPartialSum_mem_of_mul_closed
    {E : Submodule 𝒪[K] L}
    (hmul : ∀ x : L, x ∈ E → ∀ y : L, y ∈ E → x * y ∈ E)
    {x : L} (hx : x ∈ E) (d : Nat) :
    inverseCorrectionPartialSum (L := L) x d ∈ E := by
  unfold inverseCorrectionPartialSum
  refine Submodule.sum_mem E ?_
  intro i _
  exact submodule_pow_succ_mem_of_mul_closed (K := K) (L := L)
    hmul (E.neg_mem hx) i

variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Under a valuation extension, the chosen base prime element maps into the
maximal ideal of the extension valuation ring. -/
theorem integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtension :
    integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K) ∈
      (𝓂[L] : Ideal 𝒪[L]) := by
  have hπK :
      chosenIntegerRingUniformizer K ∈ (𝓂[K] : Ideal 𝒪[K]) := by
    rw [chosenIntegerRingUniformizer_maximalIdeal_eq K]
    exact Ideal.subset_span (Set.mem_singleton (chosenIntegerRingUniformizer K))
  exact (Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff
    (ValuativeRel.valuation K) (ValuativeRel.valuation L)).2 hπK

/-- The valuation integer ring of `L`, viewed as an `𝒪_K`-submodule of `L`.
This is the `𝒪_L` lattice compared with the normal-basis lattice. -/
def integerRingFieldSubmodule : Submodule 𝒪[K] L where
  carrier := {x | x ∈ 𝒪[L]}
  zero_mem' := by
    change (0 : L) ∈ 𝒪[L]
    exact zero_mem _
  add_mem' := by
    intro x y hx hy
    change x + y ∈ 𝒪[L]
    exact add_mem hx hy
  smul_mem' := by
    intro a x hx
    change a • x ∈ 𝒪[L]
    rw [Algebra.smul_def]
    have ha : algebraMap 𝒪[K] L a ∈ 𝒪[L] := by
      change algebraMap K L (a : K) ∈ 𝒪[L]
      exact (integerRingMapOfValuationExtension K L a).2
    exact mul_mem ha hx

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- Characterizes the field elements lying in the embedded integer-ring submodule. -/
@[simp]
theorem mem_integerRingFieldSubmodule_iff (x : L) :
    x ∈ integerRingFieldSubmodule K L ↔ x ∈ 𝒪[L] :=
  Iff.rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A base-uniformizer multiple of `𝒪_L` is a zero-neighborhood in `L`. -/
theorem chosenBaseUniformizerPow_integerRingFieldSubmodule_mem_nhds_zero
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (m : Nat) :
    ((chosenBaseUniformizerPowSubmodule K L m
      (integerRingFieldSubmodule K L) : Set L)) ∈ nhds (0 : L) := by
  let a : L := algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m)
  have hπ_ne : (chosenIntegerRingUniformizer K ^ m : 𝒪[K]) ≠ 0 :=
    pow_ne_zero m (chosenIntegerRingUniformizer_irreducible K).ne_zero
  have ha_ne : a ≠ 0 := by
    dsimp [a]
    change algebraMap K L ((chosenIntegerRingUniformizer K ^ m : 𝒪[K]) : K) ≠ 0
    apply (map_ne_zero (algebraMap K L)).2
    intro h
    exact hπ_ne ((IsFractionRing.injective 𝒪[K] K) h)
  have ha_val_pos : 0 < ValuativeRel.valuation L a := by
    exact (ValuativeRel.valuation L).pos_iff.2 ha_ne
  let γ : (ValuativeRel.ValueGroupWithZero L)ˣ :=
    Units.mk0 (ValuativeRel.valuation L a) (ne_of_gt ha_val_pos)
  refine Filter.mem_of_superset
    ((IsValuativeTopology.hasBasis_nhds_zero L).mem_of_mem (i := γ) trivial) ?_
  intro x hx
  refine (mem_chosenBaseUniformizerPowSubmodule_iff
    (K := K) (L := L) m (integerRingFieldSubmodule K L) x).2 ?_
  refine ⟨a⁻¹ * x, ?_, ?_⟩
  · rw [mem_integerRingFieldSubmodule_iff]
    rw [Valuation.mem_integer_iff]
    have hxle : ValuativeRel.valuation L x ≤ ValuativeRel.valuation L a := le_of_lt hx
    have hval :
        ValuativeRel.valuation L (a⁻¹ * x) =
          (ValuativeRel.valuation L a)⁻¹ * ValuativeRel.valuation L x := by
      simp [map_mul]
    rw [hval]
    exact (inv_mul_le_one₀ ha_val_pos).2 hxle
  · change a * (a⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ ha_ne, one_mul]

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- The maximal ideal `𝓂_L`, viewed inside `L` as an `𝒪_K`-submodule. -/
def maximalIdealFieldSubmodule : Submodule 𝒪[K] L where
  carrier := {x | ∃ a : 𝒪[L], a ∈ (𝓂[L] : Ideal 𝒪[L]) ∧ (a : L) = x}
  zero_mem' := by
    refine ⟨0, by simp, by simp⟩
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    refine ⟨a + b, (𝓂[L] : Ideal 𝒪[L]).add_mem ha hb, by simp⟩
  smul_mem' := by
    intro c x hx
    rcases hx with ⟨a, ha, rfl⟩
    refine ⟨integerRingMapOfValuationExtension K L c * a, ?_, ?_⟩
    · exact Ideal.mul_mem_left _ (integerRingMapOfValuationExtension K L c) ha
    · change ((integerRingMapOfValuationExtension K L c : 𝒪[L]) : L) * (a : L) =
        c • (a : L)
      rw [Algebra.smul_def]
      congr 1

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- Characterizes membership in the field submodule induced by the maximal ideal. -/
@[simp]
theorem mem_maximalIdealFieldSubmodule_iff (x : L) :
    x ∈ maximalIdealFieldSubmodule K L ↔
      ∃ a : 𝒪[L], a ∈ (𝓂[L] : Ideal 𝒪[L]) ∧ (a : L) = x :=
  Iff.rfl

omit [FiniteDimensional K L] [IsGalois K L] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- Multiplying an existing containment by a further base-uniformizer power. -/
theorem chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_le
    {N M : Submodule 𝒪[K] L} {a n : Nat}
    (h : chosenBaseUniformizerPowSubmodule K L a N ≤ M) :
    chosenBaseUniformizerPowSubmodule K L (a + n) N ≤
      chosenBaseUniformizerPowSubmodule K L n M := by
  intro x hx
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) (a + n) N x).1 hx with
    ⟨y, hyN, rfl⟩
  refine (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) n M _).2 ?_
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ a) * y, ?_, ?_⟩
  · exact h ((mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) a N _).2
      ⟨y, hyN, rfl⟩)
  · simp [pow_add, map_mul, mul_assoc, mul_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- If `π_K^b N` is integral, then `π_K^(b+1) N` lands in the maximal ideal of
`𝒪_L`. -/
theorem chosenBaseUniformizerPowSubmodule_succ_le_maximalIdealFieldSubmodule_of_le_integerRingFieldSubmodule
    {N : Submodule 𝒪[K] L} {b : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b N ≤ integerRingFieldSubmodule K L) :
    chosenBaseUniformizerPowSubmodule K L (b + 1) N ≤
      maximalIdealFieldSubmodule K L := by
  intro x hx
  rcases (mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) (b + 1) N x).1 hx with
    ⟨y, hyN, rfl⟩
  have hby :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ b) * y ∈
        integerRingFieldSubmodule K L := by
    exact hb ((mem_chosenBaseUniformizerPowSubmodule_iff (K := K) (L := L) b N _).2
      ⟨y, hyN, rfl⟩)
  have hby_int :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ b) * y ∈ 𝒪[L] :=
    (mem_integerRingFieldSubmodule_iff (K := K) (L := L)
      (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ b) * y)).1 hby
  let z : 𝒪[L] :=
    ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ b) * y, hby_int⟩
  let πL : 𝒪[L] :=
    integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
  have hπL : πL ∈ (𝓂[L] : Ideal 𝒪[L]) := by
    dsimp [πL]
    exact integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtension
      (K := K) (L := L)
  refine (mem_maximalIdealFieldSubmodule_iff (K := K) (L := L) _).2 ?_
  refine ⟨πL * z, Ideal.mul_mem_right z _ hπL, ?_⟩
  dsimp [πL, z]
  change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K) *
      (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ b) * y) =
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (b + 1)) * y
  simp [pow_add, map_mul, mul_comm, mul_left_comm]

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The identity belongs to the chosen normal-basis principal-unit set. -/
theorem chosenNormalBasisPrincipalUnitSet_one_mem (n : Nat) :
    (1 : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff]
  simp

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The chosen normal-basis principal-unit set is closed under multiplication. -/
theorem chosenNormalBasisPrincipalUnitSet_mul_mem {n : Nat}
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L))
    {u v : 𝒪[L]ˣ}
    (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (hv : v ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    u * v ∈ chosenNormalBasisPrincipalUnitSet K L n := by
  let E : Submodule 𝒪[K] L :=
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
  let x : L := ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  let y : L := ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  have hx : x ∈ E := hu
  have hy : y ∈ E := hv
  have hxy : x * y ∈ E := hmul x hx y hy
  have hsum : x * y + x + y ∈ E := by
    exact E.add_mem (E.add_mem hxy hx) hy
  have hunit :
      ((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) = x * y + x + y := by
    have h :=
      congrArg (fun z : 𝒪[L] => (z : L)) (unit_mul_sub_one_eq L u v)
    simpa [x, y, map_add, map_mul, mul_assoc, mul_comm, mul_left_comm,
      add_assoc, add_comm, add_left_comm] using h
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff]
  rw [hunit]
  exact hsum

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The inverse-correction partial sums remain in the lattice underlying the principal-unit set. -/
theorem chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialSum_mem {n : Nat}
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L))
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) (d : Nat) :
    inverseCorrectionPartialSum (L := L)
        ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d ∈
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) :=
  inverseCorrectionPartialSum_mem_of_mul_closed (K := K) (L := L) hmul hu d

end
end CyclicCohomology

universe u

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-! ### Additive quotient boundary -/

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The principal-unit lattice carriers form a descending filtration. -/
theorem chosenNormalBasisPrincipalUnitSet_succ_subset (n : Nat) :
    chosenNormalBasisPrincipalUnitSet K L (n + 1) ⊆
      chosenNormalBasisPrincipalUnitSet K L n := by
  intro u hu
  rw [mem_chosenNormalBasisPrincipalUnitSet_iff] at hu ⊢
  exact chosenBaseUniformizerPowSubmodule_succ_le
    (K := K) (L := L) n (chosenNormalBasisIntegerLattice K L) hu

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- Eliminate a chosen normal-basis lattice quotient through arbitrary
representatives and its canonical class map. -/
protected theorem chosenNormalBasisLatticeSuccQuot.inductionOn
    (n : Nat)
    {motive : chosenNormalBasisLatticeSuccQuot K L n → Prop}
    (q : chosenNormalBasisLatticeSuccQuot K L n)
    (h : ∀ x :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L),
      motive (chosenNormalBasisLatticeSuccQuotMk K L n x)) :
    motive q := by
  change motive
    (show
      (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n from q)
  exact
    Submodule.Quotient.induction_on
      (chosenNormalBasisLatticeSuccSubmodule K L n) q h

omit [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- A lattice representative gives zero in the successive quotient exactly
when it lies at the next level. -/
theorem chosenNormalBasisLatticeSuccQuotMk_eq_zero_iff (n : Nat)
    (x : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :
    chosenNormalBasisLatticeSuccQuotMk K L n x = 0 ↔
      (x : L) ∈ chosenBaseUniformizerPowSubmodule K L (n + 1)
        (chosenNormalBasisIntegerLattice K L) := by
  change
    (Submodule.Quotient.mk x :
      (chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) ⧸
        chosenNormalBasisLatticeSuccSubmodule K L n) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/-- The additive quotient class of `u - 1` for `u ∈ V^n`. -/
def chosenNormalBasisPrincipalUnitLatticeClass (n : Nat)
    (u : 𝒪[L]ˣ) (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisLatticeSuccQuot K L n :=
  chosenNormalBasisLatticeSuccQuotMk K L n
    ⟨((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L), hu⟩

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- A principal unit has zero lattice class exactly when its deviation from one
lies at the next level. -/
theorem chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff {n : Nat}
    (u : 𝒪[L]ˣ) (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisPrincipalUnitLatticeClass K L n u hu = 0 ↔
      u ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1) := by
  rw [chosenNormalBasisPrincipalUnitLatticeClass,
    chosenNormalBasisLatticeSuccQuotMk_eq_zero_iff]
  rfl

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The multiplicative error term for units in `V^n` is one lattice step deeper
whenever products of elements of `π_K^nM` land in `π_K^(n+1)M`. -/
theorem chosenNormalBasisPrincipalUnitSet_mul_error_mem_succ {n : Nat}
    (hmul_succ : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈
            chosenBaseUniformizerPowSubmodule K L (n + 1) (chosenNormalBasisIntegerLattice K L))
    {u v : 𝒪[L]ˣ}
    (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (hv : v ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
        (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
          ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
      chosenBaseUniformizerPowSubmodule K L (n + 1)
        (chosenNormalBasisIntegerLattice K L) := by
  let x : L := ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  let y : L := ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L)
  have hx : x ∈ chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L) := hu
  have hy : y ∈ chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L) := hv
  have hxy : x * y ∈ chosenBaseUniformizerPowSubmodule K L (n + 1)
      (chosenNormalBasisIntegerLattice K L) :=
    hmul_succ x hx y hy
  have hunit :
      ((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) = x * y + x + y := by
    have h :=
      congrArg (fun z : 𝒪[L] => (z : L)) (unit_mul_sub_one_eq L u v)
    simpa [x, y, map_add, map_mul, mul_assoc, mul_comm, mul_left_comm,
      add_assoc, add_comm, add_left_comm] using h
  change
    ((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) - (x + y) ∈
      chosenBaseUniformizerPowSubmodule K L (n + 1)
        (chosenNormalBasisIntegerLattice K L)
  rw [hunit]
  convert hxy using 1 <;> first | rfl | ring

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The lattice class of a product of principal units is the sum of their lattice classes. -/
theorem chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_add {n : Nat}
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (u v : 𝒪[L]ˣ)
    (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (hv : v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (huv : u * v ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisPrincipalUnitLatticeClass K L n (u * v) huv =
      chosenNormalBasisPrincipalUnitLatticeClass K L n u hu +
        chosenNormalBasisPrincipalUnitLatticeClass K L n v hv := by
  rw [chosenNormalBasisPrincipalUnitLatticeClass, chosenNormalBasisPrincipalUnitLatticeClass,
    chosenNormalBasisPrincipalUnitLatticeClass]
  rw [← map_add, chosenNormalBasisLatticeSuccQuotMk_eq_iff,
    mem_chosenNormalBasisLatticeSuccSubmodule_iff]
  change
    (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
        (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
          ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
      chosenBaseUniformizerPowSubmodule K L (n + 1)
        (chosenNormalBasisIntegerLattice K L)
  exact hmul_error u hu v hv

/-- The concrete principal-unit quotient equivalence sends an element to its canonical class. -/
@[simp] theorem chosenNormalBasisPrincipalUnitSuccQuotConcreteEquiv_mk
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) (u : Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotConcreteEquiv (L := L) hV
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) =
      QuotientGroup.mk u :=
  rfl

/-- Every successive principal-unit quotient class has a representative. -/
theorem chosenNormalBasisPrincipalUnitSuccQuotMk_surjective
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) :
    Function.Surjective
      (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV) :=
  QuotientGroup.mk'_surjective
    (chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)

/-- Eliminate a chosen normal-basis principal-unit quotient through arbitrary
representatives and its canonical class map. -/
protected theorem chosenNormalBasisPrincipalUnitSuccQuot.inductionOn
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn)
    {motive : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV → Prop}
    (q : chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV)
    (h : ∀ u : Vn,
      motive (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u)) :
    motive q := by
  change motive
    (show Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV from q)
  refine QuotientGroup.induction_on q ?_
  intro u
  exact h u

/-- Descend a homomorphism that kills the included next-step subgroup. -/
def chosenNormalBasisPrincipalUnitSuccQuotLift
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} {H : Type*} [Group H]
    (hV : Vsucc ≤ Vn) (f : Vn →* H)
    (h : chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV ≤ f.ker) :
    chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV →* H := by
  change
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) →* H
  exact QuotientGroup.lift
    (chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) f h

/-- A map lifted from the successive principal-unit quotient agrees on representatives. -/
@[simp] theorem chosenNormalBasisPrincipalUnitSuccQuotLift_mk
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} {H : Type*} [Group H]
    (hV : Vsucc ≤ Vn) (f : Vn →* H)
    (h : chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV ≤ f.ker)
    (u : Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotLift (L := L) hV f h
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) = f u :=
  rfl

/-- A principal unit represents the identity exactly when it lies in the next subgroup. -/
theorem chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iff
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) (u : Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u = 1 ↔
      (u : 𝒪[L]ˣ) ∈ Vsucc := by
  change
    (QuotientGroup.mk u :
      Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  exact mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff (L := L) hV u

/-- Two principal units represent the same class exactly when their quotient
lies in the next subgroup. -/
@[simp] theorem chosenNormalBasisPrincipalUnitSuccQuotMk_eq_iff_div_mem
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) (u v : Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u =
        chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV v ↔
      u / v ∈ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV := by
  change
    (QuotientGroup.mk u :
      Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) =
      QuotientGroup.mk v ↔ _
  exact QuotientGroup.eq_iff_div_mem
    (N := chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)

/-- The map `u ↦ u - 1` from a subgroup `Vn = V^n` to the additive
successive quotient, viewed multiplicatively on the target. -/
def chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom (n : Nat)
    {Vn : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L)) :
    Vn →* Multiplicative (chosenNormalBasisLatticeSuccQuot K L n) where
  toFun u :=
    Multiplicative.ofAdd
      (chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ)
        (by
          exact hVn ▸ u.2))
  map_one' := by
    change chosenNormalBasisPrincipalUnitLatticeClass K L n
      (1 : 𝒪[L]ˣ) (by exact hVn ▸ (1 : Vn).2) = 0
    rw [chosenNormalBasisPrincipalUnitLatticeClass,
      chosenNormalBasisLatticeSuccQuotMk_eq_zero_iff]
    simp
  map_mul' := by
    intro u v
    have hu : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ u.2
    have hv : (v : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ v.2
    have huv : ((u * v : Vn) : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ (u * v).2
    have hclass :=
      chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_add
        (K := K) (L := L) hmul_error (u : 𝒪[L]ˣ) (v : 𝒪[L]ˣ) hu hv huv
    simpa using congrArg Multiplicative.ofAdd hclass

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- Principal units from the next level lie in the kernel of the lattice-class homomorphism. -/
theorem chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succ
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (u : Vn) (hu : (u : 𝒪[L]ˣ) ∈ Vsucc) :
    u ∈ (chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom
      K L n hVn hmul_error).ker := by
  rw [MonoidHom.mem_ker]
  have hu_n : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
    exact hVn ▸ u.2
  have hu_succ : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1) := by
    exact hVsucc ▸ hu
  have hzero :
      chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ) hu_n = 0 :=
    (chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff
      (K := K) (L := L) (u : 𝒪[L]ˣ) hu_n).2 hu_succ
  change Multiplicative.ofAdd
      (chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ) hu_n) = 1
  simpa using congrArg Multiplicative.ofAdd hzero

/-- The induced map
`Vn/Vsucc -> π_K^nM/π_K^(n+1)M`, with the additive quotient target viewed as a
multiplicative group. -/
def chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom (n : Nat)
    {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hV : Vsucc ≤ Vn)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L)) :
    chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV →*
      Multiplicative (chosenNormalBasisLatticeSuccQuot K L n) :=
  chosenNormalBasisPrincipalUnitSuccQuotLift (L := L) hV
    (chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom K L n hVn hmul_error)
    (by
      intro u hu
      have hu_succ : (u : 𝒪[L]ˣ) ∈ Vsucc :=
        (mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff (L := L) hV u).1 hu
      exact chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom_mem_ker_of_mem_succ
        (K := K) (L := L) hVn hVsucc hmul_error u hu_succ)

omit [Valuation.HasExtension
  (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
/-- The induced quotient homomorphism sends a principal-unit class to its lattice class. -/
theorem chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_mk
    {n : Nat} {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (hV : Vsucc ≤ Vn)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (u : Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom
        K L n hVn hVsucc hV hmul_error
        (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u) =
      chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom K L n hVn hmul_error u :=
  rfl

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_ChosenLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The chosen localization at a finite place

This file equips the actual chosen localization of a finite number-field
extension with its canonical valued local-field structures. It also defines
unramifiedness for that actual completed extension.
-/

open scoped NumberField Classical ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

noncomputable instance chosenFinitePlaceBaseLocallyCompactSpace
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry w₀)
end
end

section
-- module Solutions.OAIQ244_DUKE.ProfiniteIntegers_CyclotomicTorsionQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.inertia_relIndex_eq_ramificationIndex _root_.ClassFormation.DegreeData.FiniteAbstractExtension.mapped_relIndex_eq_residueDegree _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationIndex_coe _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueDegree_coe _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.mem_fieldInertiaWithin_iff _root_.ClassFormation.DegreeData.mem_fieldInertia_iff _root_.ClassFormation.DegreeData.mem_inertia_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.restrictedDegree_apply _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The torsion quotient in the cyclotomic decomposition

The cyclotomic torsion calculation uses the decomposition
`Gal(ℚ_cyc/ℚ) ≃ ℤ̂ × f`, where the torsion subgroup is dense in the
second factor.  This file proves the topological-group calculation which
turns that decomposition into a `ℤ̂`-extension.
-/

open scoped Topology

noncomputable section

namespace ClassFormation

/-- The additive group of `ℤ̂` is torsion-free. -/
instance instIsAddTorsionFreeZHat : IsAddTorsionFree ZHat :=
  ⟨fun {_} hn => zHatMulNat_injective (Nat.pos_of_ne_zero hn)⟩

/-- The multiplicative presentation of additive `ℤ̂` is torsion-free. -/
instance instIsMulTorsionFreeMultiplicativeZHat : IsMulTorsionFree (Multiplicative ZHat) :=
  inferInstance

/-- In a product `ℤ̂ × T` whose torsion is dense in `T`, the closure of
the torsion subgroup is precisely the second factor. -/
theorem topologicalClosure_torsion_zHatMul_prod
    (T : Type*) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T]
    (hT : Dense (CommGroup.torsion T : Set T)) :
    (CommGroup.torsion (Multiplicative ZHat × T)).topologicalClosure =
      (⊥ : Subgroup (Multiplicative ZHat)).prod (⊤ : Subgroup T) := by
  rw [CommGroup.torsion_prod,
    (CommGroup.isMulTorsionFree_iff_torsion_eq_bot.mp inferInstance)]
  apply SetLike.ext'
  rw [Subgroup.topologicalClosure_coe, Subgroup.coe_prod,
    closure_prod_eq]
  simp only [Subgroup.coe_bot, hT.closure_eq]
  rw [closure_singleton]
  ext x
  simp [Subgroup.mem_prod]

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.ProfiniteIntegers_ProfiniteIntegerPrimeProduct
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.inertia_relIndex_eq_ramificationIndex _root_.ClassFormation.DegreeData.FiniteAbstractExtension.mapped_relIndex_eq_residueDegree _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationIndex_coe _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueDegree_coe _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.mem_fieldInertiaWithin_iff _root_.ClassFormation.DegreeData.mem_fieldInertia_iff _root_.ClassFormation.DegreeData.mem_inertia_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.restrictedDegree_apply _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Prime decomposition of the profinite integers

This file constructs the canonical map
`ℤ̂ → ∏ p : Nat.Primes, ℤ_p` from the compatible finite reductions.
-/

open scoped Topology

noncomputable section

namespace ClassFormation

attribute [local instance] ClassFormation.instFactPrimeValNat_solutions
/-- The ring form of the canonical reduction `ℤ̂ → ℤ/nℤ`. -/
def zHatReductionRingHom (n : ℕ) (hn : 0 < n) :
    ZHat →+* ZMod n where
  toFun := zHatReduction n hn
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem zHatReductionRingHom_apply
    (n : ℕ) (hn : 0 < n) (z : ZHat) :
    zHatReductionRingHom n hn z = zHatReduction n hn z :=
  rfl

/-- The compatible `p`-power reductions of a profinite integer. -/
def zHatPadicReduction (p : Nat.Primes) (n : ℕ) :
    ZHat →+* ZMod (p.1 ^ n) :=
  zHatReductionRingHom (p.1 ^ n) (pow_pos p.2.pos n)

theorem zHatPadicReduction_compatible
    (p : Nat.Primes) (m n : ℕ) (hmn : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p.1 hmn) (ZMod (p.1 ^ m))).comp
        (zHatPadicReduction p n) =
      zHatPadicReduction p m := by
  ext z
  exact zHatReduction_transition
    (pow_pos p.2.pos m) (pow_pos p.2.pos n)
    (pow_dvd_pow p.1 hmn) z

/-- The `p`-adic coordinate of a profinite integer. -/
def zHatToPadicInt (p : Nat.Primes) :
    ZHat →+* ℤ_[p.1] :=
  PadicInt.lift (zHatPadicReduction_compatible p)

@[simp]
theorem toZModPow_zHatToPadicInt
    (p : Nat.Primes) (n : ℕ) :
    (PadicInt.toZModPow n).comp (zHatToPadicInt p) =
      zHatPadicReduction p n :=
  PadicInt.lift_spec (zHatPadicReduction_compatible p) n

/-- The canonical ring homomorphism `ℤ̂ → ∏ₚ ℤ_p`. -/
def zHatToProfiniteIntegerPrimeProduct :
    ZHat →+* ProfiniteIntegerPrimeProduct :=
  RingHom.pi zHatToPadicInt

@[simp]
theorem zHatToProfiniteIntegerPrimeProduct_apply
    (z : ZHat) (p : Nat.Primes) :
    zHatToProfiniteIntegerPrimeProduct z p =
      zHatToPadicInt p z :=
  rfl

/-- The prime-coordinate map separates profinite integers. -/
theorem zHatToProfiniteIntegerPrimeProduct_injective :
    Function.Injective zHatToProfiniteIntegerPrimeProduct := by
  intro x y hxy
  apply ZHat.ext
  intro n hn
  let e := ZMod.equivPi (n := n) hn.ne'
  apply e.injective
  funext p
  have hpPrime : p.1.Prime :=
    Nat.prime_of_mem_primeFactors p.2
  let p' : Nat.Primes := ⟨p.1, hpPrime⟩
  have hpCoord :=
    congrArg (fun z : ProfiniteIntegerPrimeProduct => z p') hxy
  have hpReduction :=
    congrArg (PadicInt.toZModPow (n.factorization p.1)) hpCoord
  change
    ((PadicInt.toZModPow (n.factorization p.1)).comp
        (zHatToPadicInt p')) x =
      ((PadicInt.toZModPow (n.factorization p.1)).comp
        (zHatToPadicInt p')) y at hpReduction
  rw [toZModPow_zHatToPadicInt] at hpReduction
  have hpReduction' :
      zHatReduction (p.1 ^ n.factorization p.1)
          (pow_pos hpPrime.pos _) x =
        zHatReduction (p.1 ^ n.factorization p.1)
          (pow_pos hpPrime.pos _) y := by
    exact hpReduction
  have hpowDvd :
      p.1 ^ n.factorization p.1 ∣ n :=
    (hpPrime.pow_dvd_iff_le_factorization hn.ne').2 le_rfl
  have hcast :
      ZMod.castHom hpowDvd
          (ZMod (p.1 ^ n.factorization p.1))
          (zHatReduction n hn x) =
        ZMod.castHom hpowDvd
          (ZMod (p.1 ^ n.factorization p.1))
          (zHatReduction n hn y) := by
    rw [zHatReduction_transition
        (pow_pos hpPrime.pos _) hn hpowDvd x,
      zHatReduction_transition
        (pow_pos hpPrime.pos _) hn hpowDvd y]
    exact hpReduction'
  have heval (z : ZMod n) :
      e z p =
        ZMod.castHom hpowDvd
          (ZMod (p.1 ^ n.factorization p.1)) z := by
    change
      ((Pi.evalRingHom
          (fun q : n.primeFactors =>
            ZMod (q.1 ^ n.factorization q.1)) p).comp
        e.toRingHom) z =
        ZMod.castHom hpowDvd
          (ZMod (p.1 ^ n.factorization p.1)) z
    exact RingHom.congr_fun (Subsingleton.elim _ _) z
  rw [heval, heval]
  exact hcast

/-- Each `p`-adic coordinate map is continuous. -/
theorem continuous_zHatToPadicInt (p : Nat.Primes) :
    Continuous (zHatToPadicInt p) := by
  apply continuous_of_continuousAt_zero
    (zHatToPadicInt p).toAddMonoidHom
  rw [ContinuousAt, Metric.nhds_basis_closedBall.tendsto_right_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p.1 hε
  let K : Set ZHat :=
    (zHatPadicReduction p n).toAddMonoidHom.ker
  have hKopen : IsOpen K := by
    change IsOpen
      ((zHatReduction (p.1 ^ n) (pow_pos p.2.pos n)) ⁻¹'
        ({0} : Set (ZMod (p.1 ^ n))))
    exact (isOpen_discrete ({0} : Set (ZMod (p.1 ^ n)))).preimage
      (zHatReduction (p.1 ^ n) (pow_pos p.2.pos n)).continuous
  have hKzero : (0 : ZHat) ∈ K := by
    change zHatPadicReduction p n 0 = 0
    exact map_zero _
  apply Filter.mem_of_superset (hKopen.mem_nhds hKzero)
  intro z hz
  change zHatPadicReduction p n z = 0 at hz
  have hmod :
      PadicInt.toZModPow n (zHatToPadicInt p z) = 0 := by
    have hspec :=
      RingHom.congr_fun (toZModPow_zHatToPadicInt p n) z
    rw [RingHom.comp_apply] at hspec
    rw [hspec]
    exact hz
  have hmem :
      zHatToPadicInt p z ∈
        Ideal.span ({(p.1 : ℤ_[p.1]) ^ n} : Set ℤ_[p.1]) := by
    rw [← PadicInt.ker_toZModPow n, RingHom.mem_ker]
    exact hmod
  simp only [Set.mem_ofPred_eq, map_zero]
  change zHatToPadicInt p z ∈
    Metric.closedBall (0 : ℤ_[p.1]) ε
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow
    (zHatToPadicInt p z) n).2 hmem |>.trans hn.le

/-- The canonical map to the full prime product is continuous. -/
theorem continuous_zHatToProfiniteIntegerPrimeProduct :
    Continuous zHatToProfiniteIntegerPrimeProduct :=
  continuous_pi continuous_zHatToPadicInt

/-- The diagonal copy of `ℤ` is dense in the product of all `ℤ_p`.
This is the topological form of the finite Chinese remainder theorem. -/
theorem denseRange_intCast_profiniteIntegerPrimeProduct :
    DenseRange
      (Int.castRingHom ProfiniteIntegerPrimeProduct) := by
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨x, hx⟩
  obtain ⟨S, u, hu, hSu⟩ :=
    isOpen_pi_iff.mp hU x hx
  have hNhd (p : ↥S) :
      u p.1 ∈ 𝓝 (x p.1) :=
    (hu p.1 p.2).1.mem_nhds (hu p.1 p.2).2
  choose ε hε hεsub using fun p : ↥S =>
    Metric.nhds_basis_closedBall.mem_iff.mp (hNhd p)
  choose k hk using fun p : ↥S =>
    PadicInt.exists_pow_neg_lt p.1.1 (hε p)
  let modulus : ↥S → ℕ :=
    fun p => p.1.1 ^ k p
  have hcoprime :
      Pairwise (fun p q : ↥S =>
        Nat.Coprime (modulus p) (modulus q)) := by
    intro p q hpq
    apply Nat.coprime_pow_primes
      (k p) (k q) p.1.2 q.1.2
    intro hpval
    apply hpq
    apply Subtype.ext
    apply Nat.Primes.coe_nat_injective
    exact hpval
  let target : ∀ p : ↥S, ZMod (modulus p) :=
    fun p => PadicInt.toZModPow (k p) (x p.1)
  let crt :=
    ZMod.prodEquivPi modulus hcoprime
  obtain ⟨a, ha⟩ :=
    ZMod.intCast_surjective (crt.symm target)
  use Int.castRingHom ProfiniteIntegerPrimeProduct a
  refine ⟨hSu ?_, a, rfl⟩
  intro p hp
  let pS : ↥S := ⟨p, hp⟩
  apply hεsub pS
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hres :
      PadicInt.toZModPow (k pS)
          ((a : ℤ_[p.1])) =
        PadicInt.toZModPow (k pS) (x p) := by
    have heval (z : ZMod (∏ q : ↥S, modulus q)) :
        crt z pS =
          ZMod.castHom
            (Finset.dvd_prod_of_mem modulus (Finset.mem_univ pS))
            (ZMod (modulus pS)) z := by
      change
        ((Pi.evalRingHom
            (fun q : ↥S => ZMod (modulus q)) pS).comp
          crt.toRingHom) z =
          ZMod.castHom
            (Finset.dvd_prod_of_mem modulus (Finset.mem_univ pS))
            (ZMod (modulus pS)) z
      exact RingHom.congr_fun (Subsingleton.elim _ _) z
    calc
      PadicInt.toZModPow (k pS) ((a : ℤ_[p.1])) =
          (a : ZMod (modulus pS)) := by
            simp [modulus, pS]
      _ =
          ZMod.castHom
            (Finset.dvd_prod_of_mem modulus (Finset.mem_univ pS))
            (ZMod (modulus pS))
            (a : ZMod (∏ q : ↥S, modulus q)) := by
              exact
                (map_intCast
                  (ZMod.castHom
                    (Finset.dvd_prod_of_mem modulus
                      (Finset.mem_univ pS))
                    (ZMod (modulus pS))) a).symm
      _ = crt (a : ZMod (∏ q : ↥S, modulus q)) pS :=
            (heval (a : ZMod (∏ q : ↥S, modulus q))).symm
      _ = crt (crt.symm target) pS := by rw [ha]
      _ = target pS := congrFun (crt.apply_symm_apply target) pS
      _ = PadicInt.toZModPow (k pS) (x p) := by
            rfl
  have hmem :
      (a : ℤ_[p.1]) - x p ∈
        Ideal.span
          ({(p.1 : ℤ_[p.1]) ^ k pS} : Set ℤ_[p.1]) := by
    rw [← PadicInt.ker_toZModPow (k pS), RingHom.mem_ker,
      map_sub, hres, sub_self]
  exact
    (PadicInt.norm_le_pow_iff_mem_span_pow
      ((a : ℤ_[p.1]) - x p) (k pS)).2 hmem |>.trans
      (hk pS).le

@[simp]
theorem zHatToPadicInt_intCast
    (p : Nat.Primes) (a : ℤ) :
    zHatToPadicInt p (a : ZHat) = (a : ℤ_[p.1]) :=
  map_intCast (zHatToPadicInt p) a

@[simp]
theorem zHatToProfiniteIntegerPrimeProduct_intCast
    (a : ℤ) :
    zHatToProfiniteIntegerPrimeProduct (a : ZHat) =
      Int.castRingHom ProfiniteIntegerPrimeProduct a := by
  funext p
  exact zHatToPadicInt_intCast p a

/-- The canonical map from the profinite integers to the product of all
`p`-adic integers is onto.  Compactness closes its range, while the finite
Chinese remainder theorem makes that range dense. -/
theorem zHatToProfiniteIntegerPrimeProduct_surjective :
    Function.Surjective zHatToProfiniteIntegerPrimeProduct := by
  have hsubset :
      Set.range (Int.castRingHom ProfiniteIntegerPrimeProduct) ⊆
        Set.range zHatToProfiniteIntegerPrimeProduct := by
    rintro y ⟨a, rfl⟩
    exact
      ⟨(a : ZHat),
        zHatToProfiniteIntegerPrimeProduct_intCast a⟩
  have hdense :
      Dense (Set.range zHatToProfiniteIntegerPrimeProduct) :=
    denseRange_intCast_profiniteIntegerPrimeProduct.mono hsubset
  have hclosed :
      IsClosed (Set.range zHatToProfiniteIntegerPrimeProduct) :=
    (isCompact_range
      continuous_zHatToProfiniteIntegerPrimeProduct).isClosed
  intro y
  have hy :
      y ∈ closure
        (Set.range zHatToProfiniteIntegerPrimeProduct) := by
    rw [hdense.closure_eq]
    trivial
  rwa [hclosed.closure_eq] at hy

/-- The Chinese-remainder ring equivalence
`ℤ̂ ≃ ∏ p : Nat.Primes, ℤ_p`. -/
noncomputable def zHatRingEquivProfiniteIntegerPrimeProduct :
    ZHat ≃+* ProfiniteIntegerPrimeProduct :=
  RingEquiv.ofBijective zHatToProfiniteIntegerPrimeProduct
    ⟨zHatToProfiniteIntegerPrimeProduct_injective,
      zHatToProfiniteIntegerPrimeProduct_surjective⟩

@[simp]
theorem zHatRingEquivProfiniteIntegerPrimeProduct_apply
    (z : ZHat) :
    zHatRingEquivProfiniteIntegerPrimeProduct z =
      zHatToProfiniteIntegerPrimeProduct z :=
  rfl

end ClassFormation
end
end

section
-- module Solutions.OAIQ244_DUKE.ProfiniteIntegers_ProfiniteIntegerUnits
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace
attribute [-simp] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.inertia_relIndex_eq_ramificationIndex _root_.ClassFormation.DegreeData.FiniteAbstractExtension.mapped_relIndex_eq_residueDegree _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationIndex_coe _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueDegree_coe _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.fieldImageAdd_index _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_frobenius _root_.ClassFormation.DegreeData.maximalUnramifiedDegreeEquiv_mk _root_.ClassFormation.DegreeData.mem_fieldInertiaWithin_iff _root_.ClassFormation.DegreeData.mem_fieldInertia_iff _root_.ClassFormation.DegreeData.mem_inertia_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.normalizedDegree_apply_toAdd _root_.ClassFormation.DegreeData.restrictedDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.restrictedDegree_apply _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.ValuationData.valuationAt_coe _root_.ClassFormation.ValuationData.valueModulo_apply _root_.ClassFormation.canonicalValueQuotientMap_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.mem_nsmulImage_iff _root_.ClassFormation.nsmulImage_top _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Units of the profinite integers

This file upgrades the prime-product Chinese-remainder equivalence for
`ℤ̂` to topological additive, multiplicative, and unit-group equivalences.
-/

open scoped Topology

noncomputable section

namespace ClassFormation

/-- The Chinese-remainder isomorphism as a topological monoid equivalence. -/
noncomputable def zHatContinuousMulEquivPrimeProduct :
    ZHat ≃ₜ* ProfiniteIntegerPrimeProduct :=
  ContinuousMulEquiv.mk'
    (continuous_zHatToProfiniteIntegerPrimeProduct.homeoOfEquivCompactToT2
      (f := zHatRingEquivProfiniteIntegerPrimeProduct.toEquiv))
    zHatRingEquivProfiniteIntegerPrimeProduct.map_mul

/-- The additive form of the topological Chinese-remainder isomorphism. -/
noncomputable def zHatContinuousAddEquivPrimeProduct :
    ZHat ≃ₜ+ ProfiniteIntegerPrimeProduct :=
  { zHatRingEquivProfiniteIntegerPrimeProduct.toAddEquiv with
    continuous_toFun :=
      zHatContinuousMulEquivPrimeProduct.continuous_toFun
    continuous_invFun :=
      zHatContinuousMulEquivPrimeProduct.continuous_invFun }

attribute [local instance] ClassFormation.instFactPrimeValNat_solutions_1
/-- The canonical topological Chinese-remainder equivalence on unit
groups. -/
noncomputable def zHatUnitsContinuousMulEquivPrimeProduct :
    ZHatˣ ≃ₜ* ((p : Nat.Primes) → ℤ_[p.1]ˣ) :=
  (Units.mapContinuousMulEquiv
    zHatContinuousMulEquivPrimeProduct).trans
      ContinuousMulEquiv.piUnits

/-- On underlying ring elements, the unit-group Chinese-remainder
equivalence is the canonical `p`-adic coordinate map. -/
@[simp]
theorem zHatUnitsContinuousMulEquivPrimeProduct_coe_apply
    (u : ZHatˣ) (p : Nat.Primes) :
    (zHatUnitsContinuousMulEquivPrimeProduct u p : ℤ_[p.1]) =
      zHatToPadicInt p (u : ZHat) :=
  rfl

end ClassFormation
end
end


