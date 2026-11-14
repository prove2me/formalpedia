-- Prove2me | Definitions.Def_OAIQ244Duke004
-- name    : OAIQ244Duke004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:11:24.284577+00:00
-- url     : https://prove2.me/theorems/981f7987-61e8-44b6-93ba-b61fcfbd0486
-- title:
--   Definitions bundle OAIQ244Duke004 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 560 declarations of OpenAI's Lean: 213 definitions, 17 inductive types or structures, 39 instances and 291 theorems. The definitions and types are `ClassFieldTheory.arithmeticFrobeniusAt`, `ClassFormation.ClassFieldAxiomCohomologyData`, `ClassFormation.DegreeData`, `ClassFormation.DegreeData.AbstractExtension`, `ClassFormation.DegreeData.AbstractExtension.IsTotallyRamified`, `ClassFormation.DegreeData.AbstractExtension.IsUnramified`, `ClassFormation.DegreeData.AbstractExtension.Tower`, `ClassFormation.DegreeData.AbstractExtension.Tower.baseExtension`, `ClassFormation.DegreeData.AbstractExtension.Tower.topExtension`, `ClassFormation.DegreeData.AbstractExtension.Tower.totalExtension`, `ClassFormation.DegreeData.AbstractExtension.degreeCardinal`, `ClassFormation.DegreeData.AbstractExtension.quotient`, `ClassFormation.DegreeData.AbstractExtension.relativeRamificationIndexCardinal`, `ClassFormation.DegreeData.AbstractExtension.relativeResidueDegreeCardinal`, `ClassFormation.DegreeData.AbstractExtension.subgroup`, `ClassFormation.DegreeData.FiniteAbstractExtension`, `ClassFormation.DegreeData.FiniteAbstractExtension.IsTotallyRamified`, `ClassFormation.DegreeData.FiniteAbstractExtension.IsUnramified`, `ClassFormation.DegreeData.FiniteAbstractExtension.degree`, `ClassFormation.DegreeData.FiniteAbstractExtension.ofInclusion`, `ClassFormation.DegreeData.FiniteAbstractExtension.quotient`, `ClassFormation.DegreeData.FiniteAbstractExtension.ramificationIndex`, `ClassFormation.DegreeData.FiniteAbstractExtension.residueDegree`, `ClassFormation.DegreeData.FiniteAbstractExtension.subgroup`, `ClassFormation.DegreeData.FiniteResidueAbstractExtension`, `ClassFormation.DegreeData.FiniteResidueAbstractExtension.degree`, `ClassFormation.DegreeData.FiniteResidueAbstractExtension.ofInclusion`, `ClassFormation.DegreeData.FiniteResidueAbstractExtension.ramificationIndex`, `ClassFormation.DegreeData.FiniteResidueAbstractExtension.residueDegree`, `ClassFormation.DegreeData.FiniteResidueAbstractExtension.toFiniteAbstractExtension`, `ClassFormation.DegreeData.FiniteResidueAbstractField`, `ClassFormation.DegreeData.FiniteResidueAbstractField.conjugate`, `ClassFormation.DegreeData.FiniteResidueAbstractField.ofRelativeInclusion`, `ClassFormation.DegreeData.FiniteResidueAbstractField.residueDegree`, `ClassFormation.DegreeData.FiniteResidueAbstractField.toSubgroup`, `ClassFormation.DegreeData.FiniteTower`, `ClassFormation.DegreeData.FiniteTower.totalExtension`, `ClassFormation.DegreeData.FrobeniusElements`, `ClassFormation.DegreeData.GaloisSubextension`, `ClassFormation.DegreeData.GaloisSubextension.IsTotallyRamified` and 190 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AbstractClassFieldTheory_Degree_Fields`, `AbstractClassFieldTheory_Degree_Frobenius`, `AbstractClassFieldTheory_Degree_FrobeniusFixedField`, `AbstractClassFieldTheory_Degree_FrobeniusLift`, `AbstractClassFieldTheory_Degree_Indices`, `AbstractClassFieldTheory_Degree_Norm`, `AbstractClassFieldTheory_Degree_NormConjugation`, `AbstractClassFieldTheory_Degree_NormLaws`, `AbstractClassFieldTheory_Degree_PrimeElements`, `AbstractClassFieldTheory_Degree_Valuation`, `AbstractClassFieldTheory_Degree_ValuationLaws`, `AbstractClassFieldTheory_Reciprocity_ClassFieldAxiom`, `AbstractClassFieldTheory_Reciprocity_Construction_DoubleCosetOrbitGeometry`, `AbstractClassFieldTheory_Reciprocity_Construction_FiniteNormQuotient`, `AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_CorrectionSum`, `AbstractClassFieldTheory_Reciprocity_Construction_NormSubgroup`, `AbstractClassFieldTheory_Reciprocity_Construction_PrimeChoice`, `AbstractClassFieldTheory_Reciprocity_Construction_ReciprocityIndependence`, `AbstractClassFieldTheory_Reciprocity_Construction_TransferOrbitClosure`, `AbstractClassFieldTheory_Reciprocity_Construction_UnitCohomologyAxiom`, `AbstractClassFieldTheory_Reciprocity_FieldRepresentation`, `AbstractClassFieldTheory_Reciprocity_FiniteGaloisSubextension`, `AbstractClassFieldTheory_Reciprocity_IntermediateExtension`, `AlgebraicNumberTheory_Idele_LocallyCompact`, `AlgebraicNumberTheory_Idele_NormApproximation_FinitePlaces`, `Cyclic_IntegralRepUniverse`, `Cyclic_NormKernelVanishing`, `Cyclic_TateComparison`, `Definitions_FrobeniusAndHilbertClassFields_ArithmeticFrobeniusAt`, `GroupTheory_QuotientTower`, `Kummer_Abstract_KummerAbelianAssembly`, `Kummer_Abstract_KummerAbelianCyclicFactors`, `Kummer_Abstract_KummerDelta`, `Kummer_Abstract_KummerGlobalOperator`, `LocalField_NonarchimedeanLocalField_ResidueExtension`, `LocalField_NonarchimedeanLocalField_ValuativeExtension`, `LocalField_NonarchimedeanLocalField_ValuedTopology`, `ProfiniteIntegers_ProfiniteInteger`, `ProfiniteIntegers_ProfiniteIntegerCore`, `ProfiniteIntegers_TopologicalGeneration`, `Topology_TotallyDisconnectedQuotients`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke015`, `OAIQ244Duke016`, `OAIQ244Duke017`, `OAIQ244Duke018`, `OAIQ244Duke019`, `OAIQ244Duke020` and `OAIQ244Duke021`.
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
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.Shrink
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
import Mathlib.GroupTheory.Transfer
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
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Frobenius
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

section
-- module Solutions.OAIQ244_DUKE.GroupTheory_QuotientTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Quotients in subgroup towers

This file supplies the type-level equivalences between the quotient of a
subgroup and the corresponding quotient after viewing that subgroup inside a
larger group. They complement Mathlib's natural-number relative-index laws
when cardinal-valued indices must also cover infinite towers.
-/

noncomputable section

universe u

namespace Subgroup

variable {G : Type u} [Group G]

/-- Viewing `H` inside `K` does not change the quotient of `H` by the
subgroup induced by `M`. -/
def quotientSubgroupOfEquiv {H K M : Subgroup G} (hHK : H ≤ K) :
    (↑(H.subgroupOf K) ⧸ (M.subgroupOf K).subgroupOf (H.subgroupOf K)) ≃
      (↑H ⧸ M.subgroupOf H) where
  toFun := Quotient.map' (subgroupOfEquivOfLe hHK) (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    exact hxy)
  invFun := Quotient.map' (subgroupOfEquivOfLe hHK).symm (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    exact hxy)
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change Quotient.map' _ _ (Quotient.map' _ _ (Quotient.mk'' x)) = Quotient.mk'' x
    simpa only [Quotient.map'_mk''] using
      congrArg Quotient.mk'' ((subgroupOfEquivOfLe hHK).symm_apply_apply x)
  right_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change Quotient.map' _ _ (Quotient.map' _ _ (Quotient.mk'' x)) = Quotient.mk'' x
    simpa only [Quotient.map'_mk''] using
      congrArg Quotient.mk'' ((subgroupOfEquivOfLe hHK).apply_symm_apply x)

/-- A quotient by the bottom of a subgroup tower is equivalent to the product
of the two successive quotient types. -/
def quotientTowerEquiv {M L K : Subgroup G} (hML : M ≤ L) (hLK : L ≤ K) :
    (K ⧸ M.subgroupOf K) ≃
      (K ⧸ L.subgroupOf K) × (L ⧸ M.subgroupOf L) :=
  (quotientEquivProdOfLE (subgroupOf_mono K hML)).trans
    (Equiv.prodCongr (Equiv.refl _) (quotientSubgroupOfEquiv hLK))

end Subgroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

def kernelToSaturation (d : G →* D) (L K : Subgroup G) :
    ↑(K ⊓ d.ker) →* ↑(K ⊓ (L ⊔ d.ker)) :=
  Subgroup.inclusion (inf_le_inf le_rfl le_sup_right)

theorem kernelToSaturation_rel_iff (d : G →* D) (L K : Subgroup G)
    (x y : ↑(K ⊓ d.ker)) :
    QuotientGroup.leftRel ((L ⊓ d.ker).subgroupOf (K ⊓ d.ker)) x y ↔
      QuotientGroup.leftRel (L.subgroupOf (K ⊓ (L ⊔ d.ker)))
        (kernelToSaturation d L K x) (kernelToSaturation d L K y) := by
  simp only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · exact fun h ↦ h.1
  · intro h
    exact ⟨h, d.ker.mul_mem (d.ker.inv_mem x.property.2) y.property.2⟩

noncomputable def kernelCosetToSaturationCoset (d : G →* D) (L K : Subgroup G) :
    (↑(K ⊓ d.ker) ⧸ (L ⊓ d.ker).subgroupOf (K ⊓ d.ker)) →
      (↑(K ⊓ (L ⊔ d.ker)) ⧸ L.subgroupOf (K ⊓ (L ⊔ d.ker))) :=
  Quotient.map' (kernelToSaturation d L K) fun x y h ↦
    (kernelToSaturation_rel_iff d L K x y).mp h

theorem kernelCosetToSaturationCoset_injective (d : G →* D) (L K : Subgroup G) :
    Function.Injective (kernelCosetToSaturationCoset d L K) := by
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro x y h
  apply Quotient.eq''.mpr
  apply (kernelToSaturation_rel_iff d L K x y).mpr
  apply Quotient.eq''.mp
  simpa only [kernelCosetToSaturationCoset, Quotient.map'_mk''] using h

theorem kernelCosetToSaturationCoset_surjective (d : G →* D) {L K : Subgroup G}
    (hLK : L ≤ K) : Function.Surjective (kernelCosetToSaturationCoset d L K) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro z
  have hzSup : (z : G) ∈ d.ker ⊔ L := by
    rw [sup_comm]
    exact z.property.2
  obtain ⟨n, hnKer, l, hlL, hnl⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := d.ker) (t := L)).mp hzSup
  have hnK : n ∈ K := by
    rw [show n = (z : G) * l⁻¹ by rw [← hnl]; simp]
    exact K.mul_mem z.property.1 (K.inv_mem (hLK hlL))
  let n' : ↑(K ⊓ d.ker) := ⟨n, hnK, hnKer⟩
  refine ⟨Quotient.mk'' n', ?_⟩
  simp only [kernelCosetToSaturationCoset, Quotient.map'_mk'']
  apply Quotient.eq''.mpr
  rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
  change n⁻¹ * (z : G) ∈ L
  rw [← hnl]
  simpa using hlL

/-- The kernel cosets for `L ≤ K` are the cosets in the part of `K` saturated by `ker d`.

This is the set-level second-isomorphism argument needed for relative indices; no normality
assumption on `L` is required. -/
noncomputable def kernelCosetEquivSaturation (d : G →* D) {L K : Subgroup G} (hLK : L ≤ K) :
    (↑(K ⊓ d.ker) ⧸ (L ⊓ d.ker).subgroupOf (K ⊓ d.ker)) ≃
      (↑(K ⊓ (L ⊔ d.ker)) ⧸ L.subgroupOf (K ⊓ (L ⊔ d.ker))) :=
  Equiv.ofBijective (kernelCosetToSaturationCoset d L K)
    ⟨kernelCosetToSaturationCoset_injective d L K,
      kernelCosetToSaturationCoset_surjective d hLK⟩

/-- The index of `L` in the `ker d`-saturated part of `K` is the relative
index of the corresponding kernel intersections. -/
theorem relIndex_saturation_eq_inf_ker_relIndex (d : G →* D)
    {L K : Subgroup G} (hLK : L ≤ K) :
    L.relIndex (K ⊓ (L ⊔ d.ker)) =
      (L ⊓ d.ker).relIndex (K ⊓ d.ker) := by
  unfold Subgroup.relIndex
  exact Nat.card_congr (kernelCosetEquivSaturation d hLK).symm

/-- The mapped relative index is the index of the `ker d`-saturated part of
`K`. -/
theorem map_relIndex_eq_saturation_relIndex (d : G →* D)
    (L K : Subgroup G) :
    (L.map d).relIndex (K.map d) =
      (K ⊓ (L ⊔ d.ker)).relIndex K := by
  rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq, ← Subgroup.inf_relIndex_right,
    inf_comm]

/-- The exact relative-index identity associated to a group homomorphism.

No finite-index assumption is needed: the proof is induced by equivalences
of coset types, so the equality remains valid with Mathlib's convention that
an infinite relative index is `0`. -/
theorem relIndex_eq_map_relIndex_mul_inf_ker_relIndex (d : G →* D) {L K : Subgroup G}
    (hLK : L ≤ K) :
    L.relIndex K =
      (L.map d).relIndex (K.map d) * (L ⊓ d.ker).relIndex (K ⊓ d.ker) := by
  rw [map_relIndex_eq_saturation_relIndex,
    ← relIndex_saturation_eq_inf_ker_relIndex d hLK, mul_comm]
  exact (Subgroup.relIndex_mul_relIndex L (K ⊓ (L ⊔ d.ker)) K
    (fun x hx ↦ ⟨hLK hx, (show L ≤ L ⊔ d.ker from le_sup_left) hx⟩) inf_le_left).symm

/-! ## Cardinal-valued relative indices

The natural-valued `Subgroup.relIndex` is useful only after finiteness is
known: it represents every infinite index by zero.  The following API keeps
the actual coset cardinality and is therefore the source for general tower
and image--kernel laws.  Chosen representatives occur only in private
equivalences used to prove these canonical equalities. -/

/-- The cardinality of the coset type of the intersection of two subgroups.

This is defined for arbitrary subgroups.  For the cardinal relative index of
an inclusion, use `relativeIndexCardinal`, which records the inclusion in its
domain. -/
noncomputable def intersectionIndexCardinal (L K : Subgroup G) : Cardinal :=
  Cardinal.mk (K ⧸ L.subgroupOf K)

/-- The cardinality of the actual relative coset type of a subgroup inclusion. -/
noncomputable def relativeIndexCardinal {L K : Subgroup G} (_ : L ≤ K) : Cardinal :=
  intersectionIndexCardinal L K

/-- Establishes the identity `relativeIndexCardinal (le_refl K) = 1`. -/
@[simp] theorem relativeIndexCardinal_self (K : Subgroup G) :
    relativeIndexCardinal (le_refl K) = 1 := by
  let α := K ⧸ K.subgroupOf K
  let : Subsingleton α := by
    constructor
    intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro x y
    apply Quotient.eq''.mpr
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    exact (x⁻¹ * y).2
  change Cardinal.mk α = 1
  exact Cardinal.mk_eq_one α

/-- Relative cardinal indices multiply in every subgroup tower. -/
theorem relativeIndexCardinal_mul {M L K : Subgroup G}
    (hML : M ≤ L) (hLK : L ≤ K) :
    relativeIndexCardinal hML * relativeIndexCardinal hLK =
      relativeIndexCardinal (hML.trans hLK) := by
  rw [mul_comm, relativeIndexCardinal, relativeIndexCardinal,
    relativeIndexCardinal, intersectionIndexCardinal, intersectionIndexCardinal,
    intersectionIndexCardinal, Cardinal.mul_def]
  exact Cardinal.mk_congr (Subgroup.quotientTowerEquiv hML hLK).symm

def subgroupMapRestriction (d : G →* D) (K : Subgroup G) :
    K →* K.map d where
  toFun x := ⟨d x.1, ⟨x.1, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one d)
  map_mul' x y := Subtype.ext (map_mul d x.1 y.1)

theorem subgroupMapRestriction_surjective (d : G →* D) (K : Subgroup G) :
    Function.Surjective (subgroupMapRestriction d K) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem subgroupMapRestriction_rel_iff (d : G →* D)
    (H : Subgroup D) (K : Subgroup G) (x y : K) :
    QuotientGroup.leftRel ((H.comap d).subgroupOf K) x y ↔
      QuotientGroup.leftRel (H.subgroupOf (K.map d))
        (subgroupMapRestriction d K x) (subgroupMapRestriction d K y) := by
  simp only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf,
    Subgroup.mem_comap]
  change d (x.1⁻¹ * y.1) ∈ H ↔ (d x.1)⁻¹ * d y.1 ∈ H
  rw [map_mul, map_inv]

noncomputable def relativeCosetComapMap (d : G →* D)
    (H : Subgroup D) (K : Subgroup G) :
    (K ⧸ (H.comap d).subgroupOf K) →
      (K.map d ⧸ H.subgroupOf (K.map d)) :=
  Quotient.map' (subgroupMapRestriction d K) fun x y h ↦
    (subgroupMapRestriction_rel_iff d H K x y).mp h

theorem relativeCosetComapMap_injective (d : G →* D)
    (H : Subgroup D) (K : Subgroup G) :
    Function.Injective (relativeCosetComapMap d H K) := by
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro x y h
  apply Quotient.eq''.mpr
  apply (subgroupMapRestriction_rel_iff d H K x y).mpr
  apply Quotient.eq''.mp
  simpa only [relativeCosetComapMap, Quotient.map'_mk''] using h

theorem relativeCosetComapMap_surjective (d : G →* D)
    (H : Subgroup D) (K : Subgroup G) :
    Function.Surjective (relativeCosetComapMap d H K) := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro z
  obtain ⟨x, rfl⟩ := subgroupMapRestriction_surjective d K z
  exact ⟨Quotient.mk'' x, by
    simp only [relativeCosetComapMap, Quotient.map'_mk'']⟩

noncomputable def relativeCosetComapEquiv (d : G →* D)
    (H : Subgroup D) (K : Subgroup G) :
    (K ⧸ (H.comap d).subgroupOf K) ≃
      (K.map d ⧸ H.subgroupOf (K.map d)) :=
  Equiv.ofBijective (relativeCosetComapMap d H K)
    ⟨relativeCosetComapMap_injective d H K,
      relativeCosetComapMap_surjective d H K⟩

noncomputable def imageCosetEquivSaturation (d : G →* D)
    (L K : Subgroup G) :
    (K ⧸ (K ⊓ (L ⊔ d.ker)).subgroupOf K) ≃
      (K.map d ⧸ (L.map d).subgroupOf (K.map d)) := by
  have hsub :
      ((L.map d).comap d).subgroupOf K =
        (K ⊓ (L ⊔ d.ker)).subgroupOf K := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [Subgroup.comap_map_eq]
    exact (and_iff_right x.2).symm
  exact (Subgroup.quotientEquivOfEq hsub.symm).trans
    (relativeCosetComapEquiv d (L.map d) K)

/-- Cardinal form of the image contribution: it is the intersection index of
the kernel-saturated part of the upper subgroup. -/
theorem intersectionIndexCardinal_image_eq_saturation (d : G →* D)
    (L K : Subgroup G) :
    Cardinal.lift.{u} (intersectionIndexCardinal (L.map d) (K.map d)) =
      Cardinal.lift.{v}
        (intersectionIndexCardinal (K ⊓ (L ⊔ d.ker)) K) := by
  exact (imageCosetEquivSaturation d L K).lift_cardinal_eq.symm

/-- Cardinal form of the kernel contribution: intersecting both subgroups
with the kernel gives the saturated inner index. -/
theorem relativeIndexCardinal_kernel_eq_saturation (d : G →* D)
    {L K : Subgroup G} (hLK : L ≤ K) :
    relativeIndexCardinal
      (show L ⊓ d.ker ≤ K ⊓ d.ker from inf_le_inf hLK le_rfl) =
      relativeIndexCardinal
        (show L ≤ K ⊓ (L ⊔ d.ker) from fun _ hx ↦
          ⟨hLK hx, (show L ≤ L ⊔ d.ker from le_sup_left) hx⟩) := by
  exact Cardinal.mk_congr (kernelCosetEquivSaturation d hLK)

/-- The cardinal image--kernel identity for a subgroup inclusion.  It remains
valid for infinite indices because it is induced by equivalences of the
actual coset types. -/
theorem relativeIndexCardinal_eq_map_mul_inf_ker (d : G →* D)
    {L K : Subgroup G} (hLK : L ≤ K) :
    Cardinal.lift.{v} (relativeIndexCardinal hLK) =
      Cardinal.lift.{u}
          (relativeIndexCardinal (Subgroup.map_mono (f := d) hLK)) *
        Cardinal.lift.{v}
          (relativeIndexCardinal
            (show L ⊓ d.ker ≤ K ⊓ d.ker from inf_le_inf hLK le_rfl)) := by
  have hLS : L ≤ K ⊓ (L ⊔ d.ker) := fun _ hx ↦
    ⟨hLK hx, (show L ≤ L ⊔ d.ker from le_sup_left) hx⟩
  have hSK : K ⊓ (L ⊔ d.ker) ≤ K := inf_le_left
  calc
    Cardinal.lift.{v} (relativeIndexCardinal hLK) =
        Cardinal.lift.{v}
            (relativeIndexCardinal hLS) *
          Cardinal.lift.{v}
            (relativeIndexCardinal hSK) := by
      rw [← Cardinal.lift_mul, relativeIndexCardinal_mul hLS hSK]
    _ = Cardinal.lift.{v}
            (relativeIndexCardinal
              (show L ⊓ d.ker ≤ K ⊓ d.ker from inf_le_inf hLK le_rfl)) *
          Cardinal.lift.{u}
            (relativeIndexCardinal (Subgroup.map_mono (f := d) hLK)) := by
      have hkernel :
          intersectionIndexCardinal (L ⊓ d.ker) (K ⊓ d.ker) =
            intersectionIndexCardinal L (K ⊓ (L ⊔ d.ker)) := by
        simpa only [relativeIndexCardinal] using
          relativeIndexCardinal_kernel_eq_saturation d hLK
      change
        Cardinal.lift.{v}
            (intersectionIndexCardinal L (K ⊓ (L ⊔ d.ker))) *
          Cardinal.lift.{v}
            (intersectionIndexCardinal (K ⊓ (L ⊔ d.ker)) K) =
          Cardinal.lift.{v}
            (intersectionIndexCardinal (L ⊓ d.ker) (K ⊓ d.ker)) *
          Cardinal.lift.{u}
            (intersectionIndexCardinal (L.map d) (K.map d))
      rw [hkernel, intersectionIndexCardinal_image_eq_saturation d L K]
    _ = Cardinal.lift.{u}
            (relativeIndexCardinal (Subgroup.map_mono (f := d) hLK)) *
          Cardinal.lift.{v}
            (relativeIndexCardinal
              (show L ⊓ d.ker ≤ K ⊓ d.ker from inf_le_inf hLK le_rfl)) := mul_comm _ _

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_IntegralRepUniverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Universe boundary for integral representations

Mathlib's `Rep ℤ G` currently requires the coefficient ring and acting group
to inhabit the same universe.  Since `ℤ : Type 0`, every representation-bearing
part of local class field theory uses this single named boundary.  Keeping the
restriction here makes a future universe-polymorphic migration searchable and
prevents individual subtrees from inventing private aliases.
-/

set_option autoImplicit false

/-- The universe-zero group boundary imposed by integral representations. -/
abbrev IntegralRepGroupType := Type 0
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_TateComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Boundary-degree Tate cohomology for finite cyclic groups

This file identifies mathlib's Tate cohomology in degrees `0` and `-1` with the
standard finite-cyclic short complexes.  It adds no alternative cohomology
model: both targets are the homology objects already defined by mathlib.
-/

noncomputable section

open CategoryTheory

namespace TateCohomology

universe u

/-- Degree-zero Tate cohomology is the homology of the standard boundary
short complex `A --N--> A --d₀₁--> C¹(G, A)` for every finite group. -/
def isoZeroBoundary {R G : Type u} [CommRing R] [Group G] [Fintype G]
    (A : Rep R G) :
    tateCohomology A 0 ≅
      (ShortComplex.mk A.norm.toModuleCatHom (groupCohomology.d₀₁ A)
        (Rep.norm_comp_d_eq_zero A)).homology := by
  let S : ShortComplex (ModuleCat R) :=
    .mk A.norm.toModuleCatHom (groupCohomology.d₀₁ A)
      (Rep.norm_comp_d_eq_zero A)
  let eS : (tateComplex A).sc 0 ≅ S :=
    (tateComplex A).isoSc' (-1) 0 1 (by simp) (by simp) ≪≫
      ShortComplex.isoMk
        (by exact groupHomology.chainsIso₀ A)
        (groupCohomology.cochainsIso₀ A)
        (groupCohomology.cochainsIso₁ A)
        (by
          change
            (groupHomology.chainsIso₀ A).hom ≫ A.norm.toModuleCatHom =
              A.tateNorm ≫ (groupCohomology.cochainsIso₀ A).hom
          rw [Rep.tateNorm]
          simp)
        (groupCohomology.comp_d₀₁_eq A)
  exact ShortComplex.homologyMapIso eS

/-- For a finite cyclic group generated by `g`, degree-zero Tate cohomology is
the homology of `A --N--> A --(ρ(g) - 1)--> A`. -/
def isoFiniteCyclicZero {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A 0 ≅
      (Rep.FiniteCyclicGroup.normHomCompSub A g).homology := by
  let S : ShortComplex (ModuleCat R) :=
    .mk A.norm.toModuleCatHom (groupCohomology.d₀₁ A)
      (Rep.norm_comp_d_eq_zero A)
  let T := Rep.FiniteCyclicGroup.normHomCompSub A g
  have hker : LinearMap.ker S.g.hom = LinearMap.ker T.g.hom := by
    dsimp [S, T]
    rw [groupCohomology.d₀₁_ker_eq_invariants]
    ext x
    simpa [Rep.sub_hom, sub_eq_zero] using
      Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg x
  let eK : LinearMap.ker S.g.hom ≃ₗ[R] LinearMap.ker T.g.hom :=
    LinearEquiv.ofEq _ _ hker
  have hboundary :
      (LinearMap.range S.moduleCatToCycles).map eK.toLinearMap =
        LinearMap.range T.moduleCatToCycles := by
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
  let eQ : S.moduleCatLeftHomologyData.H ≅ T.moduleCatLeftHomologyData.H :=
    (Submodule.Quotient.equiv _ _ eK hboundary).toModuleIso
  exact isoZeroBoundary A ≪≫
    S.moduleCatHomologyIso ≪≫ eQ ≪≫ T.moduleCatHomologyIso.symm

/-- For a finite cyclic group generated by `g`, degree-minus-one Tate
cohomology is the homology of `A --(ρ(g) - 1)--> A --N--> A`. -/
def isoFiniteCyclicNegOne {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]
    (A : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A (-1) ≅
      (Rep.FiniteCyclicGroup.subCompNormHom A g).homology := by
  let S : ShortComplex (ModuleCat R) :=
    .mk (groupHomology.d₁₀ A) A.norm.toModuleCatHom (Rep.comp_eq_zero A)
  let eS : (tateComplex A).sc (-1) ≅ S :=
    (tateComplex A).isoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫
      ShortComplex.isoMk
        (groupHomology.chainsIso₁ A)
        (groupHomology.chainsIso₀ A)
        (groupCohomology.cochainsIso₀ A)
        (groupHomology.comp_d₁₀_eq A)
        (by simp [S, tateComplex, Rep.tateNorm]; rfl)
  let T := Rep.FiniteCyclicGroup.subCompNormHom A g
  have hRange : LinearMap.range S.f.hom = LinearMap.range T.f.hom := by
    dsimp [S, T]
    rw [groupHomology.range_d₁₀_eq_coinvariantsKer]
    exact Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ g hg
  let eK : LinearMap.ker S.g.hom ≃ₗ[R] LinearMap.ker T.g.hom :=
    LinearEquiv.ofEq _ _ rfl
  have hboundary :
      (LinearMap.range S.moduleCatToCycles).map eK.toLinearMap =
        LinearMap.range T.moduleCatToCycles := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      have hz : S.f z ∈ LinearMap.range T.f.hom := by
        rw [← hRange]
        exact ⟨z, rfl⟩
      rcases hz with ⟨w, hw⟩
      refine ⟨w, ?_⟩
      apply Subtype.ext
      exact hw
    · rintro ⟨w, rfl⟩
      have hw : T.f w ∈ LinearMap.range S.f.hom := by
        rw [hRange]
        exact ⟨w, rfl⟩
      rcases hw with ⟨z, hz⟩
      refine ⟨S.moduleCatToCycles z, ⟨z, rfl⟩, ?_⟩
      apply Subtype.ext
      exact hz
  let eQ : S.moduleCatLeftHomologyData.H ≅ T.moduleCatLeftHomologyData.H :=
    (Submodule.Quotient.equiv _ _ eK hboundary).toModuleIso
  exact ShortComplex.homologyMapIso eS ≪≫
    S.moduleCatHomologyIso ≪≫ eQ ≪≫ T.moduleCatHomologyIso.symm

end TateCohomology
end
end

section
-- module Solutions.OAIQ244_DUKE.Cyclic_NormKernelVanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace CyclicCohomology

/-!
# The cyclic-cohomology vanishing condition

This file formalizes the cyclic norm-kernel vanishing condition as a property, not as a new Lean axiom, and
the finite-cyclic cohomology calculation using the actual finite-cyclic group-cohomology computation.

The construction writes multiplicative modules with a right action.  Here an abelian
group is represented additively as a `ℤ`-linear left representation; passing
between the two conventions replaces a generator by its inverse and does not
change either quotient below.
-/

noncomputable section

open CategoryTheory

universe u

/-- A specified generator supplies the `IsCyclic` instance used throughout
the cyclic cohomology constructions. -/
theorem isCyclic_of_generator {G : Type} [Group G] (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) : IsCyclic G := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨g, ?_⟩
  ext x
  constructor
  · intro _
    exact Subgroup.mem_top x
  · intro _
    exact hg x

/-- If the abstract field `L` extends `K`, this is exactly `G_L` regarded as
a subgroup of `G_K`.  The standard `Subgroup.subgroupOf` construction is the
canonical representation; the containment proof only changes the subtype
membership proof and therefore cannot create a second subgroup representation. -/
abbrev extensionSubgroup {G : Type u} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (_hLK : L.toSubgroup ≤ K.toSubgroup) :
    Subgroup K.toSubgroup :=
  L.toSubgroup.subgroupOf K.toSubgroup

/-- The actual coefficient module `A_L` for an abstract Galois extension
`L | K`: restrict the global representation to `G_K`, take `G_L`-fixed
vectors, and descend the action to `G_K / G_L`.

The subgroup occurring in the quotient is `G_L` viewed inside `G_K`. -/
noncomputable def extensionFixedRepresentation {G : Type} [Group G]
    [TopologicalSpace G] (A : Rep.{0} ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    Rep ℤ (K.toSubgroup ⧸ extensionSubgroup K L hLK) := by
  exact Rep.quotientToInvariants
    (Rep.res K.toSubgroup.subtype A)
    (extensionSubgroup K L hLK)

/-- **the finite-cyclic cohomology calculation.**  If `G` is finite cyclic, then
`H¹(G,A) ≅ H⁻¹(G,A)`.

The right-hand side is the actual homology object
`ker(N_G) / im(ρ(g) - 1)`, not a compatibility placeholder. -/
noncomputable def finiteCyclicH1IsoTateHMinusOne {G : Type} [Group G] [Fintype G]
    (A : Rep.{0} ℤ G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    groupCohomology.H1 A ≅ tateCohomology A (-1) := by
  letI : IsCyclic G := isCyclic_of_generator g hg
  letI : CommGroup G := IsCyclic.commGroup (α := G)
  let e :
      groupCohomology.H1 A ≅
        (Rep.FiniteCyclicGroup.subCompNormHom A g).homology := by
    simpa using
      (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 (by simp))
  exact e ≪≫ (TateCohomology.isoFiniteCyclicNegOne A g hg).symm

/-- Elementwise content of the vanishing condition in the cyclic norm-kernel vanishing condition: every
norm-zero element is in the image of `ρ(g) - 1`.  This is the source used in
the cyclic step of abstract Kummer theory; the conclusion is extracted from
the actual homology object rather than assumed separately. -/
theorem normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
    {G : Type} [Group G] [Fintype G]
    (A : Rep.{0} ℤ G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hzero : Limits.IsZero (tateCohomology A (-1))) :
    ∀ x : A.V, A.norm.hom x = 0 →
      ∃ y : A.V, A.ρ g y - y = x := by
  let : IsCyclic G := isCyclic_of_generator g hg
  let : CommGroup G := IsCyclic.commGroup (α := G)
  have hH1 : Limits.IsZero (groupCohomology.H1 A) :=
    Limits.IsZero.of_iso hzero (finiteCyclicH1IsoTateHMinusOne A g hg)
  let : Subsingleton (groupCohomology.H1 A) :=
    ModuleCat.subsingleton_of_isZero hH1
  intro x hx
  let : Module ℤ A.V := A.hV2
  let x' : LinearMap.ker A.norm.hom.toLinearMap := ⟨x, hx⟩
  have hclass :
      Rep.FiniteCyclicGroup.groupCohomologyπOdd A g hg 1 (by simp) x' = 0 :=
    Subsingleton.elim _ _
  rcases (Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff
    A g hg 1 (by simp) x').1 hclass with ⟨y, hy⟩
  exact ⟨y, by simpa [Rep.sub_hom] using hy⟩

end
end CyclicCohomology
end

section
-- module Solutions.OAIQ244_DUKE.ProfiniteIntegers_TopologicalGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ClassFormation

/-!
# normalized degree and Frobenius theory: topological generation

This file contains the small amount of topological-generation theory used in
the construction of Frobenius fixed fields, next to its sole application.
-/

open Set
open scoped Topology Pointwise

universe u v

section

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A set topologically generates a group when the closure of the abstract
subgroup it generates is the whole group. -/
def TopologicallyGenerates (X : Set G) : Prop :=
  (Subgroup.closure X).topologicalClosure = ⊤

/-- Topological generation is equivalently density of the generated abstract
subgroup. -/
theorem topologicallyGenerates_iff_dense {X : Set G} :
    TopologicallyGenerates (G := G) X ↔
      Dense ((Subgroup.closure X : Subgroup G) : Set G) := by
  rw [TopologicallyGenerates, SetLike.ext'_iff, Subgroup.topologicalClosure_coe,
    Subgroup.coe_top, dense_iff_closure_eq]

/-- The closed subgroup topologically generated by a set. -/
def closedSubgroupGenerated (X : Set G) : ClosedSubgroup G where
  toSubgroup := (Subgroup.closure X).topologicalClosure
  isClosed' := Subgroup.isClosed_topologicalClosure _

/-- The canonical family in the closed subgroup that it generates. -/
def closedSubgroupGeneratedMap {A : Type v} (φ : A → G) :
    A → (closedSubgroupGenerated (G := G) (Set.range φ) : Subgroup G) :=
  fun a =>
    ⟨φ a, Subgroup.le_topologicalClosure _
      (Subgroup.subset_closure ⟨a, rfl⟩)⟩

/-- The canonical family topologically generates its closed generated
subgroup. -/
theorem closedSubgroupGeneratedMap_topologicallyGenerates {A : Type v}
    (φ : A → G) :
    TopologicallyGenerates
      (G := (closedSubgroupGenerated (G := G) (Set.range φ) : Subgroup G))
      (Set.range (closedSubgroupGeneratedMap (G := G) φ)) := by
  let K : ClosedSubgroup G := closedSubgroupGenerated (G := G) (Set.range φ)
  let φK : A → (K : Subgroup G) := closedSubgroupGeneratedMap (G := G) φ
  let L : Subgroup (K : Subgroup G) := Subgroup.closure (Set.range φK)
  have hmap :
      Subgroup.map (K : Subgroup G).subtype L =
        Subgroup.closure (Set.range φ) := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      rintro y ⟨a, rfl⟩
      exact Subgroup.subset_closure ⟨a, rfl⟩
    · rw [Subgroup.closure_le]
      rintro y ⟨a, rfl⟩
      change φ a ∈ Subgroup.map (K : Subgroup G).subtype L
      exact ⟨φK a, Subgroup.subset_closure ⟨a, rfl⟩, rfl⟩
  have himage :
      ((Subtype.val : ↥(K : Subgroup G) → G) ''
          ((L : Subgroup ↥(K : Subgroup G)) : Set ↥(K : Subgroup G))) =
        ((Subgroup.map (K : Subgroup G).subtype L : Subgroup G) : Set G) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      exact ⟨z, hz, hzy⟩
  rw [topologicallyGenerates_iff_dense, dense_iff_closure_eq]
  ext y
  constructor
  · intro _
    simp only [mem_univ]
  · intro _
    change y ∈ closure ((L : Subgroup K) : Set K)
    rw [closure_subtype]
    change (y : G) ∈
      closure
        (((Subtype.val : ↥(K : Subgroup G) → G) ''
          ((L : Subgroup ↥(K : Subgroup G)) : Set ↥(K : Subgroup G))))
    rw [himage, hmap]
    change (y : G) ∈
      ((Subgroup.closure (Set.range φ)).topologicalClosure : Set G)
    exact y.2

/-- Membership in a closed generated subgroup is preserved by a continuous
homomorphism after mapping the generating set. -/
theorem map_mem_closedSubgroupGenerated_image
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : G →ₜ* H) {X : Set G} {y : G}
    (hy : y ∈ (closedSubgroupGenerated (G := G) X : Subgroup G)) :
    φ y ∈ (closedSubgroupGenerated (G := H) (φ '' X) : Subgroup H) := by
  let K : Subgroup G :=
    (closedSubgroupGenerated (G := H) (φ '' X) : Subgroup H).comap
      (φ : G →* H)
  have hX : X ⊆ K := by
    intro x hx
    exact Subgroup.le_topologicalClosure _
      (Subgroup.subset_closure ⟨x, hx, rfl⟩)
  have hKclosed : IsClosed (K : Set G) := by
    change IsClosed {x : G | φ x ∈
      (closedSubgroupGenerated (G := H) (φ '' X) : Subgroup H)}
    exact (closedSubgroupGenerated (G := H) (φ '' X)).isClosed'.preimage
      φ.continuous
  exact
    (Subgroup.topologicalClosure_minimal _
      ((Subgroup.closure_le (K := K)).2 hX) hKclosed) hy

/-- The singleton form of functoriality of closed topological generation. -/
theorem map_mem_closedSubgroupGenerated_singleton
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : G →ₜ* H) (x : G) {y : G}
    (hy : y ∈
      (closedSubgroupGenerated (G := G) ({x} : Set G) : Subgroup G)) :
    φ y ∈
      (closedSubgroupGenerated (G := H) ({φ x} : Set H) : Subgroup H) := by
  simpa using
    (map_mem_closedSubgroupGenerated_image (G := G) (H := H) φ
      (X := ({x} : Set G)) hy)

/-- A dense image of the infinite cyclic group is topologically generated by
the image of `1`. -/
theorem topologicallyGenerates_singleton_of_denseRange_mint
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : Multiplicative ℤ →* H) (hf : DenseRange f) :
    TopologicallyGenerates
      (G := H) ({f (Multiplicative.ofAdd 1)} : Set H) := by
  let g : H := f (Multiplicative.ofAdd 1)
  have hsubset :
      Set.range f ⊆
        (((Subgroup.closure ({g} : Set H)).topologicalClosure : Subgroup H) :
          Set H) := by
    intro y hy
    rcases hy with ⟨n, rfl⟩
    have hz : f n ∈ Subgroup.zpowers g := by
      have hEq : f n = g ^ n.toAdd := by
        simpa [g] using (MonoidHom.apply_mint (f := f) (n := n))
      rw [hEq]
      exact (Subgroup.zpowers g).zpow_mem (Subgroup.mem_zpowers g) n.toAdd
    exact Subgroup.le_topologicalClosure _
      (by simpa [g, Subgroup.zpowers_eq_closure] using hz)
  have hclosure :
      closure (Set.range f) ⊆
        (((Subgroup.closure ({g} : Set H)).topologicalClosure : Subgroup H) :
          Set H) :=
    closure_minimal hsubset (Subgroup.isClosed_topologicalClosure _)
  rw [TopologicallyGenerates]
  apply top_unique
  intro x _hx
  have hx' : x ∈ closure (Set.range f) := by
    rw [hf.closure_range]
    simp only [mem_univ]
  exact hclosure hx'

/-- Topological generation pushes forward along a continuous surjective
homomorphism. -/
theorem topologicallyGenerates_image_of_continuousSurjective
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →* H) (hf : Continuous f) (hfsurj : Function.Surjective f)
    {X : Set G} (hX : TopologicallyGenerates (G := G) X) :
    TopologicallyGenerates (G := H) (f '' X) := by
  have hmap :
      (Subgroup.closure X).map f = Subgroup.closure (f '' X) := by
    simpa using MonoidHom.map_closure f X
  have htop :
      ((Subgroup.closure X).map f).topologicalClosure = ⊤ := by
    exact DenseRange.topologicalClosure_map_subgroup
      (f := f) (hf := hf) (hf' := hfsurj.denseRange)
      (by simpa [TopologicallyGenerates] using hX)
  rw [TopologicallyGenerates, ← hmap]
  exact htop

/-- Topological generation descends to a quotient by a normal subgroup. -/
theorem topologicallyGenerates_quotient_image
    (N : Subgroup G) [N.Normal]
    {X : Set G} (hX : TopologicallyGenerates (G := G) X) :
    TopologicallyGenerates
      (G := G ⧸ N) ((QuotientGroup.mk' N) '' X) :=
  topologicallyGenerates_image_of_continuousSurjective
    (G := G) (H := G ⧸ N) (QuotientGroup.mk' N)
    continuous_quotient_mk' (QuotientGroup.mk'_surjective N) hX

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.ProfiniteIntegers_ProfiniteIntegerCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

structure ZHatIndex where
  modulus : ℕ
  positive : 0 < modulus

instance instNeZeroNatModulus (i : ZHatIndex) : NeZero i.modulus :=
  ⟨Nat.ne_of_gt i.positive⟩

def zHatIndex (n : ℕ) (hn : 0 < n) : ZHatIndex :=
  ⟨n, hn⟩

abbrev ZHatAmbient : Type 0 :=
  ∀ i : ZHatIndex, ZMod i.modulus

def zHatDiagonal : ℤ →+* ZHatAmbient where
  toFun a i := (a : ZMod i.modulus)
  map_zero' := by
    funext i
    exact Int.cast_zero
  map_one' := by
    funext i
    exact Int.cast_one
  map_add' a b := by
    funext i
    exact Int.cast_add a b
  map_mul' a b := by
    funext i
    exact Int.cast_mul a b

def zHatIntegerSubring : Subring ZHatAmbient :=
  zHatDiagonal.range

abbrev ZHatClosureModel : Type 0 :=
  zHatIntegerSubring.topologicalClosure

/-- The profinite completion `ℤ̂ = lim ℤ/nℤ` over all positive moduli.

This is deliberately a `def`, rather than an `abbrev`: clients use the
reduction maps and the representation equivalence below instead of depending
on the closure subtype. -/
def ZHat : Type 0 :=
  ZHatClosureModel

/-- The closure model equips `ZHat` with its canonical commutative ring structure. -/
instance instCommRingZHat : CommRing ZHat := by
  change CommRing ZHatClosureModel
  infer_instance

/-- The closure model equips `ZHat` with its subspace topology. -/
instance instTopologicalSpaceZHat : TopologicalSpace ZHat := by
  change TopologicalSpace ZHatClosureModel
  infer_instance

/-- Ring operations on `ZHat` are continuous for the closure-model topology. -/
instance instIsTopologicalRingZHat : IsTopologicalRing ZHat := by
  change IsTopologicalRing ZHatClosureModel
  infer_instance

/-- The closure-model topology on `ZHat` is Hausdorff. -/
instance instT2SpaceZHat : T2Space ZHat := by
  change T2Space ZHatClosureModel
  infer_instance

/-- The profinite integer closure model is compact. -/
instance instCompactSpaceZHat : CompactSpace ZHat :=
  Topology.IsClosedEmbedding.compactSpace
    (Subring.isClosed_topologicalClosure zHatIntegerSubring).isClosedEmbedding_subtypeVal

/-- The canonical continuous reduction `ℤ̂ → ℤ/nℤ`. -/
def zHatReduction (n : ℕ) (hn : 0 < n) :
    ContinuousAddMonoidHom ZHat (ZMod n) where
  toFun x := (show ZHatClosureModel from x).1 (zHatIndex n hn)
  map_zero' := rfl
  map_add' _ _ := rfl
  continuous_toFun := by
    change Continuous
      (fun x : ZHatClosureModel => x.1 (zHatIndex n hn))
    exact (continuous_apply (zHatIndex n hn)).comp continuous_subtype_val

/-- Reduction agrees with the ordinary integer cast.  This is the public
computation rule; it does not expose the closure model used to construct
`ZHat`. -/
@[simp] theorem zHatReduction_intCast (n : ℕ) (hn : 0 < n) (a : ℤ) :
    zHatReduction n hn (a : ZHat) = (a : ZMod n) :=
  rfl

/-- Reduction modulo one sends every profinite integer to the unique residue class. -/
@[simp] theorem zHatReduction_one (n : ℕ) (hn : 0 < n) :
    zHatReduction n hn (1 : ZHat) = 1 := by
  simpa only [Int.cast_one] using zHatReduction_intCast n hn 1

namespace ZHat

/-- Profinite integers are determined by all positive-modulus reductions. -/
@[ext]
theorem ext {x y : ZHat}
    (h : ∀ n (hn : 0 < n), zHatReduction n hn x = zHatReduction n hn y) :
    x = y := by
  apply Subtype.ext
  funext i
  rcases i with ⟨n, hn⟩
  exact h n hn

end ZHat

/-- Reduction maps commute with reduction along a divisibility relation. -/
theorem zHatReduction_transition {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) (x : ZHat) :
    ZMod.castHom hmn (ZMod m) (zHatReduction n hn x) =
      zHatReduction m hm x := by
  let f : ZHatAmbient → ZMod m :=
    fun z => ZMod.castHom hmn (ZMod m) (z (zHatIndex n hn))
  let g : ZHatAmbient → ZMod m :=
    fun z => z (zHatIndex m hm)
  have hfg : Set.EqOn f g (zHatIntegerSubring : Set ZHatAmbient) := by
    rintro _ ⟨a, rfl⟩
    exact map_intCast (ZMod.castHom hmn (ZMod m)) a
  have hf : Continuous f :=
    continuous_of_discreteTopology.comp (continuous_apply (zHatIndex n hn))
  have hg : Continuous g :=
    continuous_apply (zHatIndex m hm)
  exact hfg.closure hf hg x.property

/-- The ordinary integers have dense image in their profinite completion. -/
theorem denseRange_intCast_zHat :
    DenseRange (Int.castRingHom ZHat) := by
  have hinclusion : DenseRange
      (Set.inclusion (Subring.le_topologicalClosure zHatIntegerSubring)) := by
    apply (denseRange_inclusion_iff
      (Subring.le_topologicalClosure zHatIntegerSubring)).2
    change closure (zHatIntegerSubring : Set ZHatAmbient) ⊆
      closure (zHatIntegerSubring : Set ZHatAmbient)
    exact Set.Subset.rfl
  have hdiagonal : DenseRange zHatDiagonal.rangeRestrict :=
    zHatDiagonal.rangeRestrict_surjective.denseRange
  have hcomp : DenseRange
      (Set.inclusion (Subring.le_topologicalClosure zHatIntegerSubring) ∘
        zHatDiagonal.rangeRestrict) :=
    hinclusion.comp hdiagonal
      (continuous_inclusion
        (Subring.le_topologicalClosure zHatIntegerSubring))
  have heq :
      Set.inclusion (Subring.le_topologicalClosure zHatIntegerSubring) ∘
          zHatDiagonal.rangeRestrict =
        (fun a : ℤ => Int.castRingHom ZHat a) := by
    funext a
    apply Subtype.ext
    funext i
    rfl
  rw [heq] at hcomp
  exact hcomp

/-- The element `1` topologically generates the additive profinite integers,
written multiplicatively. -/
theorem zHatOne_topologicallyGenerates :
    TopologicallyGenerates
      (G := Multiplicative ZHat)
      ({Multiplicative.ofAdd (1 : ZHat)} : Set (Multiplicative ZHat)) := by
  let f : Multiplicative ℤ →* Multiplicative ZHat :=
    AddMonoidHom.toMultiplicative (Int.castRingHom ZHat).toAddMonoidHom
  have hf : DenseRange f := by
    have hOfAdd :
        DenseRange (Multiplicative.ofAdd : ZHat → Multiplicative ZHat) :=
      (show Function.Surjective
          (Multiplicative.ofAdd : ZHat → Multiplicative ZHat) from
        fun x => ⟨Multiplicative.toAdd x, rfl⟩).denseRange
    have hCast :
        DenseRange
          (Multiplicative.ofAdd ∘ fun a : ℤ => (a : ZHat)) :=
      hOfAdd.comp denseRange_intCast_zHat continuous_id
    have hToAdd :
        DenseRange (Multiplicative.toAdd : Multiplicative ℤ → ℤ) :=
      (show Function.Surjective
          (Multiplicative.toAdd : Multiplicative ℤ → ℤ) from
        fun a => ⟨Multiplicative.ofAdd a, rfl⟩).denseRange
    simpa [f, Function.comp_def] using
      hCast.comp hToAdd continuous_of_discreteTopology
  simpa [f] using
    (topologicallyGenerates_singleton_of_denseRange_mint f hf)

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.ProfiniteIntegers_ProfiniteInteger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ClassFormation

/-!
# normalized degree and Frobenius theory: the profinite integers

This file supplies the source-producing facts about `ℤ̂` used to normalize the
surjection in the opening datum of abstract valuation theory.  In particular,
multiplication by a positive integer identifies `ℤ̂` with the closed subgroup
`n ℤ̂`, which is the kernel of reduction modulo `n`.
-/

noncomputable section

/-- Distinct natural powers of the canonical positive generator of `ℤ̂` are
distinct.  This common exponent-uniqueness fact is independent of the later
reciprocity constructions that use it. -/
theorem proCIntegerOne_pow_nat_injective :
    Function.Injective (fun n : ℕ =>
      (Multiplicative.ofAdd (1 : ZHat)) ^ n) := by
  intro a b hab
  let m := a + b + 1
  have hm : 0 < m := by simp [m]
  have ha : a < m := by omega
  have hb : b < m := by omega
  have habAdd := congrArg Multiplicative.toAdd hab
  have habAdd' : a • (1 : ZHat) = b • (1 : ZHat) := by
    simpa using habAdd
  have habRed := congrArg (fun z : ZHat => zHatReduction m hm z) habAdd'
  have hredOne : zHatReduction m hm (1 : ZHat) = 1 :=
    rfl
  change zHatReduction m hm (a • (1 : ZHat)) =
      zHatReduction m hm (b • (1 : ZHat)) at habRed
  rw [map_nsmul, map_nsmul, hredOne] at habRed
  have hval := congrArg ZMod.val habRed
  simpa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hval

/-- Multiplication by `n` on the additive group of the profinite integers. -/
def zHatMulNat (n : ℕ) : ContinuousAddMonoidHom ZHat ZHat where
  toFun := fun x => n • x
  map_zero' := nsmul_zero n
  map_add' := fun x y => nsmul_add x y n
  continuous_toFun := continuous_nsmul n

/-- The defining evaluation formula for `zHatMulNat` is `zHatMulNat n x = n • x`. -/
@[simp]
theorem zHatMulNat_apply (n : ℕ) (x : ZHat) :
    zHatMulNat n x = n • x :=
  rfl

theorem zmod_cast_eq_of_nsmul_eq
    {n m : ℕ} (hn : 0 < n) {a b : ZMod (n * m)}
    (h : n • a = n • b) :
    ZMod.castHom (show m ∣ n * m from ⟨n, by simp [Nat.mul_comm]⟩) (ZMod m) a =
      ZMod.castHom (show m ∣ n * m from ⟨n, by simp [Nat.mul_comm]⟩) (ZMod m) b := by
  rcases ZMod.intCast_surjective a with ⟨a, rfl⟩
  rcases ZMod.intCast_surjective b with ⟨b, rfl⟩
  rw [ZMod.castHom_apply, ZMod.castHom_apply]
  rw [ZMod.cast_intCast
      (R := ZMod m) (n := n * m) (m := m)
      (show m ∣ n * m from ⟨n, by simp [Nat.mul_comm]⟩) a,
    ZMod.cast_intCast
      (R := ZMod m) (n := n * m) (m := m)
      (show m ∣ n * m from ⟨n, by simp [Nat.mul_comm]⟩) b]
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hzero : (n • ((a - b : ℤ) : ZMod (n * m))) = 0 := by
    rw [Int.cast_sub, nsmul_sub, h, sub_self]
  have hdiv : ((n * m : ℕ) : ℤ) ∣ (n : ℤ) * (a - b) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [nsmul_eq_mul, Int.cast_natCast, Int.cast_mul] using hzero
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  apply (mul_dvd_mul_iff_left hn0).mp
  simpa [Nat.cast_mul] using hdiv

/-- Multiplication by a positive integer is injective on `ℤ̂`. -/
theorem zHatMulNat_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (zHatMulNat n) := by
  intro x y hxy
  apply ZHat.ext
  intro m hm
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  have hdiv : m ∣ n * m := ⟨n, by simp [Nat.mul_comm]⟩
  have hj : n • zHatReduction (n * m) hnm x =
      n • zHatReduction (n * m) hnm y := by
    simpa only [zHatMulNat_apply, map_nsmul] using
      congrArg (fun z : ZHat => zHatReduction (n * m) hnm z) hxy
  rw [← zHatReduction_transition hm hnm hdiv x,
    ← zHatReduction_transition hm hnm hdiv y]
  exact zmod_cast_eq_of_nsmul_eq hn hj

/-- The image `n ℤ̂` is closed. -/
theorem isClosed_zHatMulNat_range (n : ℕ) :
    IsClosed ((zHatMulNat n).toAddMonoidHom.range : Set ZHat) := by
  rw [AddMonoidHom.coe_range]
  exact (isCompact_range (map_continuous (zHatMulNat n))).isClosed

/-- Establishes the identity `zHatReduction n hn ((Int.castRingHom ZHat) a) = (a : ZMod n)`. -/
@[simp]
theorem zHatReduction_int (n : ℕ) (hn : 0 < n) (a : ℤ) :
    zHatReduction n hn
        ((Int.castRingHom ZHat) a) =
      (a : ZMod n) :=
  rfl

/-- Reduction modulo a positive integer is onto. -/
theorem zHatReduction_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (zHatReduction n hn) := by
  intro a
  rcases ZMod.intCast_surjective a with ⟨a, rfl⟩
  exact ⟨(Int.castRingHom ZHat) a, rfl⟩

/--
Establishes the identity `zHatMulNat n ((Int.castRingHom ZHat) a) = (Int.castRingHom ZHat) ((n :
ℤ) * a)`.
-/
@[simp]
theorem zHatMulNat_int (n : ℕ) (a : ℤ) :
    zHatMulNat n ((Int.castRingHom ZHat) a) =
      (Int.castRingHom ZHat) ((n : ℤ) * a) := by
  apply ZHat.ext
  intro m hm
  change n • (a : ZMod m) = (((n : ℤ) * a : ℤ) : ZMod m)
  simp [nsmul_eq_mul]

/-- The subgroup `n ℤ̂` is exactly the kernel of reduction modulo `n`. -/
theorem zHatMulNat_range_eq_ker_reduction (n : ℕ) (hn : 0 < n) :
    (zHatMulNat n).toAddMonoidHom.range =
      (zHatReduction n hn).toAddMonoidHom.ker := by
  apply AddSubgroup.ext
  intro y
  constructor
  · rintro ⟨x, rfl⟩
    change zHatReduction n hn (zHatMulNat n x) = 0
    change n • zHatReduction n hn x = 0
    simp [nsmul_eq_mul]
  · intro hy
    let K : Set ZHat :=
      ((zHatReduction n hn).toAddMonoidHom.ker : Set ZHat)
    let D : Set ZHat :=
      Set.range (Int.castRingHom ZHat)
    have hKopen : IsOpen K := by
      change IsOpen ((zHatReduction n hn) ⁻¹' ({0} : Set (ZMod n)))
      have hzeroOpen : IsOpen ({0} : Set (ZMod n)) := isOpen_discrete _
      exact hzeroOpen.preimage (map_continuous (zHatReduction n hn))
    have hDdense : Dense D := by
      exact denseRange_intCast_zHat
    have hKD : K ∩ D ⊆
        ((zHatMulNat n).toAddMonoidHom.range : Set ZHat) := by
      rintro _ ⟨hzK, a, rfl⟩
      have ha0 : (a : ZMod n) = 0 := by
        simpa [K] using hzK
      have hna : (n : ℤ) ∣ a :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd a n).mp ha0
      rcases hna with ⟨b, rfl⟩
      refine ⟨(Int.castRingHom ZHat) b, ?_⟩
      exact zHatMulNat_int n b
    have hyClosure : y ∈ closure (K ∩ D) :=
      (hDdense.open_subset_closure_inter hKopen) hy
    exact (closure_minimal hKD (isClosed_zHatMulNat_range n)) hyClosure

/-- The additive index of `n ℤ̂` in `ℤ̂` is `n`. -/
theorem zHatMulNat_range_index (n : ℕ) (hn : 0 < n) :
    (zHatMulNat n).toAddMonoidHom.range.index = n := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [zHatMulNat_range_eq_ker_reduction n hn,
    AddSubgroup.index_ker]
  rw [AddMonoidHom.range_eq_top_of_surjective
    (zHatReduction n hn).toAddMonoidHom (zHatReduction_surjective n hn)]
  calc
    Nat.card (↑(⊤ : AddSubgroup (ZMod n))) = Nat.card (ZMod n) :=
      Nat.card_congr
        { toFun := fun x => x.1
          invFun := fun x => ⟨x, AddSubgroup.mem_top x⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun _ => rfl }
    _ = n := Nat.card_zmod n

/-- Every additive subgroup of finite nonzero index in `ℤ̂` is the expected
principal subgroup.  Closedness is not needed: the quotient is abelian, so its
cardinality annihilates every quotient class, and comparison of indices forces
equality. -/
theorem zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero
    (H : AddSubgroup ZHat) (hH : H.index ≠ 0) :
    H = (zHatMulNat H.index).toAddMonoidHom.range := by
  have hle : (zHatMulNat H.index).toAddMonoidHom.range ≤ H := by
    rintro y ⟨x, rfl⟩
    exact H.nsmul_index_mem x
  have hrangeIndex :
      (zHatMulNat H.index).toAddMonoidHom.range.index = H.index :=
    zHatMulNat_range_index H.index (Nat.pos_of_ne_zero hH)
  have hrel :
      (zHatMulNat H.index).toAddMonoidHom.range.relIndex H = 1 := by
    have heq :
        (zHatMulNat H.index).toAddMonoidHom.range.relIndex H * H.index =
          H.index :=
      (AddSubgroup.relIndex_mul_index hle).trans hrangeIndex
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hH)
    simpa only [one_mul] using heq
  exact le_antisymm (AddSubgroup.relIndex_eq_one.mp hrel) hle

/-- Index-explicit form of the classification of finite-index additive
subgroups of `ℤ̂`. -/
theorem zHatAddSubgroup_eq_mulNat_range_of_index_eq
    (H : AddSubgroup ZHat) {n : ℕ} (hn : 0 < n) (hindex : H.index = n) :
    H = (zHatMulNat n).toAddMonoidHom.range := by
  subst n
  exact zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero H
    (Nat.ne_of_gt hn)

/-- Multiplication by `n > 0` identifies `ℤ̂` continuously with its image. -/
noncomputable def zHatMulNatRangeEquiv (n : ℕ) (hn : 0 < n) :
    ZHat ≃ₜ+ (zHatMulNat n).toAddMonoidHom.range := by
  let e : ZHat ≃+ (zHatMulNat n).toAddMonoidHom.range :=
    AddMonoidHom.ofInjective (zHatMulNat_injective hn)
  have he : Continuous e := by
    change Continuous fun x : ZHat =>
      (⟨zHatMulNat n x, ⟨x, rfl⟩⟩ : (zHatMulNat n).toAddMonoidHom.range)
    exact Continuous.subtype_mk (map_continuous (zHatMulNat n)) fun x => ⟨x, rfl⟩
  let h : ZHat ≃ₜ (zHatMulNat n).toAddMonoidHom.range :=
    he.homeoOfEquivCompactToT2
  exact
    { e with
      continuous_toFun := h.continuous
      continuous_invFun := h.symm.continuous }

/-- Division by `n` on the subgroup `n ℤ̂`. -/
noncomputable def zHatDivide (n : ℕ) (hn : 0 < n) :
    ContinuousAddMonoidHom ((zHatMulNat n).toAddMonoidHom.range) ZHat :=
  (zHatMulNatRangeEquiv n hn).symm

/-- Establishes the identity `zHatMulNat n (zHatDivide n hn y) = y.1`. -/
@[simp]
theorem zHatMulNat_zHatDivide (n : ℕ) (hn : 0 < n)
    (y : (zHatMulNat n).toAddMonoidHom.range) :
    zHatMulNat n (zHatDivide n hn y) = y.1 := by
  change ((zHatMulNatRangeEquiv n hn)
    ((zHatMulNatRangeEquiv n hn).symm y)).1 = y.1
  exact congrArg Subtype.val ((zHatMulNatRangeEquiv n hn).apply_symm_apply y)

/-- Establishes the identity `zHatDivide n hn ⟨zHatMulNat n x, ⟨x, rfl⟩⟩ = x`. -/
@[simp]
theorem zHatDivide_zHatMulNat (n : ℕ) (hn : 0 < n) (x : ZHat) :
    zHatDivide n hn
      ⟨zHatMulNat n x, ⟨x, rfl⟩⟩ = x := by
  change (zHatMulNatRangeEquiv n hn).symm
    ((zHatMulNatRangeEquiv n hn) x) = x
  exact (zHatMulNatRangeEquiv n hn).symm_apply_apply x

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_Fields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# normalized degree and Frobenius theory: the initial datum and abstract fields

This file records the opening datum of abstract valuation theory and the
residue and ramification indices attached to inclusions of abstract fields.
As in, a field is represented contravariantly by a closed subgroup of the
ambient profinite group.
-/

noncomputable section

universe u

/-- The multiplicative presentation of `ℤ̂`; multiplication here is addition
in the profinite integers. -/
abbrev ZHatMul : Type 0 := Multiplicative ZHat

/-- The degree datum on a topological group: a continuous surjection
`d : G → ℤ̂`.  Profinite hypotheses belong to the ambient group and are
requested only by results that use them; they are not duplicated as proof
fields inside this datum. -/
structure DegreeData (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The continuous degree homomorphism to the profinite integers. -/
  degree : G →ₜ* ZHatMul
  /-- The degree homomorphism is surjective. -/
  degree_surjective : Function.Surjective degree

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The distinguished base field, represented contravariantly by the full
ambient group. -/
def baseField (G : Type u) [Group G] [TopologicalSpace G] : ClosedSubgroup G where
  toSubgroup := ⊤
  isClosed' := isClosed_univ

/-- The distinguished base field is represented by the full ambient subgroup. -/
@[simp]
theorem baseField_toSubgroup (G : Type u) [Group G] [TopologicalSpace G] :
    (baseField G).toSubgroup = ⊤ :=
  rfl

/-- Every abstract field lies over the distinguished base field. -/
theorem le_baseField (K : ClosedSubgroup G) :
    K.toSubgroup ≤ (baseField G).toSubgroup :=
  le_top

namespace DegreeData

/-- The inertia group `I = ker d`, including its closedness. -/
def inertia (D : DegreeData G) : ClosedSubgroup G where
  toSubgroup := D.degree.toMonoidHom.ker
  isClosed' := by
    change IsClosed {g : G | (D.degree g).toAdd = 0}
    exact isClosed_eq D.degree.continuous_toFun continuous_const

/-- An element is inertial exactly when its degree is the multiplicative identity. -/
@[simp]
theorem mem_inertia_iff (D : DegreeData G) (g : G) :
    g ∈ D.inertia ↔ D.degree g = 1 :=
  Iff.rfl

/-- The restriction of `d` to the subgroup representing an abstract field. -/
def restrictedDegree (D : DegreeData G) (K : ClosedSubgroup G) :
    K.toSubgroup →ₜ* ZHatMul where
  toMonoidHom := D.degree.toMonoidHom.comp K.toSubgroup.subtype
  continuous_toFun := D.degree.continuous_toFun.comp continuous_subtype_val

/-- The restricted degree map evaluates through the underlying ambient element. -/
@[simp]
theorem restrictedDegree_apply (D : DegreeData G) (K : ClosedSubgroup G)
    (k : K.toSubgroup) : D.restrictedDegree K k = D.degree k.1 :=
  rfl

/-- The image `d(G_K)` in `ℤ̂`. -/
def fieldImage (D : DegreeData G) (K : ClosedSubgroup G) : Subgroup ZHatMul :=
  (D.restrictedDegree K).toMonoidHom.range

/-- The field's degree image is the image of its subgroup under the ambient degree map. -/
theorem fieldImage_eq_map (D : DegreeData G) (K : ClosedSubgroup G) :
    D.fieldImage K = K.toSubgroup.map D.degree.toMonoidHom := by
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.1, k.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

/-- The inertia group `I_K = G_K ∩ I` over `K`. -/
def fieldInertia (D : DegreeData G) (K : ClosedSubgroup G) : ClosedSubgroup G :=
  K ⊓ D.inertia

/-- Field inertia consists of field elements whose ambient degree is one. -/
@[simp]
theorem mem_fieldInertia_iff (D : DegreeData G) (K : ClosedSubgroup G) (g : G) :
    g ∈ D.fieldInertia K ↔ g ∈ K ∧ D.degree g = 1 :=
  Iff.rfl

/-- `I_K` viewed inside `G_K`; equivalently, the kernel of `d|G_K`. -/
def fieldInertiaWithin (D : DegreeData G) (K : ClosedSubgroup G) :
    Subgroup K.toSubgroup :=
  (D.restrictedDegree K).toMonoidHom.ker

/-- The degree kernel defining inertia inside a field subgroup is normal. -/
instance fieldInertiaWithin_normal (D : DegreeData G) (K : ClosedSubgroup G) :
    (D.fieldInertiaWithin K).Normal := by
  rw [fieldInertiaWithin]
  infer_instance

/-- Membership in internal field inertia is equivalent to having ambient degree one. -/
@[simp]
theorem mem_fieldInertiaWithin_iff (D : DegreeData G) (K : ClosedSubgroup G)
    (k : K.toSubgroup) : k ∈ D.fieldInertiaWithin K ↔ D.degree k.1 = 1 :=
  Iff.rfl

/-- The absolute residue degree as the cardinality of the actual quotient of
`ZHat` by the degree image. -/
noncomputable def residueDegreeCardinal (D : DegreeData G)
    (K : ClosedSubgroup G) : Cardinal :=
  relativeIndexCardinal
    (show D.fieldImage K ≤ (⊤ : Subgroup ZHatMul) from le_top)

/-- The actual quotient whose cardinality is the absolute residue degree. -/
def residueQuotient (D : DegreeData G) (K : ClosedSubgroup G) : Type :=
  (⊤ : Subgroup ZHatMul) ⧸ (D.fieldImage K).subgroupOf ⊤

/-- The cardinal residue degree is the cardinality of the concrete residue quotient. -/
@[simp] theorem residueDegreeCardinal_eq_mk_residueQuotient
    (D : DegreeData G) (K : ClosedSubgroup G) :
    D.residueDegreeCardinal K = Cardinal.mk (D.residueQuotient K) :=
  rfl

/-- The distinguished base field has absolute residue degree one, without
passing through a natural-valued subgroup index. -/
@[simp] theorem residueDegreeCardinal_baseField (D : DegreeData G) :
    D.residueDegreeCardinal (baseField G) = 1 := by
  change
    intersectionIndexCardinal (D.fieldImage (baseField G))
      (⊤ : Subgroup ZHatMul) = 1
  rw [D.fieldImage_eq_map, baseField_toSubgroup,
    Subgroup.map_top_of_surjective _ D.degree_surjective]
  change Cardinal.mk (↥(⊤ : Subgroup ZHatMul) ⧸ ⊤) = 1
  let : Subsingleton (↥(⊤ : Subgroup ZHatMul) ⧸
      (⊤ : Subgroup ↥(⊤ : Subgroup ZHatMul))) :=
    QuotientGroup.subsingleton_quotient_top
  exact Cardinal.mk_eq_one _

/-- An abstract field together with finiteness of its actual degree-image
quotient.  Its numerical residue degree is therefore genuinely positive. -/
structure FiniteResidueAbstractField (D : DegreeData G) where
  /-- The closed subgroup representing the abstract field. -/
  field : ClosedSubgroup G
  /-- The field's residue quotient is finite. -/
  finiteResidueQuotient : Finite (D.residueQuotient field)

namespace FiniteResidueAbstractField

variable {D : DegreeData G}

/-- The underlying subgroup. -/
@[implicit_reducible]
def toSubgroup (K : FiniteResidueAbstractField D) : Subgroup G :=
  K.field.toSubgroup

/-- A finite-residue abstract field supplies finiteness of its residue quotient. -/
instance instFiniteResidueQuotientField (K : FiniteResidueAbstractField D) :
    Finite (D.residueQuotient K.field) :=
  K.finiteResidueQuotient

/-- The positive absolute residue degree. -/
noncomputable def residueDegree (K : FiniteResidueAbstractField D) : ℕ+ := by
  letI : Nonempty (D.residueQuotient K.field) := ⟨QuotientGroup.mk 1⟩
  exact ⟨Nat.card (D.residueQuotient K.field), Nat.card_pos⟩

/-- The natural value of the positive residue degree is the quotient's `Nat.card`. -/
@[simp] theorem residueDegree_coe (K : FiniteResidueAbstractField D) :
    (K.residueDegree : ℕ) = Nat.card (D.residueQuotient K.field) :=
  rfl

/-- Cardinal-to-positive-natural specialization at the finite boundary. -/
@[simp] theorem residueDegreeCardinal_eq_coe
    (K : FiniteResidueAbstractField D) :
    D.residueDegreeCardinal K.field = ((K.residueDegree : ℕ) : Cardinal) := by
  change Cardinal.mk (D.residueQuotient K.field) =
    (Nat.card (D.residueQuotient K.field) : Cardinal)
  exact Nat.cast_card.symm

end FiniteResidueAbstractField

end DegreeData

namespace DegreeData

/-- An abstract field extension, including the containment which makes the
notation `L / K` meaningful in the closed-subgroup model.  Keeping this proof
in the object prevents predicates for extensions from being formed for
unrelated closed subgroups. -/
structure AbstractExtension (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The closed subgroup contravariantly representing the extension field. -/
  field : ClosedSubgroup G
  /-- The closed subgroup contravariantly representing the base field. -/
  base : ClosedSubgroup G
  /-- Contravariance turns the field inclusion into this subgroup inclusion. -/
  below : field.toSubgroup ≤ base.toSubgroup

namespace AbstractExtension

/-- The subgroup of the base group represented by the extension field.  This
projection packages the proof-dependent `subgroupOf` construction behind the
extension object. -/
def subgroup (E : AbstractExtension G) : Subgroup E.base.toSubgroup :=
  extensionSubgroup E.base E.field E.below

/-- The actual relative coset space of an abstract extension. -/
def quotient (E : AbstractExtension G) : Type u :=
  E.base.toSubgroup ⧸ E.subgroup

/-- The honest cardinal degree of an arbitrary abstract extension.  Unlike
the raw natural-valued subgroup index, this does not encode infinity as zero. -/
noncomputable def degreeCardinal (E : AbstractExtension G) : Cardinal :=
  relativeIndexCardinal E.below

/-- The cardinal degree of an abstract extension is the cardinality of its coset space. -/
@[simp] theorem degreeCardinal_eq_mk_quotient (E : AbstractExtension G) :
    E.degreeCardinal = Cardinal.mk E.quotient :=
  rfl

/-- The relative residue degree of an arbitrary abstract extension, as the
cardinality of the actual coset type of degree images.  This is the canonical
general API: an infinite residue degree remains an infinite cardinal. -/
noncomputable def relativeResidueDegreeCardinal
    (E : AbstractExtension G) (D : DegreeData G) : Cardinal :=
  relativeIndexCardinal (Subgroup.map_mono (f := D.degree.toMonoidHom) E.below)

/-- The relative ramification index of an arbitrary abstract extension, as
the cardinality of the actual coset type inside the degree kernel.  In
particular, infinity is not encoded as zero. -/
noncomputable def relativeRamificationIndexCardinal
    (E : AbstractExtension G) (D : DegreeData G) : Cardinal :=
  relativeIndexCardinal
    (show E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker from
        inf_le_inf E.below le_rfl)

/-- The cardinal-valued fundamental identity for an arbitrary abstract
extension.  The residue cardinal is lifted from the universe of `ZHat`; no
finiteness assumption or infinite-index convention is involved. -/
theorem degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal
    (E : AbstractExtension G) (D : DegreeData G) :
    E.degreeCardinal =
      Cardinal.lift.{u} (E.relativeResidueDegreeCardinal D) *
        E.relativeRamificationIndexCardinal D := by
  simpa [degreeCardinal, relativeResidueDegreeCardinal,
    relativeRamificationIndexCardinal] using
    (relativeIndexCardinal_eq_map_mul_inf_ker
      D.degree.toMonoidHom E.below)

/-- Cardinal Frobenius residue-degree compatibility: the relative residue
cardinal times the absolute residue cardinal of the base is the absolute
residue cardinal of the extension field. -/
theorem relativeResidueDegreeCardinal_mul_residueDegreeCardinal
    (E : AbstractExtension G) (D : DegreeData G) :
    E.relativeResidueDegreeCardinal D * D.residueDegreeCardinal E.base =
      D.residueDegreeCardinal E.field := by
  change
    intersectionIndexCardinal
        (E.field.toSubgroup.map D.degree.toMonoidHom)
        (E.base.toSubgroup.map D.degree.toMonoidHom) *
      intersectionIndexCardinal (D.fieldImage E.base) (⊤ : Subgroup ZHatMul) =
        intersectionIndexCardinal (D.fieldImage E.field) (⊤ : Subgroup ZHatMul)
  rw [D.fieldImage_eq_map,
    D.fieldImage_eq_map]
  simpa only [relativeIndexCardinal] using
    (relativeIndexCardinal_mul
      (Subgroup.map_mono (f := D.degree.toMonoidHom) E.below)
      (show E.base.toSubgroup.map D.degree.toMonoidHom ≤
        (⊤ : Subgroup ZHatMul) from le_top))

/-- A composable tower of abstract extensions, represented by three closed
subgroups and the two adjacent containments. -/
structure Tower (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The closed subgroup representing the top field. -/
  top : ClosedSubgroup G
  /-- The closed subgroup representing the middle field. -/
  middle : ClosedSubgroup G
  /-- The closed subgroup representing the base field. -/
  base : ClosedSubgroup G
  /-- Contravariant containment for the top-to-middle extension. -/
  top_le_middle : top.toSubgroup ≤ middle.toSubgroup
  /-- Contravariant containment for the middle-to-base extension. -/
  middle_le_base : middle.toSubgroup ≤ base.toSubgroup

namespace Tower

variable (T : Tower G)

/-- The upper extension in a tower. -/
def topExtension : AbstractExtension G where
  field := T.top
  base := T.middle
  below := T.top_le_middle

/-- The lower extension in a tower. -/
def baseExtension : AbstractExtension G where
  field := T.middle
  base := T.base
  below := T.middle_le_base

/-- The composite extension in a tower. -/
def totalExtension : AbstractExtension G where
  field := T.top
  base := T.base
  below := T.top_le_middle.trans T.middle_le_base

/-- Cardinal degrees multiply in an arbitrary abstract-extension tower. -/
theorem degreeCardinal_mul :
    T.topExtension.degreeCardinal * T.baseExtension.degreeCardinal =
      T.totalExtension.degreeCardinal := by
  exact relativeIndexCardinal_mul T.top_le_middle T.middle_le_base

end Tower

/-- An abstract extension is unramified when the inertia subgroup of its base
is already contained in the subgroup representing its field.  This
containment is the definition; it does not pass through a natural-valued index
that would encode an infinite index as zero. -/
def IsUnramified (E : AbstractExtension G) (D : DegreeData G) : Prop :=
  E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup

/-- An abstract extension is totally ramified when the degree image of its
base is contained in the degree image of its field. -/
def IsTotallyRamified (E : AbstractExtension G) (D : DegreeData G) : Prop :=
  E.base.toSubgroup.map D.degree.toMonoidHom ≤
    E.field.toSubgroup.map D.degree.toMonoidHom

/-- An extension is unramified exactly when the inertia subgroup of its base
is contained in the subgroup representing its field.  The containment needed
to form the extension is carried by `E`. -/
theorem isUnramified_iff_inertia_le (E : AbstractExtension G) (D : DegreeData G) :
    E.IsUnramified D ↔
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup :=
  Iff.rfl

/-- An extension is totally ramified exactly when the degree image of its
base is contained in the degree image of its field. -/
theorem isTotallyRamified_iff_image_le (E : AbstractExtension G) (D : DegreeData G) :
    E.IsTotallyRamified D ↔
      E.base.toSubgroup.map D.degree.toMonoidHom ≤
        E.field.toSubgroup.map D.degree.toMonoidHom :=
  Iff.rfl

end AbstractExtension

/-- A (not necessarily finite) Galois extension above `K`.  Normality and
the inclusion of the upper field are carried by the object, while no
finiteness assumption is introduced. -/
structure GaloisSubextension (K : ClosedSubgroup G) where
  /-- The closed subgroup representing the top field. -/
  field : ClosedSubgroup G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.toSubgroup ≤ K.toSubgroup
  /-- The relative subgroup is normal in the base-field subgroup. -/
  normal : (extensionSubgroup K field below).Normal

namespace GaloisSubextension

variable {K : ClosedSubgroup G}

/-- Forget normality while retaining the underlying abstract extension. -/
def toAbstractExtension (L : GaloisSubextension K) :
    DegreeData.AbstractExtension G where
  field := L.field
  base := K
  below := L.below

/-- The actual quotient represented by a Galois subextension.  This is a
named object boundary rather than a transparent abbreviation. -/
def extensionQuotient (L : GaloisSubextension K) : Type u :=
  K.toSubgroup ⧸ extensionSubgroup K L.field L.below

/-- Structural unramifiedness of a Galois subextension. -/
def IsUnramified (L : GaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toAbstractExtension.IsUnramified D

/-- Structural total ramification of a Galois subextension. -/
def IsTotallyRamified (L : GaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toAbstractExtension.IsTotallyRamified D

/-- A Galois subextension has a normal subgroup inside its base subgroup. -/
instance extensionSubgroup_normalInstance (L : GaloisSubextension K) :
    (extensionSubgroup K L.field L.below).Normal :=
  L.normal

/-- The group structure transported across the named quotient boundary. -/
instance extensionQuotient_groupInstance (L : GaloisSubextension K) :
    Group L.extensionQuotient := by
  change Group
    (K.toSubgroup ⧸ extensionSubgroup K L.field L.below)
  infer_instance

/-- Comparison with the quotient presentation used by the underlying group
library. -/
def extensionQuotientMulEquiv (L : GaloisSubextension K) :
    L.extensionQuotient ≃*
      (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  MulEquiv.refl _

/-- The canonical quotient projection for a Galois subextension. -/
def extensionQuotientMk (L : GaloisSubextension K) :
    K.toSubgroup →* L.extensionQuotient :=
  QuotientGroup.mk' (extensionSubgroup K L.field L.below)

/-- The named quotient projection agrees with `QuotientGroup.mk` under the
comparison equivalence. -/
@[simp]
theorem extensionQuotientMk_apply (L : GaloisSubextension K)
    (k : K.toSubgroup) :
    L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k :
        K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  rfl

/-- Unramifiedness is the canonical inertia-containment condition. -/
theorem isUnramified_iff_inertia_le (L : GaloisSubextension K)
    (D : DegreeData G) :
    L.IsUnramified D ↔
      K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup :=
  L.toAbstractExtension.isUnramified_iff_inertia_le D

/-- Total ramification is the canonical equality of degree images. -/
theorem isTotallyRamified_iff_image_le (L : GaloisSubextension K)
    (D : DegreeData G) :
    L.IsTotallyRamified D ↔
      K.toSubgroup.map D.degree.toMonoidHom ≤
        L.field.toSubgroup.map D.degree.toMonoidHom :=
  L.toAbstractExtension.isTotallyRamified_iff_image_le D

end GaloisSubextension

/-- A finite abstract extension.  Finiteness is carried by the extension
object, so its public numerical invariants can be positive naturals rather than
using the raw subgroup-index convention in which an infinite index is encoded
as `0`. -/
structure FiniteAbstractExtension (G : Type*) [Group G] [TopologicalSpace G]
    extends AbstractExtension G where
  /-- The relative quotient of the base subgroup by the extension subgroup is finite. -/
  finiteQuotient :
    Finite
      (toAbstractExtension.base.toSubgroup ⧸
        extensionSubgroup toAbstractExtension.base toAbstractExtension.field
          toAbstractExtension.below)

namespace FiniteAbstractExtension

variable (E : FiniteAbstractExtension G)

/-- The subgroup of the base represented by a finite extension. -/
def subgroup : Subgroup E.base.toSubgroup :=
  extensionSubgroup E.base E.field E.below

/-- The finite extension's actual relative coset space. -/
def quotient : Type u :=
  E.base.toSubgroup ⧸ E.subgroup

/-- Bundle an inclusion once its actual relative coset type is known to be
finite.  This is the canonical boundary from subgroup data to the finite
extension API; numerical invariants are obtained only from the resulting
object. -/
def ofInclusion (field base : ClosedSubgroup G)
    (below : field.toSubgroup ≤ base.toSubgroup)
    [hfinite : Finite
      (base.toSubgroup ⧸ extensionSubgroup base field below)] :
    FiniteAbstractExtension G where
  field := field
  base := base
  below := below
  finiteQuotient := hfinite

/-- The field endpoint of an extension bundled from an inclusion is the supplied field. -/
@[simp] theorem ofInclusion_field (field base : ClosedSubgroup G)
    (below : field.toSubgroup ≤ base.toSubgroup)
    [Finite (base.toSubgroup ⧸ extensionSubgroup base field below)] :
    (ofInclusion field base below).field = field :=
  rfl

/-- The base endpoint of an extension bundled from an inclusion is the supplied base. -/
@[simp] theorem ofInclusion_base (field base : ClosedSubgroup G)
    (below : field.toSubgroup ≤ base.toSubgroup)
    [Finite (base.toSubgroup ⧸ extensionSubgroup base field below)] :
    (ofInclusion field base below).base = base :=
  rfl

/-- The unramified predicate for a finite extension is the predicate on its
underlying abstract extension. -/
def IsUnramified (D : DegreeData G) : Prop :=
  E.toAbstractExtension.IsUnramified D

/-- The totally ramified predicate for a finite extension is the predicate on
its underlying abstract extension. -/
def IsTotallyRamified (D : DegreeData G) : Prop :=
  E.toAbstractExtension.IsTotallyRamified D

/-- Finite-extension unramifiedness is exactly unramifiedness of the underlying
abstract extension. -/
@[simp] theorem isUnramified_iff (D : DegreeData G) :
    E.IsUnramified D ↔ E.toAbstractExtension.IsUnramified D :=
  Iff.rfl

/-- Finite-extension total ramification is inherited from the underlying abstract extension. -/
@[simp] theorem isTotallyRamified_iff (D : DegreeData G) :
    E.IsTotallyRamified D ↔ E.toAbstractExtension.IsTotallyRamified D :=
  Iff.rfl

/-- Finite unramified extensions satisfy the same inertia-containment
characterization as their underlying abstract extensions. -/
theorem isUnramified_iff_inertia_le (D : DegreeData G) :
    E.IsUnramified D ↔
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup :=
  E.toAbstractExtension.isUnramified_iff_inertia_le D

/-- Finite totally ramified extensions satisfy the same degree-image
characterization as their underlying abstract extensions. -/
theorem isTotallyRamified_iff_image_le (D : DegreeData G) :
    E.IsTotallyRamified D ↔
      E.base.toSubgroup.map D.degree.toMonoidHom ≤
        E.field.toSubgroup.map D.degree.toMonoidHom :=
  E.toAbstractExtension.isTotallyRamified_iff_image_le D

/-- The coset space carried by a finite abstract extension is finite. -/
instance quotientFinite :
    Finite E.quotient := by
  simpa [quotient, subgroup] using E.finiteQuotient

/-- The finite instance in the concrete quotient presentation used by norm
maps. -/
instance representedQuotientFinite :
    Finite
      (E.base.toSubgroup ⧸
        extensionSubgroup E.base E.field E.below) :=
  E.finiteQuotient

theorem degreeCardinal_lt_aleph0 :
    E.toAbstractExtension.degreeCardinal < Cardinal.aleph0 := by
  change Cardinal.mk
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) <
    Cardinal.aleph0
  exact Cardinal.lt_aleph0_of_finite _

theorem relativeDegreeCardinals_lt_aleph0 (D : DegreeData G) :
    Cardinal.lift.{u}
          (E.toAbstractExtension.relativeResidueDegreeCardinal D) <
        Cardinal.aleph0 ∧
      E.toAbstractExtension.relativeRamificationIndexCardinal D <
        Cardinal.aleph0 := by
  have hresidueUnlifted :
      E.toAbstractExtension.relativeResidueDegreeCardinal D ≠ 0 := by
    rw [AbstractExtension.relativeResidueDegreeCardinal,
      relativeIndexCardinal, intersectionIndexCardinal]
    exact Cardinal.mk_ne_zero _
  have hresidue :
      Cardinal.lift.{u}
          (E.toAbstractExtension.relativeResidueDegreeCardinal D) ≠ 0 := by
    intro hzero
    exact hresidueUnlifted (Cardinal.lift_eq_zero.mp hzero)
  have hramification :
      E.toAbstractExtension.relativeRamificationIndexCardinal D ≠ 0 := by
    rw [AbstractExtension.relativeRamificationIndexCardinal,
      relativeIndexCardinal, intersectionIndexCardinal]
    exact Cardinal.mk_ne_zero _
  apply (Cardinal.mul_lt_aleph0_iff_of_ne_zero
    hresidue hramification).mp
  rw [← E.toAbstractExtension.degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal D]
  exact E.degreeCardinal_lt_aleph0

theorem relativeResidueDegreeCardinal_lt_aleph0
    (D : DegreeData G) :
    E.toAbstractExtension.relativeResidueDegreeCardinal D <
      Cardinal.aleph0 :=
  Cardinal.lift_lt_aleph0.mp (E.relativeDegreeCardinals_lt_aleph0 D).1

theorem relativeRamificationIndexCardinal_lt_aleph0
    (D : DegreeData G) :
    E.toAbstractExtension.relativeRamificationIndexCardinal D <
      Cardinal.aleph0 :=
  (E.relativeDegreeCardinals_lt_aleph0 D).2

/-- The residue coset type of a finite extension is finite.  This is derived
from the cardinal fundamental identity, rather than from a natural-valued
index whose infinite case would be represented by zero. -/
noncomputable instance residueQuotientFinite (D : DegreeData G) :
    Finite
      (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
        (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
          (E.base.toSubgroup.map D.degree.toMonoidHom)) := by
  apply Cardinal.lt_aleph0_iff_finite.mp
  simpa [AbstractExtension.relativeResidueDegreeCardinal,
    relativeIndexCardinal, intersectionIndexCardinal] using
      E.relativeResidueDegreeCardinal_lt_aleph0 D

/-- The inertia coset type of a finite extension is finite.  As for the
residue quotient, this is a consequence of the cardinal fundamental identity. -/
noncomputable instance ramificationQuotientFinite (D : DegreeData G) :
    Finite
      (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
        (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
          (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)) := by
  apply Cardinal.lt_aleph0_iff_finite.mp
  simpa [AbstractExtension.relativeRamificationIndexCardinal,
    relativeIndexCardinal, intersectionIndexCardinal] using
      E.relativeRamificationIndexCardinal_lt_aleph0 D

/-- The positive degree of a finite abstract extension. -/
def degree : ℕ+ :=
  by
    letI : Nonempty E.quotient :=
      ⟨QuotientGroup.mk 1⟩
    exact ⟨Nat.card E.quotient, Nat.card_pos⟩

/-- The positive relative residue degree of a finite abstract extension. -/
def residueDegree (D : DegreeData G) : ℕ+ :=
  ⟨Nat.card
      (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
        (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
          (E.base.toSubgroup.map D.degree.toMonoidHom)),
    Nat.card_pos⟩

/-- The positive relative ramification index of a finite abstract extension. -/
def ramificationIndex (D : DegreeData G) : ℕ+ :=
  ⟨Nat.card
      (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
        (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
          (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)),
    Nat.card_pos⟩

/-- The natural value of the positive extension degree is the cardinality of its quotient. -/
@[simp] theorem degree_coe :
    (E.degree : ℕ) = Nat.card E.quotient :=
  rfl

/-- The positive residue degree coerces to the cardinality of the mapped-subgroup quotient. -/
@[simp] theorem residueDegree_coe (D : DegreeData G) :
    (E.residueDegree D : ℕ) =
      Nat.card
        (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
          (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
            (E.base.toSubgroup.map D.degree.toMonoidHom)) :=
  rfl

/-- The positive ramification index coerces to the cardinality of the inertia quotient. -/
@[simp] theorem ramificationIndex_coe (D : DegreeData G) :
    (E.ramificationIndex D : ℕ) =
      Nat.card
        (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
          (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
            (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)) :=
  rfl

/-- The underlying subgroup index of a finite extension is the natural
coercion of its positive degree.  This theorem is a finite-only bridge, not a
general natural-valued degree definition. -/
@[simp] theorem relIndex_eq_degree :
    E.field.toSubgroup.relIndex E.base.toSubgroup = (E.degree : ℕ) := by
  rw [Subgroup.relIndex, Subgroup.index, E.degree_coe]
  rfl

/-- The index of the represented extension subgroup is the finite extension
degree. -/
@[simp] theorem extensionSubgroup_index_eq_degree :
    (extensionSubgroup E.base E.field E.below).index = (E.degree : ℕ) := by
  rw [Subgroup.index, E.degree_coe]
  rfl

/-- The relative index of the mapped field subgroups is the positive residue
degree of a finite extension. -/
@[simp] theorem mapped_relIndex_eq_residueDegree (D : DegreeData G) :
    (E.field.toSubgroup.map D.degree.toMonoidHom).relIndex
        (E.base.toSubgroup.map D.degree.toMonoidHom) =
      (E.residueDegree D : ℕ) := by
  rw [Subgroup.relIndex, Subgroup.index, E.residueDegree_coe]

/-- The relative index inside the degree kernel is the positive ramification
index of a finite extension. -/
@[simp] theorem inertia_relIndex_eq_ramificationIndex (D : DegreeData G) :
    (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).relIndex
        (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) =
      (E.ramificationIndex D : ℕ) := by
  rw [Subgroup.relIndex, Subgroup.index, E.ramificationIndex_coe]

/-- The finite fundamental identity, stated only in terms of the positive
invariants carried by a finite extension object. -/
theorem degree_eq_residueDegree_mul_ramificationIndex (D : DegreeData G) :
    (E.degree : ℕ) =
      (E.residueDegree D : ℕ) * (E.ramificationIndex D : ℕ) := by
  rw [← E.relIndex_eq_degree, ← E.mapped_relIndex_eq_residueDegree D,
    ← E.inertia_relIndex_eq_ramificationIndex D]
  exact relIndex_eq_map_relIndex_mul_inf_ker_relIndex
    D.degree.toMonoidHom E.below

/-- An unramified finite extension has ramification index one. -/
theorem ramificationIndex_eq_one_of_isUnramified (D : DegreeData G)
    (hE : E.IsUnramified D) :
    (E.ramificationIndex D : ℕ) = 1 := by
  rw [← E.inertia_relIndex_eq_ramificationIndex D,
    Subgroup.relIndex_eq_one]
  intro x hx
  exact ⟨hE hx, hx.2⟩

/-- A totally ramified finite extension has residue degree one. -/
theorem residueDegree_eq_one_of_isTotallyRamified (D : DegreeData G)
    (hE : E.IsTotallyRamified D) :
    (E.residueDegree D : ℕ) = 1 := by
  rw [← E.mapped_relIndex_eq_residueDegree D,
    Subgroup.relIndex_eq_one]
  exact hE

/-- A finite extension has residue degree one exactly when it is totally
ramified.  This keeps callers on the structural predicate API instead of
unfolding the image-index implementation. -/
theorem isTotallyRamified_iff_residueDegree_eq_one (D : DegreeData G) :
    E.IsTotallyRamified D ↔ (E.residueDegree D : ℕ) = 1 := by
  constructor
  · exact E.residueDegree_eq_one_of_isTotallyRamified D
  · intro h
    rw [isTotallyRamified_iff_image_le]
    rw [← E.mapped_relIndex_eq_residueDegree D,
      Subgroup.relIndex_eq_one] at h
    exact h

/-- Converse form convenient for constructing the structural predicate from
the positive finite invariant. -/
theorem isTotallyRamified_of_residueDegree_eq_one (D : DegreeData G)
    (h : (E.residueDegree D : ℕ) = 1) : E.IsTotallyRamified D :=
  (E.isTotallyRamified_iff_residueDegree_eq_one D).2 h

/-- In an unramified finite extension, residue degree equals extension
degree. -/
theorem residueDegree_eq_degree_of_isUnramified (D : DegreeData G)
    (hE : E.IsUnramified D) :
    (E.residueDegree D : ℕ) = (E.degree : ℕ) := by
  rw [E.degree_eq_residueDegree_mul_ramificationIndex D,
    E.ramificationIndex_eq_one_of_isUnramified D hE, mul_one]

/-- For a finite extension, its cardinal-valued degree is the cardinal cast
of its positive natural degree. -/
@[simp] theorem degreeCardinal_eq_coe :
    E.toAbstractExtension.degreeCardinal =
      ((E.degree : ℕ) : Cardinal) := by
  change Cardinal.mk
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) =
    (Nat.card
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) : Cardinal)
  simpa [quotient, subgroup] using
    ((Nat.cast_card :
      (Nat.card E.quotient : Cardinal) = Cardinal.mk E.quotient).symm)

/-- For a finite extension, the cardinal-valued relative residue degree is
the cardinal cast of the positive natural residue degree. -/
@[simp] theorem relativeResidueDegreeCardinal_eq_coe (D : DegreeData G) :
    E.toAbstractExtension.relativeResidueDegreeCardinal D =
      ((E.residueDegree D : ℕ) : Cardinal) := by
  change Cardinal.mk
    (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
      (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
        (E.base.toSubgroup.map D.degree.toMonoidHom)) =
      (Nat.card
        (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
          (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
            (E.base.toSubgroup.map D.degree.toMonoidHom)) : Cardinal)
  exact (Nat.cast_card).symm

/-- For a finite extension, the cardinal-valued relative ramification index
is the cardinal cast of the positive natural ramification index. -/
@[simp] theorem relativeRamificationIndexCardinal_eq_coe (D : DegreeData G) :
    E.toAbstractExtension.relativeRamificationIndexCardinal D =
      ((E.ramificationIndex D : ℕ) : Cardinal) := by
  change Cardinal.mk
    (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
      (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
        (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)) =
      (Nat.card
        (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
          (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
            (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)) : Cardinal)
  exact (Nat.cast_card).symm

end FiniteAbstractExtension

/-- A finite composable tower of abstract extensions.  The two adjacent
finite quotient proofs belong to the tower object, so downstream norm and
degree laws do not thread subgroup containments and finiteness instances as
independent arguments. -/
structure FiniteTower (G : Type*) [Group G] [TopologicalSpace G]
    extends AbstractExtension.Tower G where
  /-- The quotient for the top-to-middle extension is finite. -/
  finiteTopQuotient : Finite toTower.topExtension.quotient
  /-- The quotient for the middle-to-base extension is finite. -/
  finiteBaseQuotient : Finite toTower.baseExtension.quotient

namespace FiniteTower

variable (T : FiniteTower G)

/-- The upper relative quotient in a finite tower is finite. -/
instance topQuotientFinite :
    Finite (T.middle.toSubgroup ⧸
      extensionSubgroup T.middle T.top T.top_le_middle) :=
  T.finiteTopQuotient

/-- The lower relative quotient in a finite tower is finite. -/
instance baseQuotientFinite :
    Finite (T.base.toSubgroup ⧸
      extensionSubgroup T.base T.middle T.middle_le_base) :=
  T.finiteBaseQuotient

end FiniteTower

namespace FiniteResidueAbstractField

variable {D : DegreeData G}

/-- If the relative residue quotient over a field with finite absolute
residue quotient is finite, then the upper field also has finite absolute
residue quotient.  This is the minimal honest boundary constructor: it uses
the actual quotient types and the cardinal tower identity. -/
noncomputable def ofRelativeInclusion (D : DegreeData G)
    (field : ClosedSubgroup G) (base : FiniteResidueAbstractField D)
    (below : field.toSubgroup ≤ base.field.toSubgroup)
    [finiteRelativeResidueQuotient : Finite
      (↥(base.field.toSubgroup.map D.degree.toMonoidHom) ⧸
        (field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
          (base.field.toSubgroup.map D.degree.toMonoidHom))] :
    FiniteResidueAbstractField D where
  field := field
  finiteResidueQuotient := by
    apply Cardinal.lt_aleph0_iff_finite.mp
    rw [← D.residueDegreeCardinal_eq_mk_residueQuotient]
    let E : AbstractExtension G := {
      field := field
      base := base.field
      below := below
    }
    rw [← E.relativeResidueDegreeCardinal_mul_residueDegreeCardinal D]
    apply Cardinal.mul_lt_aleph0_iff.mpr
    exact Or.inr (Or.inr ⟨by
      change Cardinal.mk
          (↥(base.field.toSubgroup.map D.degree.toMonoidHom) ⧸
            (field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
              (base.field.toSubgroup.map D.degree.toMonoidHom)) <
        Cardinal.aleph0
      exact Cardinal.lt_aleph0_of_finite _, by
      rw [D.residueDegreeCardinal_eq_mk_residueQuotient]
      exact Cardinal.lt_aleph0_of_finite _⟩)

end FiniteResidueAbstractField

/-- A finite extension whose base and field both carry their honest finite
absolute residue quotients.  The proof-dependent relative quotient is stored
once in the object and exposed through `toFiniteAbstractExtension`. -/
structure FiniteResidueAbstractExtension (D : DegreeData G) where
  /-- The top endpoint with its finite residue quotient. -/
  field : FiniteResidueAbstractField D
  /-- The base endpoint with its finite residue quotient. -/
  base : FiniteResidueAbstractField D
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.field.toSubgroup ≤ base.field.toSubgroup
  /-- The relative extension quotient is finite. -/
  finiteQuotient :
    Finite
      (base.field.toSubgroup ⧸
        extensionSubgroup base.field field.field below)

namespace FiniteResidueAbstractExtension

variable {D : DegreeData G}

/-- Enrich a finite extension of a field with finite absolute residue quotient
with the corresponding honest residue data on its upper endpoint.  Finiteness
of the upper absolute residue quotient is deduced from the cardinal-valued
tower identity, which is the source of truth for arbitrary-index data. -/
noncomputable def ofInclusion (D : DegreeData G)
    (field : ClosedSubgroup G) (base : FiniteResidueAbstractField D)
    (below : field.toSubgroup ≤ base.field.toSubgroup)
    [finiteQuotient : Finite
      (base.field.toSubgroup ⧸
        extensionSubgroup base.field field below)] :
    FiniteResidueAbstractExtension D where
  field := {
    field := field
    finiteResidueQuotient := by
      apply Cardinal.lt_aleph0_iff_finite.mp
      rw [← D.residueDegreeCardinal_eq_mk_residueQuotient]
      let E : FiniteAbstractExtension G := {
        field := field
        base := base.field
        below := below
        finiteQuotient := finiteQuotient
      }
      rw [← E.toAbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal D]
      apply Cardinal.mul_lt_aleph0_iff.mpr
      exact Or.inr (Or.inr ⟨E.relativeResidueDegreeCardinal_lt_aleph0 D, by
        rw [D.residueDegreeCardinal_eq_mk_residueQuotient]
        exact Cardinal.lt_aleph0_of_finite (D.residueQuotient base.field)⟩) }
  base := base
  below := below
  finiteQuotient := finiteQuotient

/-- Forget only the endpoint residue-finiteness data. -/
def toFiniteAbstractExtension (E : FiniteResidueAbstractExtension D) :
    FiniteAbstractExtension G where
  field := E.field.field
  base := E.base.field
  below := E.below
  finiteQuotient := E.finiteQuotient

/-- A finite-residue extension supplies finiteness of its represented relative quotient. -/
instance instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField (E : FiniteResidueAbstractExtension D) :
    Finite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below) :=
  E.finiteQuotient

/-- The positive relative degree. -/
noncomputable def degree (E : FiniteResidueAbstractExtension D) : ℕ+ :=
  E.toFiniteAbstractExtension.degree

/-- The positive relative residue degree. -/
noncomputable def residueDegree (E : FiniteResidueAbstractExtension D) : ℕ+ :=
  E.toFiniteAbstractExtension.residueDegree D

/-- The positive relative ramification index. -/
noncomputable def ramificationIndex
    (E : FiniteResidueAbstractExtension D) : ℕ+ :=
  E.toFiniteAbstractExtension.ramificationIndex D

/-- The residue-enriched extension degree agrees with the underlying finite-extension degree. -/
@[simp] theorem degree_coe (E : FiniteResidueAbstractExtension D) :
    (E.degree : ℕ) = (E.toFiniteAbstractExtension.degree : ℕ) :=
  rfl

/-- The residue-enriched residue degree agrees with the underlying finite-extension invariant. -/
@[simp] theorem residueDegree_coe (E : FiniteResidueAbstractExtension D) :
    (E.residueDegree : ℕ) =
      (E.toFiniteAbstractExtension.residueDegree D : ℕ) :=
  rfl

/-- The residue-enriched ramification index agrees with the underlying
finite-extension invariant. -/
@[simp] theorem ramificationIndex_coe
    (E : FiniteResidueAbstractExtension D) :
    (E.ramificationIndex : ℕ) =
      (E.toFiniteAbstractExtension.ramificationIndex D : ℕ) :=
  rfl

end FiniteResidueAbstractExtension

end DegreeData

/-! ## Fields finite over the distinguished base -/

/-- An abstract field finite over the distinguished base field. -/
structure FiniteAbstractField (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The closed subgroup representing the abstract field. -/
  field : ClosedSubgroup G
  /-- The field has finite degree over the distinguished base. -/
  finite : Finite ((baseField G).toSubgroup ⧸
    extensionSubgroup (baseField G) field (le_baseField field))

namespace FiniteAbstractField

/-- A finite abstract field is determined by its underlying closed subgroup;
the finiteness component is proof-irrelevant. -/
theorem eq_of_field_eq (K L : FiniteAbstractField G)
    (h : K.field = L.field) : K = L := by
  cases K with
  | mk K hK =>
    cases L with
    | mk L hL =>
      cases h
      rfl

/-- The distinguished base field, bundled with its trivial finite quotient. -/
noncomputable def base (G : Type u) [Group G] [TopologicalSpace G] :
    FiniteAbstractField G where
  field := baseField G
  finite := by
    let : (extensionSubgroup (baseField G) (baseField G)
        (le_baseField (baseField G))).Normal := by
      rw [show extensionSubgroup (baseField G) (baseField G)
          (le_baseField (baseField G)) = ⊤ by
        ext x
        exact Iff.rfl]
      infer_instance
    let : Subsingleton
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) (baseField G)
            (le_baseField (baseField G))) := by
      constructor
      intro x y
      refine Quotient.inductionOn₂' x y ?_
      intro a b
      apply QuotientGroup.eq_iff_div_mem.mpr
      exact Subgroup.mem_top _
    infer_instance

/-- Regard a finite abstract field as its finite extension of the
distinguished base field. -/
def toFiniteAbstractExtension (K : FiniteAbstractField G) :
    DegreeData.FiniteAbstractExtension G where
  field := K.field
  base := baseField G
  below := le_baseField K.field
  finiteQuotient := K.finite

/-- A finite abstract field supplies finiteness of its quotient over the distinguished base. -/
instance instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField (K : FiniteAbstractField G) :
    Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K.field (le_baseField K.field)) :=
  K.finite

/-- A finite field over the distinguished base has a finite absolute residue
quotient.  This is derived from the finite relative quotient and the
surjectivity of the ambient degree map. -/
@[implicit_reducible]
noncomputable def toFiniteResidueAbstractField
    (K : FiniteAbstractField G) (D : DegreeData G) :
    DegreeData.FiniteResidueAbstractField D where
  field := K.field
  finiteResidueQuotient := by
    apply Cardinal.lt_aleph0_iff_finite.mp
    change
      intersectionIndexCardinal (D.fieldImage K.field)
        (⊤ : Subgroup ZHatMul) < Cardinal.aleph0
    rw [D.fieldImage_eq_map]
    have htop :
        (baseField G).toSubgroup.map D.degree.toMonoidHom = ⊤ := by
      rw [baseField_toSubgroup]
      exact Subgroup.map_top_of_surjective _ D.degree_surjective
    rw [← htop]
    simpa only [FiniteAbstractField.toFiniteAbstractExtension,
      DegreeData.AbstractExtension.relativeResidueDegreeCardinal, relativeIndexCardinal] using
      K.toFiniteAbstractExtension.relativeResidueDegreeCardinal_lt_aleph0 D

/-- The positive absolute residue degree of a field finite over the
distinguished base. -/
noncomputable def residueDegree (K : FiniteAbstractField G)
    (D : DegreeData G) : ℕ+ :=
  (K.toFiniteResidueAbstractField D).residueDegree

/-- Positive-natural specialization of the base-field residue degree. -/
@[simp] theorem base_residueDegree (D : DegreeData G) :
    (FiniteAbstractField.base G).residueDegree D = 1 := by
  apply Subtype.ext
  change (((FiniteAbstractField.base G).toFiniteResidueAbstractField D).residueDegree : ℕ) = 1
  apply Nat.cast_injective (R := Cardinal)
  rw [← DegreeData.FiniteResidueAbstractField.residueDegreeCardinal_eq_coe]
  exact D.residueDegreeCardinal_baseField

/-- The field residue degree is inherited from its finite-residue-field enrichment. -/
@[simp] theorem residueDegree_coe (K : FiniteAbstractField G)
    (D : DegreeData G) :
    (K.residueDegree D : ℕ) =
      ((K.toFiniteResidueAbstractField D).residueDegree : ℕ) :=
  rfl

end FiniteAbstractField

/-- A finite extension between two fields that are themselves finite over the
distinguished base.  Both endpoint finiteness proofs and the relative quotient
belong to the object. -/
structure FiniteAbstractFieldExtension (G : Type u)
    [Group G] [TopologicalSpace G] where
  /-- The top endpoint, finite over the distinguished base. -/
  field : FiniteAbstractField G
  /-- The base endpoint, finite over the distinguished base. -/
  base : FiniteAbstractField G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.field.toSubgroup ≤ base.field.toSubgroup
  /-- The relative extension quotient is finite. -/
  finiteQuotient :
    Finite
      (base.field.toSubgroup ⧸
        extensionSubgroup base.field field.field below)

namespace FiniteAbstractFieldExtension

/-- Canonically bundle a finite relative extension of a field already finite
over the distinguished base.  Finiteness of the upper field follows from the
actual quotient tower. -/
@[implicit_reducible]
noncomputable def ofInclusion (field : ClosedSubgroup G)
    (base : FiniteAbstractField G)
    (below : field.toSubgroup ≤ base.field.toSubgroup)
    [finiteQuotient : Finite
      (base.field.toSubgroup ⧸
        extensionSubgroup base.field field below)] :
    FiniteAbstractFieldExtension G where
  field := {
    field := field
    finite := by
      apply Cardinal.lt_aleph0_iff_finite.mp
      let T : DegreeData.AbstractExtension.Tower G := {
        top := field
        middle := base.field
        base := baseField G
        top_le_middle := below
        middle_le_base := le_baseField base.field }
      change T.totalExtension.degreeCardinal < Cardinal.aleph0
      rw [← T.degreeCardinal_mul]
      apply Cardinal.mul_lt_aleph0
      · change Cardinal.mk
          (base.field.toSubgroup ⧸
            extensionSubgroup base.field field below) < Cardinal.aleph0
        exact Cardinal.lt_aleph0_of_finite _
      · change Cardinal.mk
          ((baseField G).toSubgroup ⧸
            extensionSubgroup (baseField G) base.field
              (le_baseField base.field)) < Cardinal.aleph0
        exact Cardinal.lt_aleph0_of_finite _ }
  base := base
  below := below
  finiteQuotient := finiteQuotient

/-- Forget endpoint finiteness over the distinguished base. -/
@[implicit_reducible]
def toFiniteAbstractExtension (E : FiniteAbstractFieldExtension G) :
    DegreeData.FiniteAbstractExtension G where
  field := E.field.field
  base := E.base.field
  below := E.below
  finiteQuotient := E.finiteQuotient

/-- Structural unramifiedness of the represented relative extension. -/
@[implicit_reducible]
def IsUnramified (E : FiniteAbstractFieldExtension G) (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsUnramified D

/-- Structural total ramification of the represented relative extension. -/
def IsTotallyRamified (E : FiniteAbstractFieldExtension G)
    (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsTotallyRamified D

/-- The positive relative degree. -/
noncomputable def degree (E : FiniteAbstractFieldExtension G) : ℕ+ :=
  E.toFiniteAbstractExtension.degree

/-- The positive relative residue degree. -/
noncomputable def residueDegree (E : FiniteAbstractFieldExtension G)
    (D : DegreeData G) : ℕ+ :=
  E.toFiniteAbstractExtension.residueDegree D

/-- In an unramified finite field extension, the positive relative residue
degree is the positive extension degree. -/
theorem residueDegree_eq_degree_of_isUnramified
    (E : FiniteAbstractFieldExtension G) (D : DegreeData G)
    (hE : E.IsUnramified D) :
    (E.residueDegree D : ℕ) = (E.degree : ℕ) :=
  E.toFiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified D hE

/-- A finite abstract field extension supplies finiteness of its relative quotient. -/
instance instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField (E : FiniteAbstractFieldExtension G) :
    Finite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below) :=
  E.finiteQuotient

/-- Canonically enrich both endpoints with their finite residue quotients. -/
noncomputable def toFiniteResidueAbstractExtension
    (E : FiniteAbstractFieldExtension G) (D : DegreeData G) :
    DegreeData.FiniteResidueAbstractExtension D where
  field := E.field.toFiniteResidueAbstractField D
  base := E.base.toFiniteResidueAbstractField D
  below := E.below
  finiteQuotient := E.finiteQuotient

end FiniteAbstractFieldExtension

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_Frobenius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ClassFormation

/-!
# normalized degree and Frobenius theory: normalized degree maps and Frobenius

For a field of finite residue degree, this file constructs the map
`d_K = (1 / f_K) d`; division is performed only after proving that
`d(G_K) = f_K ℤ̂`.  The Frobenius is then the unique class mapping to `1`.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The image `d(G_K)`, written additively inside `ℤ̂`. -/
def fieldImageAdd (D : DegreeData G) (K : ClosedSubgroup G) : AddSubgroup ZHat :=
  Subgroup.toAddSubgroup' (D.fieldImage K)

/-- The additive degree image has index equal to the field's positive residue degree. -/
@[simp]
theorem fieldImageAdd_index (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    (D.fieldImageAdd K.field).index = (K.residueDegree : ℕ) := by
  change (D.fieldImage K.field).index = (K.residueDegree : ℕ)
  rw [← Subgroup.relIndex_top_right]
  change Nat.card (D.residueQuotient K.field) = (K.residueDegree : ℕ)
  exact K.residueDegree_coe.symm

/-- Finite residue degree identifies `d(G_K)` with `f_K ℤ̂`. -/
theorem fieldImageAdd_eq_mulNat_range (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    D.fieldImageAdd K.field =
      (zHatMulNat (K.residueDegree : ℕ)).toAddMonoidHom.range := by
  apply zHatAddSubgroup_eq_mulNat_range_of_index_eq
  · exact K.residueDegree.property
  · exact D.fieldImageAdd_index K

/-- The raw value `d(k)` regarded as an element of the subgroup `f_K ℤ̂`. -/
def restrictedDegreeInMulNatRange (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    (zHatMulNat (K.residueDegree : ℕ)).toAddMonoidHom.range := by
  refine ⟨(D.degree k.1).toAdd, ?_⟩
  rw [← D.fieldImageAdd_eq_mulNat_range K]
  change D.degree k.1 ∈ D.fieldImage K.field
  exact ⟨k, rfl⟩

/-- The restricted degree in the natural-multiple range has the original additive value. -/
@[simp]
theorem restrictedDegreeInMulNatRange_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.toSubgroup) :
    (D.restrictedDegreeInMulNatRange K k).1 = (D.degree k.1).toAdd :=
  rfl

/-- The normalized degree map `d_K = (1 / f_K)d`. -/
def normalizedDegree (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    K.field.toSubgroup →ₜ* ZHatMul where
  toFun k := Multiplicative.ofAdd
    (zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
      (D.restrictedDegreeInMulNatRange K k))
  map_one' := by
    apply Multiplicative.ext
    change zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
      (D.restrictedDegreeInMulNatRange K 1) = 0
    rw [show D.restrictedDegreeInMulNatRange K 1 = 0 by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (map_one D.degree)]
    exact map_zero (zHatDivide (K.residueDegree : ℕ) K.residueDegree.property)
  map_mul' x y := by
    apply Multiplicative.ext
    change zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
        (D.restrictedDegreeInMulNatRange K (x * y)) =
      zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
          (D.restrictedDegreeInMulNatRange K x) +
        zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
          (D.restrictedDegreeInMulNatRange K y)
    rw [show D.restrictedDegreeInMulNatRange K (x * y) =
        D.restrictedDegreeInMulNatRange K x +
          D.restrictedDegreeInMulNatRange K y by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        (map_mul D.degree x.1 y.1)]
    exact map_add (zHatDivide (K.residueDegree : ℕ) K.residueDegree.property) _ _
  continuous_toFun := by
    apply (map_continuous
      (zHatDivide (K.residueDegree : ℕ) K.residueDegree.property)).comp
    exact Continuous.subtype_mk
      (D.restrictedDegree K.field).continuous_toFun
      (fun k => (D.restrictedDegreeInMulNatRange K k).2)

/-- The additive coordinate of normalized degree is obtained by dividing by the residue degree. -/
@[simp]
theorem normalizedDegree_apply_toAdd (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    (D.normalizedDegree K k).toAdd =
      zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
        (D.restrictedDegreeInMulNatRange K k) :=
  rfl

/-- The defining identity `f_K d_K = d`. -/
theorem residueDegree_nsmul_normalizedDegree (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd =
      (D.degree k.1).toAdd := by
  exact zHatMulNat_zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
    (D.restrictedDegreeInMulNatRange K k)

/-- The normalized map is surjective, exactly as asserted before the normalized Frobenius definition. -/
theorem normalizedDegree_surjective (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    Function.Surjective (D.normalizedDegree K) := by
  intro z
  have hzImageAdd : (K.residueDegree : ℕ) • z.toAdd ∈
      D.fieldImageAdd K.field := by
    rw [D.fieldImageAdd_eq_mulNat_range K]
    exact ⟨z.toAdd, rfl⟩
  have hzImage : Multiplicative.ofAdd ((K.residueDegree : ℕ) • z.toAdd) ∈
      D.fieldImage K.field := hzImageAdd
  obtain ⟨k, hk⟩ := hzImage
  refine ⟨k, ?_⟩
  apply Multiplicative.ext
  apply zHatMulNat_injective K.residueDegree.property
  change (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd =
    (K.residueDegree : ℕ) • z.toAdd
  rw [D.residueDegree_nsmul_normalizedDegree K k]
  exact congrArg Multiplicative.toAdd hk

/-- The kernel of `d_K` is the inertia group `I_K`. -/
theorem normalizedDegree_ker (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    (D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field := by
  ext k
  constructor
  · intro hk
    change D.degree k.1 = 1
    apply Multiplicative.ext
    rw [← D.residueDegree_nsmul_normalizedDegree K k]
    change (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd = 0
    rw [show D.normalizedDegree K k = 1 from hk]
    simp
  · intro hk
    apply Multiplicative.ext
    apply zHatMulNat_injective K.residueDegree.property
    change (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd =
      (K.residueDegree : ℕ) • (1 : ZHatMul).toAdd
    rw [D.residueDegree_nsmul_normalizedDegree K k]
    rw [show D.degree k.1 = 1 from hk]
    simp

theorem fieldInertiaWithin_le_normalizedDegree_ker
    (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    D.fieldInertiaWithin K.field ≤ (D.normalizedDegree K).toMonoidHom.ker := by
  rw [D.normalizedDegree_ker K]

/-- The isomorphism `d_K : G(\widetilde K|K) ≃ ℤ̂`. -/
def maximalUnramifiedDegreeEquiv (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) ≃* ZHatMul := by
  let dquot : (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) →* ZHatMul :=
    QuotientGroup.lift (D.fieldInertiaWithin K.field)
      (D.normalizedDegree K).toMonoidHom
      (D.fieldInertiaWithin_le_normalizedDegree_ker K)
  apply MulEquiv.ofBijective dquot
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    apply QuotientGroup.eq.mpr
    change a⁻¹ * b ∈ D.fieldInertiaWithin K.field
    rw [← D.normalizedDegree_ker K]
    change D.normalizedDegree K (a⁻¹ * b) = 1
    rw [map_mul, map_inv]
    have hab' : D.normalizedDegree K a = D.normalizedDegree K b := by
      simpa [dquot] using hab
    rw [hab', inv_mul_cancel]
  · exact QuotientGroup.lift_surjective_of_surjective
      (D.fieldInertiaWithin K.field)
      (D.normalizedDegree K).toMonoidHom
      (D.normalizedDegree_surjective K)
      (D.fieldInertiaWithin_le_normalizedDegree_ker K)

/-- On quotient representatives, the maximal-unramified degree equivalence is normalized degree. -/
@[simp]
theorem maximalUnramifiedDegreeEquiv_mk (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    D.maximalUnramifiedDegreeEquiv K (QuotientGroup.mk k) =
      D.normalizedDegree K k := by
  rfl

/-- **the normalized Frobenius definition.** The Frobenius over `K`, characterized by
`d_K(φ_K)=1`. -/
def frobenius (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field :=
  (D.maximalUnramifiedDegreeEquiv K).symm
    (Multiplicative.ofAdd (1 : ZHat))

/-- The maximal-unramified degree equivalence sends Frobenius to the generator one. -/
@[simp]
theorem maximalUnramifiedDegreeEquiv_frobenius (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    D.maximalUnramifiedDegreeEquiv K (D.frobenius K) =
      Multiplicative.ofAdd (1 : ZHat) := by
  exact (D.maximalUnramifiedDegreeEquiv K).apply_symm_apply _

/-- For a finite extension, its positive residue degree times the absolute
residue degree of the base is the absolute residue degree of the field. -/
theorem FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree
    (D : DegreeData G) (E : FiniteResidueAbstractExtension D) :
    (E.residueDegree : ℕ) * (E.base.residueDegree : ℕ) =
      (E.field.residueDegree : ℕ) := by
  have h :=
    AbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal
      E.toFiniteAbstractExtension.toAbstractExtension D
  rw [E.toFiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe D] at h
  change ((E.residueDegree : ℕ) : Cardinal) *
      D.residueDegreeCardinal E.base.field =
    D.residueDegreeCardinal E.field.field at h
  rw [E.base.residueDegreeCardinal_eq_coe,
    E.field.residueDegreeCardinal_eq_coe] at h
  exact_mod_cast h

/-- **Frobenius residue-degree compatibility (commutative square).** On `G_L`, the normalized
degree maps satisfy `d_K = f_{L|K} d_L`. -/
theorem frobeniusRestrictionNaturality_normalizedDegree (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D)
    (l : E.field.field.toSubgroup) :
    (D.normalizedDegree E.base (Subgroup.inclusion E.below l)).toAdd =
      (E.residueDegree : ℕ) •
        (D.normalizedDegree E.field l).toAdd := by
  apply zHatMulNat_injective E.base.residueDegree.property
  change (E.base.residueDegree : ℕ) •
      (D.normalizedDegree E.base (Subgroup.inclusion E.below l)).toAdd =
    (E.base.residueDegree : ℕ) •
      ((E.residueDegree : ℕ) •
        (D.normalizedDegree E.field l).toAdd)
  rw [D.residueDegree_nsmul_normalizedDegree E.base]
  change (D.degree l.1).toAdd = _
  rw [smul_smul, Nat.mul_comm (E.base.residueDegree : ℕ),
    E.residueDegree_mul_absoluteResidueDegree D,
    D.residueDegree_nsmul_normalizedDegree E.field]

theorem fieldInertiaWithin_le_comap_inclusion
    (D : DegreeData G) {L K : ClosedSubgroup G}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    D.fieldInertiaWithin L ≤
      (D.fieldInertiaWithin K).comap (Subgroup.inclusion hLK) := by
  intro l hl
  exact hl

/-- Restriction `G(\widetilde L/L) → G(\widetilde K/K)` for `L | K`. -/
def maximalUnramifiedRestriction (D : DegreeData G) {L K : ClosedSubgroup G}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (L.toSubgroup ⧸ D.fieldInertiaWithin L) →*
      (K.toSubgroup ⧸ D.fieldInertiaWithin K) :=
  QuotientGroup.map (D.fieldInertiaWithin L) (D.fieldInertiaWithin K)
    (Subgroup.inclusion hLK) (D.fieldInertiaWithin_le_comap_inclusion hLK)

/-- Maximal-unramified restriction sends a quotient representative to its
restricted representative. -/
@[simp]
theorem maximalUnramifiedRestriction_mk (D : DegreeData G)
    {L K : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (l : L.toSubgroup) :
    D.maximalUnramifiedRestriction hLK (QuotientGroup.mk l) =
      QuotientGroup.mk (Subgroup.inclusion hLK l) := by
  rfl

end DegreeData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_FrobeniusLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# normalized degree and Frobenius theory: lifting finite Galois automorphisms

This file defines the Frobenius semigroup in `G(\widetilde L|K)` and proves
the lifting statement of the finite degree-quotient decomposition.  Positivity is explicit, so the
convention `0 ∉ ℕ` is not lost in Lean's natural numbers.
-/

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- In a finite cyclic quotient of `ℤ̂`, every class is represented by a
strictly positive natural multiple of `1`. -/
theorem exists_positive_nsmul_one_sub_mem_of_index_ne_zero
    (H : AddSubgroup ZHat) (hH : H.index ≠ 0) (z : ZHat) :
    ∃ n : ℕ, 0 < n ∧ z - n • (1 : ZHat) ∈ H := by
  let m := H.index
  have hm : 0 < m := Nat.pos_of_ne_zero hH
  let r : ZMod m := zHatReduction m hm z
  let n : ℕ := r.val + m
  refine ⟨n, Nat.add_pos_right r.val hm, ?_⟩
  rw [zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero H hH,
    zHatMulNat_range_eq_ker_reduction m hm]
  change zHatReduction m hm (z - n • (1 : ZHat)) = 0
  rw [map_sub, map_nsmul]
  have hredOne : zHatReduction m hm (1 : ZHat) = 1 :=
    rfl
  rw [hredOne]
  change zHatReduction m hm z - n • (1 : ZMod m) = 0
  rw [nsmul_eq_mul, mul_one]
  change r - (n : ZMod m) = 0
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hn : (n : ZMod m) = r := by
    change ((r.val + m : ℕ) : ZMod m) = r
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
  rw [hn, sub_self]

namespace DegreeData

/-- `I_L`, viewed inside `G_K`; this is `G_{\widetilde L}`. -/
def extensionInertiaWithin (D : DegreeData G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) : Subgroup K.toSubgroup :=
  extensionSubgroup K L hLK ⊓ D.fieldInertiaWithin K

/--
The relative inertia subgroup is normal whenever the full extension subgroup is normal.
-/
instance extensionInertiaWithin_normal (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (D.extensionInertiaWithin K L hLK).Normal := by
  rw [extensionInertiaWithin]
  infer_instance

theorem extensionInertiaWithin_le_normalizedDegree_ker
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) :
    D.extensionInertiaWithin K.field L hLK ≤
      (D.normalizedDegree K).toMonoidHom.ker := by
  intro x hx
  rw [D.normalizedDegree_ker K]
  exact hx.2

/-- The factorized map `d_K : G(\widetilde L|K) → ℤ̂`. -/
def extensionNormalizedDegree (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) →* ZHatMul :=
  QuotientGroup.lift (D.extensionInertiaWithin K.field L hLK)
    (D.normalizedDegree K).toMonoidHom
    (D.extensionInertiaWithin_le_normalizedDegree_ker K L hLK)

/--
Establishes the identity `D.extensionNormalizedDegree K L hLK (QuotientGroup.mk k) =
D.normalizedDegree K k`.
-/
@[simp]
theorem extensionNormalizedDegree_mk (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (k : K.field.toSubgroup) :
    D.extensionNormalizedDegree K L hLK (QuotientGroup.mk k) =
      D.normalizedDegree K k :=
  rfl

/-- Restriction from `G(\widetilde L|K)` to `G(L|K)`. -/
def extensionRestriction (D : DegreeData G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) →*
      (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
  QuotientGroup.map (D.extensionInertiaWithin K L hLK)
    (extensionSubgroup K L hLK) (MonoidHom.id K.toSubgroup) inf_le_left

/--
Establishes the identity `D.extensionRestriction K L hLK (QuotientGroup.mk k) = QuotientGroup.mk
k`.
-/
@[simp]
theorem extensionRestriction_mk (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) :
    D.extensionRestriction K L hLK (QuotientGroup.mk k) =
      QuotientGroup.mk k :=
  rfl

/-- The semigroup `Frob(\widetilde L|K)`: elements whose normalized
degree is a strictly positive natural. -/
def FrobeniusElements (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] : Type u :=
  {σ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK //
    ∃ n : ℕ, 0 < n ∧
      D.extensionNormalizedDegree K L hLK σ =
        (Multiplicative.ofAdd (1 : ZHat)) ^ n}

/-- The restriction map occurring in the finite degree-quotient decomposition. -/
def frobeniusRestriction (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    D.FrobeniusElements K L hLK →
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) :=
  fun σ => D.extensionRestriction K.field L hLK σ.1

def normalizedExtensionImageAdd (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) : AddSubgroup ZHat :=
  Subgroup.toAddSubgroup'
    ((extensionSubgroup K.field L hLK).map
      (D.normalizedDegree K).toMonoidHom)

theorem normalizedExtensionImageAdd_index_ne_zero
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    (D.normalizedExtensionImageAdd K L hLK).index ≠ 0 := by
  let E := extensionSubgroup K.field L hLK
  let dK := (D.normalizedDegree K).toMonoidHom
  let H := E.map dK
  have hE : E ≤ H.comap dK := Subgroup.le_comap_map dK E
  have hdvd : (H.comap dK).index ∣ E.index :=
    Subgroup.index_dvd_of_le hE
  have hcomap : (H.comap dK).index = H.index :=
    Subgroup.index_comap_of_surjective H (D.normalizedDegree_surjective K)
  have hHdvd : H.index ∣ E.index := hcomap ▸ hdvd
  have hE0 : E.index ≠ 0 := E.index_ne_zero_of_finite
  have hH0 : H.index ≠ 0 := by
    intro hzero
    rw [hzero] at hHdvd
    exact hE0 (zero_dvd_iff.mp hHdvd)
  exact hH0

/-- **the finite degree-quotient decomposition.** For a finite Galois extension `L | K`, restriction
maps the Frobenius semigroup onto `G(L|K)`. -/
theorem frobeniusRestriction_surjective (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    Function.Surjective (D.frobeniusRestriction K L hLK) := by
  intro σ
  refine Quotient.inductionOn' σ ?_
  intro s
  let H := D.normalizedExtensionImageAdd K L hLK
  have hH0 : H.index ≠ 0 :=
    D.normalizedExtensionImageAdd_index_ne_zero K L hLK
  obtain ⟨n, hn, hmem⟩ :=
    exists_positive_nsmul_one_sub_mem_of_index_ne_zero H hH0
      (D.normalizedDegree K s).toAdd
  have hneg : n • (1 : ZHat) - (D.normalizedDegree K s).toAdd ∈ H := by
    simpa [sub_eq_add_neg, add_comm] using H.neg_mem hmem
  change Multiplicative.ofAdd
      (n • (1 : ZHat) - (D.normalizedDegree K s).toAdd) ∈
    (extensionSubgroup K.field L hLK).map
      (D.normalizedDegree K).toMonoidHom at hneg
  obtain ⟨l, hlE, hdl⟩ := hneg
  let t : K.field.toSubgroup := s * l
  let q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK :=
    QuotientGroup.mk t
  have hdq : D.extensionNormalizedDegree K L hLK q =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
    apply Multiplicative.ext
    change (D.normalizedDegree K (s * l)).toAdd =
      n • (1 : ZHat)
    rw [map_mul]
    change (D.normalizedDegree K s).toAdd +
        (D.normalizedDegree K l).toAdd = n • (1 : ZHat)
    have hdl' := congrArg Multiplicative.toAdd hdl
    change (D.normalizedDegree K l).toAdd =
      n • (1 : ZHat) - (D.normalizedDegree K s).toAdd at hdl'
    rw [hdl']
    abel
  let qF : D.FrobeniusElements K L hLK := ⟨q, n, hn, hdq⟩
  refine ⟨qF, ?_⟩
  change QuotientGroup.mk (s * l) = QuotientGroup.mk s
  apply QuotientGroup.eq.mpr
  change (s * l)⁻¹ * s ∈ extensionSubgroup K.field L hLK
  simpa [mul_inv_rev, mul_assoc] using
    (extensionSubgroup K.field L hLK).inv_mem hlE

end DegreeData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.Topology_TotallyDisconnectedQuotients
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Totally disconnected quotient groups

This file proves that a closed normal quotient of a compact Hausdorff totally
disconnected topological group is totally disconnected.
-/

namespace QuotientGroup

/-- A closed normal quotient of a compact Hausdorff totally disconnected
topological group is totally disconnected. -/
theorem totallyDisconnectedSpace_of_isClosed
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hsep : Pairwise (fun a b : G ⧸ N =>
      ∃ U : Set (G ⧸ N), IsClopen U ∧ a ∈ U ∧ b ∈ Uᶜ) := by
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
    let g : G := x⁻¹ * y
    have hgN : g ∉ N := by
      intro hgN
      apply hab
      apply inv_mul_eq_one.mp
      change q g = 1
      exact (QuotientGroup.eq_one_iff g).2 hgN
    let W : Set G := {u | g * u⁻¹ ∉ N}
    have hWopen : IsOpen W := by
      change IsOpen ((fun u : G => g * u⁻¹) ⁻¹' ((N : Set G)ᶜ))
      exact hN.isOpen_compl.preimage (continuous_const.mul continuous_inv)
    have hWone : (1 : G) ∈ W := by
      simpa only [W, Set.mem_ofPred_eq, inv_one, mul_one] using hgN
    obtain ⟨V, hVW⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (G := G) hWopen hWone
    let K : Subgroup G := N ⊔ (V : Subgroup G)
    have hKopen : IsOpen (K : Set G) :=
      Subgroup.isOpen_of_openSubgroup K
        (show (V : Subgroup G) ≤ K from le_sup_right)
    have hNK : N ≤ K := le_sup_left
    have hgK : g ∉ K := by
      intro hgK
      rcases (Subgroup.mem_sup_of_normal_right
          (s := N) (t := (V : Subgroup G))).1 hgK with
        ⟨n, hnN, v, hvV, hnv⟩
      have hvW : v ∈ W := hVW hvV
      have hgn : g * v⁻¹ = n := by
        calc
          g * v⁻¹ = (n * v) * v⁻¹ := by rw [hnv]
          _ = n := by simp only [mul_assoc, mul_inv_cancel, mul_one]
      apply hvW
      simpa only [hgn] using hnN
    let Kbar : Subgroup (G ⧸ N) := K.map q
    have hKbarOpen : IsOpen (Kbar : Set (G ⧸ N)) := by
      change IsOpen (((↑) : G → G ⧸ N) '' (K : Set G))
      exact QuotientGroup.isOpenMap_coe (K : Set G) hKopen
    have hqgKbar : q g ∉ Kbar := by
      intro hqgKbar
      have hgComap : g ∈ Kbar.comap q := hqgKbar
      have hker : q.ker ≤ K := by
        simpa only [q, QuotientGroup.ker_mk'] using hNK
      have hcomap : Kbar.comap q = K := by
        simpa only [Kbar] using Subgroup.comap_map_eq_self hker
      rw [hcomap] at hgComap
      exact hgK hgComap
    let U : Set (G ⧸ N) := {z | (q x)⁻¹ * z ∈ Kbar}
    have hUclopen : IsClopen U := by
      have hcont : Continuous (fun z : G ⧸ N => (q x)⁻¹ * z) :=
        (continuous_const :
          Continuous (fun _ : G ⧸ N => (q x)⁻¹)).mul continuous_id
      exact
        ⟨(Subgroup.isClosed_of_isOpen Kbar hKbarOpen).preimage hcont,
          hKbarOpen.preimage hcont⟩
    refine ⟨U, hUclopen, ?_, ?_⟩
    · change (q x)⁻¹ * q x ∈ Kbar
      rw [inv_mul_cancel]
      exact Kbar.one_mem
    · change (q x)⁻¹ * q y ∉ Kbar
      change q (x⁻¹ * y) ∉ Kbar at hqgKbar
      simpa only [map_mul, map_inv] using hqgKbar
  let : TotallySeparatedSpace (G ⧸ N) :=
    totallySeparatedSpace_iff_exists_isClopen.2 hsep
  infer_instance

end QuotientGroup
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_FrobeniusFixedField
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The continuous lift of a homomorphism through a quotient, used locally
below. -/
def continuousQuotientLift
    {A : Type*} {B : Type*} [Group A] [TopologicalSpace A]
    [Group B] [TopologicalSpace B]
    (N : Subgroup A) [N.Normal] (f : A →ₜ* B)
    (hN : N ≤ f.toMonoidHom.ker) : A ⧸ N →ₜ* B := by
  let φ : A ⧸ N →* B := QuotientGroup.lift N f.toMonoidHom hN
  have hcomp : Continuous (fun x : A => φ (QuotientGroup.mk' N x)) := by
    simpa [φ, QuotientGroup.lift_mk'] using f.continuous_toFun
  exact
    { toMonoidHom := φ
      continuous_toFun :=
        (QuotientGroup.isQuotientMap_mk (G := A) (N := N)).continuous_iff.2 hcomp }

/-- A bijective continuous homomorphism from a compact group to a Hausdorff
group is a continuous multiplicative equivalence. -/
noncomputable def continuousMulEquivOfBijectiveCompactToT2
    {A : Type*} {B : Type*} [Group A] [TopologicalSpace A]
    [Group B] [TopologicalSpace B] [CompactSpace A] [T2Space B]
    (φ : A →* B) (hφcont : Continuous φ) (hφ : Function.Bijective φ) :
    A ≃ₜ* B := by
  let e : A ≃ B := Equiv.ofBijective φ hφ
  let eh : A ≃ₜ B :=
    e.toHomeomorphOfContinuousClosed hφcont (Continuous.isClosedMap hφcont)
  exact ContinuousMulEquiv.mk' eh φ.map_mul

/-- A nonidentity element of a profinite group is omitted by some open normal
subgroup. -/
theorem exists_openNormalSubgroup_not_mem
    {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    {x : A} (hx : x ≠ 1) :
    ∃ U : OpenNormalSubgroup A, x ∉ (U : Subgroup A) := by
  let W : Set A := ({x} : Set A)ᶜ
  have hWopen : IsOpen W := isClosed_singleton.isOpen_compl
  have hWone : (1 : A) ∈ W := by
    simpa [W] using hx.symm
  obtain ⟨U, hUW⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (G := A) hWopen hWone
  refine ⟨U, ?_⟩
  intro hxU
  have hxW : x ∈ W := hUW hxU
  change x ∉ ({x} : Set A) at hxW
  exact hxW (by simp)


/-- Multiplication by `n` on `ℤ̂`, in the multiplicative presentation. -/
def zHatPowNat (n : ℕ) : ZHatMul →ₜ* ZHatMul where
  toFun z := Multiplicative.ofAdd (zHatMulNat n z.toAdd)
  map_one' := by
    apply Multiplicative.ext
    simp [zHatMulNat]
  map_mul' x y := by
    apply Multiplicative.ext
    exact nsmul_add x.toAdd y.toAdd n
  continuous_toFun := map_continuous (zHatMulNat n)

/-- The additive coordinate of a natural profinite power is multiplication by that natural. -/
@[simp]
theorem zHatPowNat_apply_toAdd (n : ℕ) (z : ZHatMul) :
    (zHatPowNat n z).toAdd = n • z.toAdd :=
  rfl

/-- The natural profinite power map sends one to the multiplicative generator. -/
@[simp]
theorem zHatPowNat_one (n : ℕ) :
    zHatPowNat n
        (Multiplicative.ofAdd (1 : ZHat)) =
      (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
  apply Multiplicative.ext
  rfl

/-- Reduction modulo `n`, in the multiplicative presentation. -/
def zHatReductionMul (n : ℕ) (hn : 0 < n) :
    ZHatMul →ₜ* Multiplicative (ZMod n) where
  toFun z := Multiplicative.ofAdd (zHatReduction n hn z.toAdd)
  map_one' := by
    apply Multiplicative.ext
    exact map_zero (zHatReduction n hn)
  map_mul' x y := by
    apply Multiplicative.ext
    exact map_add (zHatReduction n hn) x.toAdd y.toAdd
  continuous_toFun := map_continuous (zHatReduction n hn)

/-- Reduction followed by multiplication has the expected additive-coordinate formula. -/
@[simp]
theorem zHatReductionMul_apply_toAdd (n : ℕ) (hn : 0 < n)
    (z : ZHatMul) :
    (zHatReductionMul n hn z).toAdd = zHatReduction n hn z.toAdd :=
  rfl

namespace DegreeData

/-- The positive integer `d_K(σ)` attached to a Frobenius lift. -/
def frobeniusExponent (D : DegreeData G) (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) : ℕ :=
  Exists.choose σ.2

/-- The Frobenius exponent attached to a finite extension is strictly positive. -/
theorem frobeniusExponent_pos (D : DegreeData G) (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    0 < D.frobeniusExponent K L hLK σ :=
  (Exists.choose_spec σ.2).1

/-- The normalized degree of Frobenius is the corresponding natural profinite power. -/
theorem extensionNormalizedDegree_frobenius_eq_pow (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.extensionNormalizedDegree K L hLK σ.1 =
      (Multiplicative.ofAdd (1 : ZHat)) ^
          D.frobeniusExponent K L hLK σ :=
  (Exists.choose_spec σ.2).2

/-- The factorized normalized degree as a continuous homomorphism. -/
def extensionNormalizedDegreeContinuous (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) →ₜ* ZHatMul :=
  { toMonoidHom := D.extensionNormalizedDegree K L hLK
    continuous_toFun :=
      (continuousQuotientLift (D.extensionInertiaWithin K.field L hLK)
        (D.normalizedDegree K)
        (by
          intro x hx
          rw [D.normalizedDegree_ker K]
          exact hx.2)).continuous_toFun }

/-- The continuous normalized-degree map evaluates as the algebraic normalized-degree map. -/
@[simp]
theorem extensionNormalizedDegreeContinuous_apply (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (x : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) :
    D.extensionNormalizedDegreeContinuous K L hLK x =
      D.extensionNormalizedDegree K L hLK x :=
  rfl

/-- Forgetting continuity recovers the underlying normalized-degree monoid homomorphism. -/
@[simp]
theorem extensionNormalizedDegreeContinuous_toMonoidHom (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom =
      D.extensionNormalizedDegree K L hLK :=
  rfl

/-- The continuous normalized-degree map of the extension is surjective. -/
theorem extensionNormalizedDegreeContinuous_surjective (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    Function.Surjective
      (D.extensionNormalizedDegreeContinuous K L hLK) := by
  intro z
  obtain ⟨k, hk⟩ := D.normalizedDegree_surjective K z
  refine ⟨QuotientGroup.mk k, ?_⟩
  simpa using hk

/-- Restriction embeds the kernel of `d_K` on `G(\widetilde L|K)` into
the finite group `G(L|K)`. -/
def extensionDegreeKernelRestriction (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker →*
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK) :=
  (D.extensionRestriction K.field L hLK).comp
    (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker.subtype

/-- Restriction to the degree kernel is injective on the extension subgroup. -/
theorem extensionDegreeKernelRestriction_injective (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    Function.Injective
      (D.extensionDegreeKernelRestriction K L hLK) := by
  intro a b hab
  let c := (a.1 : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)⁻¹ * b.1
  have hcRestriction : D.extensionRestriction K.field L hLK c = 1 := by
    dsimp [c]
    rw [map_mul, map_inv]
    change (D.extensionDegreeKernelRestriction K L hLK a)⁻¹ *
        D.extensionDegreeKernelRestriction K L hLK b = 1
    rw [hab, inv_mul_cancel]
  have hcDegree :
      D.extensionNormalizedDegreeContinuous K L hLK c = 1 := by
    dsimp [c]
    rw [map_mul, map_inv]
    change (D.extensionNormalizedDegreeContinuous K L hLK a.1)⁻¹ *
        D.extensionNormalizedDegreeContinuous K L hLK b.1 = 1
    have ha : D.extensionNormalizedDegreeContinuous K L hLK a.1 = 1 := a.2
    have hb : D.extensionNormalizedDegreeContinuous K L hLK b.1 = 1 := b.2
    rw [ha, hb, inv_one, one_mul]
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
    (D.extensionInertiaWithin K.field L hLK) c
  have hkE : k ∈ extensionSubgroup K.field L hLK := by
    apply (QuotientGroup.eq_one_iff k).mp
    rw [← hk] at hcRestriction
    simpa using hcRestriction
  have hkI : k ∈ D.fieldInertiaWithin K.field := by
    rw [← D.normalizedDegree_ker K]
    change D.normalizedDegree K k = 1
    rw [← hk] at hcDegree
    simpa using hcDegree
  have hkc : k ∈ D.extensionInertiaWithin K.field L hLK :=
    ⟨hkE, hkI⟩
  have hcOne : c = 1 := by
    rw [← hk]
    exact (QuotientGroup.eq_one_iff k).mpr hkc
  apply Subtype.ext
  exact inv_mul_eq_one.mp hcOne

/-- The extension's inertia subgroup is closed inside its base subgroup. -/
theorem extensionInertiaWithin_isClosed (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) :
    IsClosed (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup) := by
  have hE : IsClosed (extensionSubgroup K.field L hLK : Set K.field.toSubgroup) := by
    change IsClosed ((fun x : K.field.toSubgroup => (x : G)) ⁻¹' (L : Set G))
    exact L.isClosed'.preimage continuous_subtype_val
  have hI : IsClosed (D.fieldInertiaWithin K.field : Set K.field.toSubgroup) := by
    let : T2Space ZHatMul := by
      change T2Space ZHat
      infer_instance
    change IsClosed {x : K.field.toSubgroup | D.degree x.1 = 1}
    exact isClosed_eq
      (D.restrictedDegree K.field).continuous_toFun continuous_const
  change IsClosed
    ((extensionSubgroup K.field L hLK ⊓ D.fieldInertiaWithin K.field) : Set K.field.toSubgroup)
  exact hE.inter hI

/-- The closed cyclic subgroup `Γ = closure ⟨σ⟩` fixing the field `Σ`
of the Frobenius fixed-field theorem. -/
def frobeniusClosure (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    ClosedSubgroup
      (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) :=
  closedSubgroupGenerated
    (Set.range (fun _ : Unit => σ.1))

/-- The chosen Frobenius lift, regarded as an element of `Γ`. -/
def frobeniusInClosure (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusClosure K L hLK σ :=
  closedSubgroupGeneratedMap (fun _ : Unit => σ.1) ()

/-- The closure of the Frobenius-generated subgroup inherits a topological group structure. -/
instance frobeniusClosure_isTopologicalGroup
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    IsTopologicalGroup (D.frobeniusClosure K L hLK σ) := by
  change IsTopologicalGroup
    ↑((D.frobeniusClosure K L hLK σ).toSubgroup)
  infer_instance

/-- Defines `frobeniusClosureCommGroup`. -/
@[reducible] def frobeniusClosureCommGroup
    (D : DegreeData G) [IsTopologicalGroup G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    CommGroup (D.frobeniusClosure K L hLK σ) := by
  letI : IsClosed
      (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed K L hLK
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let s : Subgroup Q :=
    Subgroup.closure (Set.range (fun _ : Unit => σ.1))
  letI : IsMulCommutative ↑s :=
    isMulCommutative_iff.mpr (by
      intro a b
      have hrange : Set.range (fun _ : Unit => σ.1) = ({σ.1} : Set Q) := by
        ext y
        simp
      have ha : (a : Q) ∈ Subgroup.zpowers σ.1 := by
        simpa [s, hrange, Subgroup.zpowers_eq_closure] using a.2
      have hb : (b : Q) ∈ Subgroup.zpowers σ.1 := by
        simpa [s, hrange, Subgroup.zpowers_eq_closure] using b.2
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
      apply Subtype.ext
      change (a : Q) * (b : Q) = (b : Q) * (a : Q)
      rw [← hm, ← hn, ← zpow_add, add_comm, zpow_add])
  let c : CommGroup ↑s.topologicalClosure :=
    Subgroup.commGroupTopologicalClosure s
      (fun x y => Subtype.ext_iff.mpr (by
        have := (inferInstance : IsMulCommutative ↑s)
        exact congrArg Subtype.val (this.is_comm.comm x y)))
  letI : IsMulCommutative (D.frobeniusClosure K L hLK σ) :=
    isMulCommutative_iff.mpr c.mul_comm
  exact open scoped IsMulCommutative in inferInstance

/-- By construction, `σ` topologically generates `Γ`. -/
theorem frobeniusInClosure_topologicallyGenerates
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    TopologicallyGenerates
      ({D.frobeniusInClosure K L hLK σ} : Set
        (D.frobeniusClosure K L hLK σ)) := by
  let φ : Unit →
      (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) :=
    fun _ => σ.1
  have hgen := closedSubgroupGeneratedMap_topologicallyGenerates φ
  have hrange : Set.range (closedSubgroupGeneratedMap φ) =
      ({closedSubgroupGeneratedMap φ ()} : Set
        (closedSubgroupGenerated (Set.range φ))) := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl⟩
      cases u
      rfl
    · intro hx
      exact ⟨(), hx.symm⟩
  rw [hrange] at hgen
  change TopologicallyGenerates
    ({closedSubgroupGeneratedMap φ ()} : Set
      (closedSubgroupGenerated (Set.range φ) : Subgroup _))
  exact hgen

end DegreeData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Abstract_KummerGlobalOperator
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.extensionInertiaWithin_normal _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField
attribute [-simp] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.extensionSubgroup_index_eq_degree _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ofInclusion_base _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ofInclusion_field _root_.ClassFormation.DegreeData.GaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.extensionRestriction_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace KummerTheory

open CyclicCohomology

/-!
# finite abelian Kummer theory, the finite abelian Kummer decomposition: descending the global operator

This file constructs, rather than assumes, the endomorphism of `A_L` induced
by a global equivariant endomorphism `wp : A ⟶ A`.  It also embeds a
`G_K`-fixed global kernel element into the invariant subtype defining `A_L`
and supplies these constructions to the finite cyclic single-radical theorem.

The result remains only the finite cyclic step of the finite abelian Kummer decomposition, not the
full abelian Kummer correspondence.
-/

noncomputable section

open CategoryTheory

/-- The endomorphism of `A_L` induced functorially by a global equivariant
endomorphism `wp : A ⟶ A`: first restrict to `G_K`, then pass to the
`G_L`-invariants and the quotient action. -/
noncomputable def extensionFixedEndomorphism
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (wp : A ⟶ A) :
    extensionFixedRepresentation A K L hLK hnormal ⟶
      extensionFixedRepresentation A K L hLK hnormal :=
  (Rep.quotientToInvariantsFunctor (k := ℤ) (extensionSubgroup K L hLK)).map
    ((Rep.resFunctor K.toSubgroup.subtype).map wp)

/-- A global element fixed by `G_K`, viewed in the invariant subtype which
is the carrier of `A_L`. -/
noncomputable def extensionFixedKernelElement
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (xi : A.V) (hxi_fixed : ∀ k : K.toSubgroup, A.ρ k.1 xi = xi) :
    (extensionFixedRepresentation A K L hLK hnormal).V :=
  ⟨xi, by
    intro s
    change A.ρ s.1.1 xi = xi
    exact hxi_fixed s.1⟩

/-- The underlying value of the fixed kernel element is the selected global kernel element. -/
@[simp]
theorem extensionFixedKernelElement_val
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (xi : A.V) (hxi_fixed : ∀ k : K.toSubgroup, A.ρ k.1 xi = xi) :
    (extensionFixedKernelElement A K L hLK xi hxi_fixed).1 = xi := rfl

/-- The extension-fixed endomorphism acts on underlying values by the global operator. -/
@[simp]
theorem extensionFixedEndomorphism_apply_val
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (wp : A ⟶ A) (x : (extensionFixedRepresentation A K L hLK hnormal).V) :
    ((extensionFixedEndomorphism A K L hLK wp).hom x).1 = wp.hom x.1 := by
  rfl

end
end KummerTheory
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Abstract_KummerAbelianCyclicFactors
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.extensionInertiaWithin_normal _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace KummerTheory

open CyclicCohomology

/-!
# finite abelian Kummer theory, the finite abelian Kummer decomposition: cyclic factors of a finite abelian extension

The proof of the finite abelian Kummer decomposition reduces a finite abelian extension to cyclic
subextensions.  This file supplies the group-theoretic source for that step.
A finite commutative group is written as a finite product of cyclic `ZMod`
groups.  The kernels of its coordinate maps have trivial intersection.
Pulling those kernels back along a quotient map produces intermediate
subgroups whose quotients are finite cyclic and whose intersection is the
original normal subgroup.

No radical generators or field-lattice endpoint are asserted here.
-/

noncomputable section

section FiniteAbelianCyclicFactors

/-- Coordinate characters obtained from the structure theorem separate the
elements of a finite commutative group. -/
theorem finiteCommGroup_exists_jointlyFaithful_cyclic_factors
    (Q : Type*) [CommGroup Q] [Finite Q] :
    ∃ (ι : Type 0) (_ : Fintype ι) (m : ι → ℕ),
      (∀ i, 1 < m i) ∧
      ∃ f : ∀ i, Q →* Multiplicative (ZMod (m i)),
        (∀ i, Function.Surjective (f i)) ∧
        (⨅ i, MonoidHom.ker (f i)) = ⊥ := by
  obtain ⟨ι, hι, m, hm, ⟨e⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite Q
  let f : ∀ i, Q →* Multiplicative (ZMod (m i)) := fun i =>
    (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (m j))) i).comp e
  refine ⟨ι, hι, m, hm, f, ?_, ?_⟩
  · intro i
    exact (Function.surjective_eval i).comp e.surjective
  · apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_bot]
      apply e.injective
      ext i
      have hxi : x ∈ MonoidHom.ker (f i) :=
        (Subgroup.mem_iInf.mp hx) i
      simpa [f] using MonoidHom.mem_ker.mp hxi
    · exact bot_le

end FiniteAbelianCyclicFactors

section ClosedCyclicSubextensions

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A closed abstract field subgroup `G_L` remains closed when regarded as
a subgroup of the larger abstract field subgroup `G_K`. -/
theorem extensionSubgroup_isClosed
    {G : Type*} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    IsClosed (extensionSubgroup (G := G) K L hLK : Set K.toSubgroup) := by
  change IsClosed ((fun x : K.toSubgroup => (x : G)) ⁻¹' (L : Set G))
  exact L.isClosed'.preimage continuous_subtype_val

end ClosedCyclicSubextensions

end
end KummerTheory
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Abstract_KummerAbelianAssembly
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.extensionInertiaWithin_normal _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField
attribute [-simp] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.extensionSubgroup_index_eq_degree _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ofInclusion_base _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ofInclusion_field _root_.ClassFormation.DegreeData.GaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.extensionRestriction_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace KummerTheory

open CyclicCohomology

/-!
# finite abelian Kummer theory, the finite abelian Kummer decomposition: assembling cyclic radicals

This file connects elements produced in the invariant subtype `A_M` to the
ambient representation `A`.  A cyclic radical with trivial stabilizer in
`G_K / G_M` is fixed in the ambient module by exactly `G_M`.  Consequently,
a family of such radicals whose subgroups intersect in `G_L` generates the
abstract field `L` over `K`.
-/

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Membership in `G_L`, regarded as a subgroup of `G_K`, is the same as
ambient membership in the closed subgroup `G_L`. -/
@[simp]
theorem mem_extensionSubgroup_iff
    {G : Type*} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (k : K.toSubgroup) :
    k ∈ extensionSubgroup (G := G) K L hLK ↔ (k : G) ∈ L :=
  Iff.rfl

/-- The quotient action on an invariant subtype is the original ambient
action after choosing a representative in `G_K`. -/
@[simp]
theorem extensionFixedRepresentation_quotient_mk_apply_val
    (A : Rep ℤ G) (K M : ClosedSubgroup G)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K M hMK).Normal]
    (a : (extensionFixedRepresentation A K M hMK hnormal).V)
    (k : K.toSubgroup) :
    ((extensionFixedRepresentation A K M hMK hnormal).ρ
      ((QuotientGroup.mk' (extensionSubgroup (G := G) K M hMK)) k) a).1 =
      A.ρ k.1 a.1 := rfl

end
end KummerTheory
end

section
-- module Solutions.OAIQ244_DUKE.Kummer_Abstract_KummerDelta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace KummerTheory

open CyclicCohomology

/-!
# finite abelian Kummer theory, the finite abelian Kummer decomposition: the exact Delta

For an equivariant additive operator `wp`, the construction defines
`Delta = wp(A_L) ∩ A_K`.  Here fixed modules are represented as ambient
additive subgroups.  The finite abelian assembly supplies finitely many
elements in `wp⁻¹(Delta)` generating `L`; the reverse fixing inclusion uses
the construction datum that the kernel of `wp` is generated by its distinguished
element `xi`.
-/

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Ambient coefficient elements fixed pointwise by a closed abstract field
subgroup. -/
def ambientFixedAddSubgroup (A : Rep ℤ G) (H : ClosedSubgroup G) :
    AddSubgroup A.V := by
  exact
    { carrier := {a | ∀ h : H.toSubgroup, A.ρ h.1 a = a}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb h
        rw [map_add, ha h, hb h]
      neg_mem' := by
        intro a ha h
        rw [map_neg, ha h] }

/-- Membership in the ambient fixed subgroup is equivalent to invariance under every
subgroup element. -/
@[simp]
theorem mem_ambientFixedAddSubgroup_iff
    (A : Rep ℤ G) (H : ClosedSubgroup G) (a : A.V) :
    a ∈ ambientFixedAddSubgroup A H ↔
      ∀ h : H.toSubgroup, A.ρ h.1 a = a :=
  Iff.rfl

end
end KummerTheory
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_Norm
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.extensionInertiaWithin_normal _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField
attribute [-simp] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.extensionSubgroup_index_eq_degree _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ofInclusion_base _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ofInclusion_field _root_.ClassFormation.DegreeData.GaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_mk _root_.ClassFormation.DegreeData.extensionRestriction_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# normalized degree and Frobenius theory: norms on abstract fields

This file constructs the norm attached to a finite extension of the
abstract fields.  An abstract field is represented, as in, by a closed
subgroup of the ambient profinite group.  The norm is the sum over left
cosets (the additive form of the multiplicative product), so it does
not require the extension to be Galois.
-/

noncomputable section

open scoped BigOperators

-- Mathlib's `Rep ℤ G` currently fixes `G` to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The value of a fixed coefficient at a left coset.  This is independent
of the representative precisely because the coefficient is fixed by the
smaller abstract-field subgroup. -/
def relativeCosetAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) : A.V :=
  Quotient.liftOn' q (fun k : K.toSubgroup => A.ρ k.1 a.1) (by
    intro x y hxy
    have hmem : x⁻¹ * y ∈ extensionSubgroup K L hLK :=
      QuotientGroup.leftRel_apply.mp hxy
    let l : L.toSubgroup := ⟨(x⁻¹ * y).1, hmem⟩
    have hy : y = x * ⟨l.1, hLK l.2⟩ := by
      apply Subtype.ext
      simp [l]
    rw [hy]
    change A.ρ x.1 a.1 = A.ρ (x.1 * l.1) a.1
    rw [map_mul]
    change A.ρ x.1 a.1 = A.ρ x.1 (A.ρ l.1 a.1)
    rw [a.2 l])

/-- The relative coset action on a quotient representative is the corresponding group action. -/
@[simp]
theorem relativeCosetAction_mk
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A L) (k : K.toSubgroup) :
    relativeCosetAction A K L hLK a (QuotientGroup.mk k) = A.ρ k.1 a.1 :=
  rfl

/-- Left multiplication permutes the cosets of an arbitrary subgroup. -/
def leftMulCosetEquiv {G : Type*} [Group G]
    (H : Subgroup G) (g : G) : (G ⧸ H) ≃ (G ⧸ H) where
  toFun q := g • q
  invFun q := g⁻¹ • q
  left_inv q := by simp
  right_inv q := by simp

/-- Left multiplication sends the coset of `x` to the coset of `g * x`. -/
@[simp] theorem leftMulCosetEquiv_mk {G : Type*} [Group G]
    (H : Subgroup G) (g x : G) :
    leftMulCosetEquiv H g (QuotientGroup.mk x) = QuotientGroup.mk (g * x) :=
  rfl

/-- The additive norm value from `A_L` to the ambient module. -/
def relativeNormValue
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A L) : A.V := by
  letI := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  exact ∑ q, relativeCosetAction A K L hLK a q

/-- The relative coset action is additive in the represented fixed element. -/
theorem relativeCosetAction_add
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a b : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    relativeCosetAction A K L hLK (a + b) q =
      relativeCosetAction A K L hLK a q +
        relativeCosetAction A K L hLK b q := by
  refine Quotient.inductionOn' q ?_
  intro k
  simp only [relativeCosetAction_mk]
  exact map_add (A.ρ k.1) a.1 b.1

/-- Every relative coset acts trivially on the zero fixed element. -/
@[simp]
theorem relativeCosetAction_zero
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    relativeCosetAction A K L hLK 0 q = 0 := by
  refine Quotient.inductionOn' q ?_
  intro k
  simp only [relativeCosetAction_mk]
  exact map_zero (A.ρ k.1)

/-- The relative norm value is fixed by the base subgroup action. -/
theorem relativeNormValue_fixed
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A L) (k : K.toSubgroup) :
    A.ρ k.1 (relativeNormValue A K L hLK a) =
      relativeNormValue A K L hLK a := by
  let := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  have hterm : ∀ q : K.toSubgroup ⧸ extensionSubgroup K L hLK,
      A.ρ k.1 (relativeCosetAction A K L hLK a q) =
        relativeCosetAction A K L hLK a
          (leftMulCosetEquiv (extensionSubgroup K L hLK) k q) := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    simp only [relativeCosetAction_mk, leftMulCosetEquiv_mk]
    change A.ρ k.1 (A.ρ x.1 a.1) = A.ρ (k.1 * x.1) a.1
    rw [map_mul]
    rfl
  rw [relativeNormValue]
  simp_rw [map_sum, hterm]
  exact (leftMulCosetEquiv (extensionSubgroup K L hLK) k).sum_comp
    (relativeCosetAction A K L hLK a)

/-- The norm homomorphism for a finite abstract extension `L | K`.

In the multiplicative notation of the construction this additive sum is the product
over a system of representatives of `G_K / G_L`.  Its codomain is the
actual fixed module `A_K`, with fixedness proved by coset reindexing. -/
def relativeNorm
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    ambientFixedAddSubgroup A L →+ ambientFixedAddSubgroup A K where
  toFun a := ⟨relativeNormValue A K L hLK a,
    relativeNormValue_fixed A K L hLK a⟩
  map_zero' := by
    apply Subtype.ext
    let := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    simp [relativeNormValue]
  map_add' a b := by
    apply Subtype.ext
    let := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    simp only [AddSubgroup.coe_add, relativeNormValue]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    exact relativeCosetAction_add A K L hLK a b q

/-- Coercing a relative norm gives the explicit sum over quotient representatives. -/
@[simp]
theorem relativeNorm_apply_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A L) :
    ((relativeNorm A K L hLK a : ambientFixedAddSubgroup A K) : A.V) =
      relativeNormValue A K L hLK a :=
  rfl

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_Valuation
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The norm `N_{K|k}` on the actual fixed modules. -/
def normToBase (A : Rep ℤ G) (K : ClosedSubgroup G)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))] :
    ambientFixedAddSubgroup A K →+
      ambientFixedAddSubgroup A (baseField G) :=
  relativeNorm A (baseField G) K (le_baseField K)

/-- Multiplication by `n` on an additive subgroup. -/
def nsmulOnAddSubgroup (Z : AddSubgroup ZHat) (n : ℕ) : Z →+ Z where
  toFun z := ⟨n • z.1, Z.nsmul_mem z.2 n⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- The subgroup `nZ` inside a value group `Z`. -/
def nsmulWithin (Z : AddSubgroup ZHat) (n : ℕ) : AddSubgroup Z :=
  (nsmulOnAddSubgroup Z n).range

/-- The ambient subgroup `nZ ⊆ ℤ̂`. -/
def nsmulImage (Z : AddSubgroup ZHat) (n : ℕ) : AddSubgroup ZHat :=
  Z.map
    { toFun := fun z : ZHat => n • z
      map_zero' := nsmul_zero n
      map_add' := fun x y => nsmul_add x y n }

/-- An element belongs to the natural-multiple image exactly when it has a
preimage in the subgroup. -/
@[simp]
theorem mem_nsmulImage_iff (Z : AddSubgroup ZHat) (n : ℕ) (z : ZHat) :
    z ∈ nsmulImage Z n ↔ ∃ x ∈ Z, n • x = z := by
  rfl

/-- Multiples of the full value group are the range of multiplication
by the same natural number on `ZHat`. -/
@[simp]
theorem nsmulImage_top (n : ℕ) :
    nsmulImage (⊤ : AddSubgroup ZHat) n =
      (zHatMulNat n).toAddMonoidHom.range := by
  ext z
  constructor
  · rintro ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, AddSubgroup.mem_top x, rfl⟩

/-- Restriction of reduction modulo `n` along the inclusion `Z ≤ ℤ̂`. -/
def valueGroupReduction (Z : AddSubgroup ZHat) (n : ℕ) (hn : 0 < n) :
    Z →+ ZMod n :=
  (zHatReduction n hn).toAddMonoidHom.comp Z.subtype

/-- The canonical map `Z/nZ → ℤ/nℤ` induced by the inclusion `Z ≤ ℤ̂`
and reduction modulo `n`.

This is the specific map required in the valuation-quotient axiom, rather than an
arbitrarily chosen abstract equivalence between the two quotients. -/
def canonicalValueQuotientMap (Z : AddSubgroup ZHat)
    (n : ℕ) (hn : 0 < n) : (Z ⧸ nsmulWithin Z n) →+ ZMod n :=
  QuotientAddGroup.lift (nsmulWithin Z n) (valueGroupReduction Z n hn) (by
    rintro _ ⟨z, rfl⟩
    change zHatReduction n hn (n • (z : ZHat)) = 0
    rw [map_nsmul]
    simp [nsmul_eq_mul])

/-- The canonical value map evaluates on a quotient representative by reduction modulo `n`. -/
@[simp]
theorem canonicalValueQuotientMap_mk (Z : AddSubgroup ZHat)
    (n : ℕ) (hn : 0 < n) (z : Z) :
    canonicalValueQuotientMap Z n hn
        (QuotientAddGroup.mk' (nsmulWithin Z n) z) =
      zHatReduction n hn (z : ZHat) :=
  rfl

/-- The quotient used by the norm has the positive degree carried by a
finite abstract field. -/
@[simp] theorem FiniteAbstractField.normToBase_index_eq_degree
    {G : Type*} [Group G] [TopologicalSpace G]
    (K : FiniteAbstractField G) :
    (extensionSubgroup (baseField G) K.field
      (le_baseField K.field)).index =
      (K.toFiniteAbstractExtension.degree : ℕ) :=
  K.toFiniteAbstractExtension.extensionSubgroup_index_eq_degree

/-- **the valuation-quotient axiom.** A henselian valuation of `A_k` with respect to `d`.

`integers_mem` and `canonical_value_quotient_bijective` are precisely
condition (i), while `norm_range` is condition (ii). -/
structure ValuationData (D : DegreeData G) (A : Rep ℤ G) where
  /-- The additive valuation on the distinguished base-field fixed module. -/
  toAddMonoidHom : ambientFixedAddSubgroup A (baseField G) →+ ZHat
  /-- Every integral value occurs in the image of the valuation. -/
  integers_mem : ∀ m : ℤ,
    (Int.castRingHom ZHat) m ∈
      toAddMonoidHom.range
  /-- Reduction of the value group modulo every positive integer is bijective. -/
  canonical_value_quotient_bijective : ∀ (n : ℕ) (hn : 0 < n),
    Function.Bijective
      (canonicalValueQuotientMap toAddMonoidHom.range n hn)
  /-- Norms from a finite abstract field have the prescribed value-group image. -/
  norm_range : ∀ K : FiniteAbstractField G,
    (toAddMonoidHom.comp (normToBase A K.field)).range =
      nsmulImage toAddMonoidHom.range (K.residueDegree D : ℕ)

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The value group `Z = v(A_k)`. -/
def valueGroup (v : ValuationData D A) : AddSubgroup ZHat :=
  v.toAddMonoidHom.range

/-- The valuation-quotient axiom's canonical map for a henselian valuation. -/
def canonicalQuotientMap (v : ValuationData D A)
    (n : ℕ) (hn : 0 < n) :
    (v.valueGroup ⧸ nsmulWithin v.valueGroup n) →+ ZMod n :=
  canonicalValueQuotientMap v.valueGroup n hn

/-- The former equivalence API, now derived from the bijectivity of the
canonical inclusion-and-reduction map in the valuation-quotient axiom. -/
def cyclic_value_quotients (v : ValuationData D A)
    (n : ℕ) (hn : 0 < n) :
    (v.valueGroup ⧸ nsmulWithin v.valueGroup n) ≃+ ZMod n :=
  AddEquiv.ofBijective (v.canonicalQuotientMap n hn)
    (v.canonical_value_quotient_bijective n hn)

/-- Canonical reduction of the value group modulo `n`. -/
def valueModulo (v : ValuationData D A) (n : ℕ) (hn : 0 < n) :
    v.valueGroup →+ ZMod n :=
  (v.cyclic_value_quotients n hn).toAddMonoidHom.comp
    (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n))

/-- Value modulo `n` is profinite-integer reduction of the underlying value. -/
@[simp]
theorem valueModulo_apply (v : ValuationData D A)
    (n : ℕ) (hn : 0 < n) (z : v.valueGroup) :
    v.valueModulo n hn z = zHatReduction n hn (z : ZHat) :=
  rfl

/-- Reduction of the value group modulo a positive integer is surjective. -/
theorem valueModulo_surjective (v : ValuationData D A)
    (n : ℕ) (hn : 0 < n) :
    Function.Surjective (v.valueModulo n hn) := by
  intro z
  obtain ⟨q, rfl⟩ := (v.cyclic_value_quotients n hn).surjective z
  refine Quotient.inductionOn' q ?_
  intro a
  exact ⟨a, rfl⟩

/-- The norm composite `v ∘ N_{K|k}` before division by the residue degree. -/
def normCompositeAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ ZHat :=
  v.toAddMonoidHom.comp (normToBase A K.field)

/-- The norm-valuation composite has range equal to the residue-degree multiple image. -/
theorem normCompositeAt_range (v : ValuationData D A) (K : FiniteAbstractField G) :
    (v.normCompositeAt K).range =
      nsmulImage v.valueGroup (K.residueDegree D : ℕ) :=
  v.norm_range K

/-- `v(N_{K|k}a)` regarded as an element of `f_K ℤ̂`. -/
def normCompositeAtInResidueImage (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+
      (zHatMulNat (K.residueDegree D : ℕ)).toAddMonoidHom.range where
  toFun a := ⟨v.normCompositeAt K a, by
    have ha : v.normCompositeAt K a ∈ (v.normCompositeAt K).range := ⟨a, rfl⟩
    rw [v.normCompositeAt_range K] at ha
    obtain ⟨z, _hz, hz⟩ := ha
    exact ⟨z, hz⟩⟩
  map_zero' := by ext; simp [normCompositeAt]
  map_add' x y := by
    apply Subtype.ext
    exact map_add (v.normCompositeAt K) x y

/-- Division by `f_K` before restricting the codomain back to `Z`. -/
def dividedAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ ZHat :=
  (zHatDivide (K.residueDegree D : ℕ)
    (K.residueDegree D).property).toAddMonoidHom.comp
      (v.normCompositeAtInResidueImage K)

/-- The defining identity `f_K v_K = v ∘ N_{K|k}` before codomain
restriction. -/
theorem residueDegree_nsmul_dividedAt (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    (K.residueDegree D : ℕ) • v.dividedAt K a = v.normCompositeAt K a := by
  exact zHatMulNat_zHatDivide (K.residueDegree D : ℕ)
    (K.residueDegree D).property
    (v.normCompositeAtInResidueImage K a)

/-- The divided value lies in the original value group `Z`. -/
theorem dividedAt_mem_valueGroup (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    v.dividedAt K a ∈ v.valueGroup := by
  have ha : v.normCompositeAt K a ∈ (v.normCompositeAt K).range := ⟨a, rfl⟩
  rw [v.normCompositeAt_range K] at ha
  obtain ⟨z, hzZ, hz⟩ := ha
  have hzSubtype : v.normCompositeAtInResidueImage K a =
      ⟨zHatMulNat (K.residueDegree D : ℕ) z, ⟨z, rfl⟩⟩ := by
    apply Subtype.ext
    change v.normCompositeAt K a =
      zHatMulNat (K.residueDegree D : ℕ) z
    exact hz.symm
  change zHatDivide (K.residueDegree D : ℕ)
      (K.residueDegree D).property
        (v.normCompositeAtInResidueImage K a) ∈ v.valueGroup
  rw [hzSubtype]
  exact (zHatDivide_zHatMulNat (K.residueDegree D : ℕ)
    (K.residueDegree D).property z).symm ▸ hzZ

/-- The normalized valuation `v_K = (1/f_K) v ∘ N_{K|k}`, with the exact
codomain `Z` from the valuation-quotient axiom. -/
def valuationAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ v.valueGroup :=
  (v.dividedAt K).codRestrict v.valueGroup (fun a => v.dividedAt_mem_valueGroup K a)

/-- The underlying profinite value of the positive valuation is the divided valuation. -/
@[simp]
theorem valuationAt_coe (v : ValuationData D A) (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    (v.valuationAt K a : ZHat) = v.dividedAt K a :=
  rfl

/-- **normalized-valuation functoriality (surjectivity).** The normalized valuation over every
finite abstract field maps onto `Z`. -/
theorem normalizedValuation_surjective (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    Function.Surjective (v.valuationAt K) := by
  intro z
  have hzImage : (K.residueDegree D : ℕ) • z.1 ∈
      nsmulImage v.valueGroup (K.residueDegree D : ℕ) :=
    ⟨z.1, z.2, rfl⟩
  rw [← v.normCompositeAt_range K] at hzImage
  obtain ⟨a, ha⟩ := hzImage
  refine ⟨a, ?_⟩
  apply Subtype.ext
  change zHatDivide (K.residueDegree D : ℕ)
      (K.residueDegree D).property
        (v.normCompositeAtInResidueImage K a) = z.1
  have hsub : v.normCompositeAtInResidueImage K a =
      ⟨zHatMulNat (K.residueDegree D : ℕ) z.1, ⟨z.1, rfl⟩⟩ := by
    apply Subtype.ext
    change v.normCompositeAt K a =
      zHatMulNat (K.residueDegree D : ℕ) z.1
    exact ha
  rw [hsub]
  exact zHatDivide_zHatMulNat (K.residueDegree D : ℕ)
    (K.residueDegree D).property z.1

end ValuationData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_NormLaws
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# Laws for relative norms

This file proves the structural laws for the coset-sum norm constructed in `Norm.lean`.
-/

noncomputable section

open scoped BigOperators Pointwise

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The subgroup corresponding to the conjugate abstract field `K^σ`.

The construction uses a right exponent, hence `G_{K^σ} = σ⁻¹ G_K σ`. -/
def conjugateClosedSubgroup {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G) : ClosedSubgroup G where
  toSubgroup := ConjAct.toConjAct σ⁻¹ • K.toSubgroup
  isClosed' := by
    convert IsClosed.preimage
      (IsTopologicalGroup.continuous_conj (G := G) σ) K.isClosed' using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    change x ∈ (ConjAct.toConjAct σ⁻¹ • K.toSubgroup : Subgroup G) ↔
      σ * x * σ⁻¹ ∈ K.toSubgroup
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]

/--
Characterizes `x ∈ conjugateClosedSubgroup K σ` by the equivalent condition `σ * x * σ⁻¹ ∈ K`.
-/
@[simp]
theorem conjugateClosedSubgroup_mem {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G]
    (K : ClosedSubgroup G) (σ x : G) :
    x ∈ conjugateClosedSubgroup K σ ↔ σ * x * σ⁻¹ ∈ K := by
  change x ∈ (ConjAct.toConjAct σ⁻¹ • K.toSubgroup : Subgroup G) ↔
    σ * x * σ⁻¹ ∈ K.toSubgroup
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]

/-- The right-conjugate `a^σ`, expressed through the left action of `G`. -/
def conjugateFixedElement [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K) :
    ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ) := by
  refine ⟨A.ρ σ⁻¹ a.1, ?_⟩
  intro x
  let k : K.toSubgroup := ⟨σ * x.1 * σ⁻¹,
    (conjugateClosedSubgroup_mem K σ x.1).mp x.2⟩
  calc
    A.ρ x.1 (A.ρ σ⁻¹ a.1) = A.ρ (x.1 * σ⁻¹) a.1 := by
      rw [map_mul]
      rfl
    _ = A.ρ (σ⁻¹ * k.1) a.1 := by simp [k, mul_assoc]
    _ = A.ρ σ⁻¹ (A.ρ k.1 a.1) := by
      rw [map_mul]
      rfl
    _ = A.ρ σ⁻¹ a.1 := by rw [a.2 k]

/--
Establishes the identity `((conjugateFixedElement A K σ a : ambientFixedAddSubgroup A
(conjugateClosedSubgroup K σ)) : A.V) = A.ρ σ⁻¹ a.1`.
-/
@[simp]
theorem conjugateFixedElement_coe [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K) :
    ((conjugateFixedElement A K σ a :
      ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ)) : A.V) =
      A.ρ σ⁻¹ a.1 :=
  rfl

def absoluteConjugationEquiv {G : Type*} [Group G] [TopologicalSpace G]
    (σ : G) :
    (baseField G).toSubgroup ≃
      (baseField G).toSubgroup where
  toFun x := ⟨σ * x.1 * σ⁻¹, trivial⟩
  invFun x := ⟨σ⁻¹ * x.1 * σ, trivial⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]

theorem mem_absoluteExtension {G : Type*} [Group G] [TopologicalSpace G]
    (K : ClosedSubgroup G)
    (x : (baseField G).toSubgroup) :
    x ∈ extensionSubgroup (baseField G) K
        (le_baseField K) ↔ x.1 ∈ K :=
  Iff.rfl

/-- Conjugation identifies the absolute coset spaces for `K^σ` and `K`. -/
noncomputable def absoluteConjugateCosetEquiv
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G) :
    ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (conjugateClosedSubgroup K σ)
          (le_baseField (conjugateClosedSubgroup K σ))) ≃
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K)) :=
  Quotient.congr (absoluteConjugationEquiv σ) (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply,
      mem_absoluteExtension, mem_absoluteExtension,
      conjugateClosedSubgroup_mem]
    change σ * (x.1⁻¹ * y.1) * σ⁻¹ ∈ K.toSubgroup ↔
      (σ * x.1 * σ⁻¹)⁻¹ * (σ * y.1 * σ⁻¹) ∈ K.toSubgroup
    simp [mul_assoc])

/--
Establishes the identity `absoluteConjugateCosetEquiv K σ (QuotientGroup.mk x) = QuotientGroup.mk
(absoluteConjugationEquiv σ x)`.
-/
@[simp]
theorem absoluteConjugateCosetEquiv_mk
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G)
    (x : (baseField G).toSubgroup) :
    absoluteConjugateCosetEquiv K σ (QuotientGroup.mk x) =
      QuotientGroup.mk (absoluteConjugationEquiv σ x) :=
  rfl

theorem relativeCosetAction_absoluteConjugate [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K)
    (q : (baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))) :
    relativeCosetAction A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) q =
      A.ρ σ⁻¹
        (relativeCosetAction A (baseField G) K
          (le_baseField K) a
          (absoluteConjugateCosetEquiv K σ q)) := by
  refine Quotient.inductionOn' q ?_
  intro x
  rw [relativeCosetAction_mk, absoluteConjugateCosetEquiv_mk,
    relativeCosetAction_mk, conjugateFixedElement_coe]
  calc
    A.ρ x.1 (A.ρ σ⁻¹ a.1) = A.ρ (x.1 * σ⁻¹) a.1 := by
      rw [map_mul]
      rfl
    _ = A.ρ (σ⁻¹ * (σ * x.1 * σ⁻¹)) a.1 := by simp [mul_assoc]
    _ = A.ρ σ⁻¹ (A.ρ (σ * x.1 * σ⁻¹) a.1) := by
      rw [map_mul]
      rfl

/-- conjugation compatibility of normalized valuations: the absolute norm commutes with conjugation.

The construction writes the action on fields and elements on the right.  Thus the
left action used by `Rep` realizes `a^σ` as `ρ(σ⁻¹)a`. -/
theorem relativeNorm_absoluteConjugate_apply [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    [Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K))]
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G)
            (conjugateClosedSubgroup K σ)
            (le_baseField (conjugateClosedSubgroup K σ))) :=
      Finite.of_equiv
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) K
            (le_baseField K))
        (absoluteConjugateCosetEquiv K σ).symm
    ((relativeNorm A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) :
      ambientFixedAddSubgroup A (baseField G)) : A.V) =
      A.ρ σ⁻¹
        ((relativeNorm A (baseField G) K
          (le_baseField K) a :
          ambientFixedAddSubgroup A (baseField G)) : A.V) := by
  let := Fintype.ofFinite
    ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K
        (le_baseField K))
  let conjugateFintype : Fintype
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (conjugateClosedSubgroup K σ)
          (le_baseField (conjugateClosedSubgroup K σ))) :=
    Fintype.ofEquiv
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K))
      (absoluteConjugateCosetEquiv K σ).symm
  have hconjugateFintype : Fintype.ofFinite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (conjugateClosedSubgroup K σ)
          (le_baseField (conjugateClosedSubgroup K σ))) = conjugateFintype :=
    Subsingleton.elim _ _
  simp only [relativeNorm_apply_coe, relativeNormValue]
  rw [hconjugateFintype]
  calc
    ∑ q, relativeCosetAction A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) q =
      ∑ q, A.ρ σ⁻¹
        (relativeCosetAction A (baseField G) K
          (le_baseField K) a
          (absoluteConjugateCosetEquiv K σ q)) := by
            apply Finset.sum_congr rfl
            intro q _
            exact relativeCosetAction_absoluteConjugate A K σ a q
    _ = A.ρ σ⁻¹
        (∑ q, relativeCosetAction A (baseField G) K
          (le_baseField K) a
          (absoluteConjugateCosetEquiv K σ q)) := by
            rw [map_sum]
    _ = A.ρ σ⁻¹
        (∑ q, relativeCosetAction A (baseField G) K
          (le_baseField K) a q) := by
            rw [(absoluteConjugateCosetEquiv K σ).sum_comp]

/-- The action of an element of `G_K` on `A_L`, when `L | K` is Galois.

Normality is used only to prove that the translate is still fixed by `G_L`. -/
def normalExtensionAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    ambientFixedAddSubgroup A L := by
  refine ⟨A.ρ k.1 a.1, ?_⟩
  intro l
  let lK : K.toSubgroup := Subgroup.inclusion hLK l
  have hc : k⁻¹ * lK * k ∈ extensionSubgroup K L hLK :=
    by simpa using hnormal.conj_mem lK l.2 k⁻¹
  let l' : L.toSubgroup := ⟨(k⁻¹ * lK * k).1, hc⟩
  have hl'val : (l' : G) = (k⁻¹ * lK * k : K.toSubgroup) :=
    rfl
  calc
    A.ρ l.1 (A.ρ k.1 a.1) = A.ρ (l.1 * k.1) a.1 := by rw [map_mul]; rfl
    _ = A.ρ (k.1 * l'.1) a.1 := by rw [hl'val]; simp [lK, mul_assoc]
    _ = A.ρ k.1 (A.ρ l'.1 a.1) := by rw [map_mul]; rfl
    _ = A.ρ k.1 a.1 := by rw [a.2 l']

/--
Establishes the identity `((normalExtensionAction A K L hLK hnormal k a : ambientFixedAddSubgroup
A L) : A.V) = A.ρ k.1 a.1`.
-/
@[simp]
theorem normalExtensionAction_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    ((normalExtensionAction A K L hLK hnormal k a : ambientFixedAddSubgroup A L) : A.V) =
      A.ρ k.1 a.1 :=
  rfl

/-- For a finite Galois abstract extension, the relative norm is invariant under
the `G_K`-conjugacy action on `A_L`. -/
theorem relativeNorm_normalExtensionAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    relativeNorm A K L hLK (normalExtensionAction A K L hLK hnormal k a) =
      relativeNorm A K L hLK a := by
  apply Subtype.ext
  let := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let e : (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃
      (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    Equiv.mulRight (QuotientGroup.mk k)
  have hterm : ∀ q : K.toSubgroup ⧸ extensionSubgroup K L hLK,
      relativeCosetAction A K L hLK (normalExtensionAction A K L hLK hnormal k a) q =
        relativeCosetAction A K L hLK a (e q) := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    simp only [relativeCosetAction_mk, normalExtensionAction_coe]
    have he : e (QuotientGroup.mk x) = QuotientGroup.mk (x * k) := rfl
    rw [he, relativeCosetAction_mk]
    change A.ρ x.1 (A.ρ k.1 a.1) = A.ρ (x.1 * k.1) a.1
    rw [map_mul]
    rfl
  simp only [relativeNorm_apply_coe, relativeNormValue]
  simp_rw [hterm]
  exact e.sum_comp (relativeCosetAction A K L hLK a)

/-- Finiteness is closed under composition in a tower of closed subgroups. -/
theorem relativeTowerQuotientFinite
    {G : Type*} [Group G] [TopologicalSpace G]
    (K L M : ClosedSubgroup G)
    (hML : M.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [Finite (L.toSubgroup ⧸ extensionSubgroup L M hML)] :
    Finite
      (K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK)) :=
  Finite.of_equiv
    ((K.toSubgroup ⧸ extensionSubgroup K L hLK) ×
      (L.toSubgroup ⧸ extensionSubgroup L M hML))
    (Subgroup.quotientTowerEquiv hML hLK).symm

namespace DegreeData.FiniteTower

variable (T : DegreeData.FiniteTower G)

/-- The finite composite extension represented by a finite tower. -/
noncomputable def totalExtension : DegreeData.FiniteAbstractExtension G where
  toAbstractExtension := T.toTower.totalExtension
  finiteQuotient := relativeTowerQuotientFinite
    T.base T.middle T.top T.top_le_middle T.middle_le_base

/-- The quotient from the top to the base of a finite tower is finite. -/
instance totalQuotientFinite :
    Finite (T.base.toSubgroup ⧸
      extensionSubgroup T.base T.top
        (T.top_le_middle.trans T.middle_le_base)) :=
  T.totalExtension.finiteQuotient

end DegreeData.FiniteTower

theorem relativeCosetAction_towerProductEquiv
    (A : Rep ℤ G) (K L M : ClosedSubgroup G)
    (hML : M.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A M)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (r : L.toSubgroup ⧸ extensionSubgroup L M hML) :
    relativeCosetAction A K M (hML.trans hLK) a
        ((Subgroup.quotientTowerEquiv hML hLK).symm (q, r)) =
      A.ρ (Quotient.out q).1 (relativeCosetAction A L M hML a r) := by
  refine Quotient.inductionOn' r ?_
  intro x
  have he : (Subgroup.quotientTowerEquiv hML hLK).symm
      (q, QuotientGroup.mk x) =
      QuotientGroup.mk (Quotient.out q * Subgroup.inclusion hLK x) := rfl
  rw [he, relativeCosetAction_mk, relativeCosetAction_mk]
  change A.ρ ((Quotient.out q).1 * x.1) a.1 =
    A.ρ (Quotient.out q).1 (A.ρ x.1 a.1)
  rw [map_mul]
  rfl

theorem finiteTowerNormTransApplyAux
    (A : Rep ℤ G) (K L M : ClosedSubgroup G)
    (hML : M.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [Finite (L.toSubgroup ⧸ extensionSubgroup L M hML)]
    (a : ambientFixedAddSubgroup A M) :
    letI : Finite (K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK)) :=
      relativeTowerQuotientFinite K L M hML hLK
    relativeNorm A K L hLK (relativeNorm A L M hML a) =
      relativeNorm A K M (hML.trans hLK) a := by
  apply Subtype.ext
  let := Fintype.ofFinite (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let := Fintype.ofFinite (L.toSubgroup ⧸ extensionSubgroup L M hML)
  let totalFintype : Fintype
      (K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK)) :=
    Fintype.ofEquiv
      ((K.toSubgroup ⧸ extensionSubgroup K L hLK) ×
        (L.toSubgroup ⧸ extensionSubgroup L M hML))
      (Subgroup.quotientTowerEquiv hML hLK).symm
  have htotalFintype : Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK)) = totalFintype :=
    Subsingleton.elim _ _
  have houter : ∀ q : K.toSubgroup ⧸ extensionSubgroup K L hLK,
      relativeCosetAction A K L hLK (relativeNorm A L M hML a) q =
        A.ρ (Quotient.out q).1 (relativeNormValue A L M hML a) := by
    intro q
    calc
      relativeCosetAction A K L hLK (relativeNorm A L M hML a) q =
          relativeCosetAction A K L hLK (relativeNorm A L M hML a)
            (QuotientGroup.mk (Quotient.out q)) := by
              exact congrArg
                (relativeCosetAction A K L hLK (relativeNorm A L M hML a))
                (Quotient.out_eq' q).symm
      _ = A.ρ (Quotient.out q).1
          ((relativeNorm A L M hML a : ambientFixedAddSubgroup A L) : A.V) :=
        relativeCosetAction_mk A K L hLK (relativeNorm A L M hML a)
          (Quotient.out q)
      _ = A.ρ (Quotient.out q).1 (relativeNormValue A L M hML a) := by
        rw [relativeNorm_apply_coe]
  simp only [relativeNorm_apply_coe, relativeNormValue]
  rw [htotalFintype]
  rw [Finset.sum_congr rfl (fun q _ ↦ houter q)]
  simp only [relativeNormValue]
  simp_rw [map_sum]
  rw [← Fintype.sum_prod_type (f := fun p :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ×
      (L.toSubgroup ⧸ extensionSubgroup L M hML) ↦
        A.ρ (Quotient.out p.1).1
          (relativeCosetAction A L M hML a p.2))]
  calc
    ∑ p : (K.toSubgroup ⧸ extensionSubgroup K L hLK) ×
        (L.toSubgroup ⧸ extensionSubgroup L M hML),
        A.ρ (Quotient.out p.1).1 (relativeCosetAction A L M hML a p.2) =
      ∑ p, relativeCosetAction A K M (hML.trans hLK) a
        ((Subgroup.quotientTowerEquiv hML hLK).symm p) := by
          apply Fintype.sum_congr
          intro p
          exact (relativeCosetAction_towerProductEquiv A K L M hML hLK a p.1 p.2).symm
    _ = ∑ q, relativeCosetAction A K M (hML.trans hLK) a q :=
      (Subgroup.quotientTowerEquiv hML hLK).symm.sum_comp
        (relativeCosetAction A K M (hML.trans hLK) a)

namespace DegreeData.FiniteTower

variable (T : DegreeData.FiniteTower G)

/-- Relative norms are transitive along a finite tower.  All containments and
finite quotient witnesses are obtained from `T`. -/
theorem norm_trans_apply (A : Rep ℤ G)
    (a : ambientFixedAddSubgroup A T.top) :
    relativeNorm A T.base T.middle T.middle_le_base
        (relativeNorm A T.middle T.top T.top_le_middle a) =
      relativeNorm A T.base T.top
        (T.top_le_middle.trans T.middle_le_base) a := by
  exact finiteTowerNormTransApplyAux A T.base T.middle T.top
    T.top_le_middle T.middle_le_base a

end DegreeData.FiniteTower

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_NormConjugation
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# Conjugation and relative norms

These are the field-conjugation and norm identities used in the abstract reciprocity construction and theorem.  They belong before the reciprocity construction: their proofs
use only the actual relative norm and the conjugation action.
-/

noncomputable section

open scoped BigOperators

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Conjugation preserves inclusions of abstract fields. -/
theorem conjugateClosedSubgroup_mono [ContinuousMul G]
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (s : G) :
    (conjugateClosedSubgroup L s).toSubgroup ≤
      (conjugateClosedSubgroup K s).toSubgroup := by
  intro x hx
  change x ∈ conjugateClosedSubgroup L s at hx
  change x ∈ conjugateClosedSubgroup K s
  rw [conjugateClosedSubgroup_mem] at hx ⊢
  exact hLK hx

/-- Conjugation by `s⁻¹` identifies a field subgroup with the subgroup
representing its right conjugate `K^s`. -/
def conjugateSubgroupEquiv [ContinuousMul G]
    (K : ClosedSubgroup G) (s : G) :
    K.toSubgroup ≃* (conjugateClosedSubgroup K s).toSubgroup where
  toFun k := ⟨s⁻¹ * k.1 * s, by
    change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup K s
    rw [conjugateClosedSubgroup_mem]
    convert k.2 using 1
    all_goals try with_reducible_and_instances rfl
    simp [mul_assoc]⟩
  invFun x := ⟨s * x.1 * s⁻¹,
    (conjugateClosedSubgroup_mem K s x.1).mp x.2⟩
  left_inv k := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

/-- Establishes the identity `(conjugateSubgroupEquiv K s k).1 = s⁻¹ * k.1 * s`. -/
@[simp]
theorem conjugateSubgroupEquiv_apply_coe [ContinuousMul G]
    (K : ClosedSubgroup G) (s : G) (k : K.toSubgroup) :
    (conjugateSubgroupEquiv K s k).1 = s⁻¹ * k.1 * s :=
  rfl

/-- Conjugation carries the subgroup for `L/K` exactly to the subgroup for
`L^s/K^s`. -/
theorem map_extensionSubgroup_conjugate [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G) :
    (extensionSubgroup K L hLK).map
        (conjugateSubgroupEquiv K s).toMonoidHom =
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup L s
    rw [conjugateClosedSubgroup_mem]
    simpa [mul_assoc] using hk
  · intro hx
    refine ⟨(conjugateSubgroupEquiv K s).symm x, ?_, ?_⟩
    · change s * x.1 * s⁻¹ ∈ L.toSubgroup
      exact (conjugateClosedSubgroup_mem L s x.1).mp hx
    · exact (conjugateSubgroupEquiv K s).apply_symm_apply x

/-- Conjugation identifies the relative coset spaces even when the
extension is not normal. -/
noncomputable def relativeConjugateCosetEquiv [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G) :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
  Quotient.congr (conjugateSubgroupEquiv K s).toEquiv (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    let e := conjugateSubgroupEquiv K s
    let H := extensionSubgroup K L hLK
    let Hs := extensionSubgroup (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)
    have hmap : H.map e.toMonoidHom = Hs :=
      map_extensionSubgroup_conjugate K L hLK s
    change x⁻¹ * y ∈ H ↔ (e x)⁻¹ * e y ∈ Hs
    rw [← hmap]
    constructor
    · intro hxy
      refine ⟨x⁻¹ * y, hxy, ?_⟩
      simp
    · rintro ⟨z, hz, hez⟩
      have heq : z = x⁻¹ * y := by
        apply e.injective
        simpa using hez
      simpa [heq] using hz)

/--
Establishes the identity `relativeConjugateCosetEquiv K L hLK s (QuotientGroup.mk k) =
QuotientGroup.mk (conjugateSubgroupEquiv K s k)`.
-/
@[simp]
theorem relativeConjugateCosetEquiv_mk [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    (k : K.toSubgroup) :
    relativeConjugateCosetEquiv K L hLK s (QuotientGroup.mk k) =
      QuotientGroup.mk (conjugateSubgroupEquiv K s k) :=
  rfl

/-- A conjugate of a Galois extension is Galois. -/
instance conjugateExtension_normal [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (extensionSubgroup (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)).Normal := by
  rw [← map_extensionSubgroup_conjugate K L hLK s]
  exact Subgroup.Normal.map hLnormal
    (conjugateSubgroupEquiv K s).toMonoidHom
    (conjugateSubgroupEquiv K s).surjective

/-- The left vertical isomorphism in the conjugation diagram of
norm--conjugation naturality, `τ ↦ s⁻¹τs`. -/
noncomputable def finiteReciprocityNaturalityConjugation
    [ContinuousMul G] (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃*
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
  QuotientGroup.congr
    (extensionSubgroup K L hLK)
    (extensionSubgroup (conjugateClosedSubgroup K s)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s))
    (conjugateSubgroupEquiv K s)
    (map_extensionSubgroup_conjugate K L hLK s)

/--
Establishes the identity `finiteReciprocityNaturalityConjugation K L hLK s (QuotientGroup.mk k) =
QuotientGroup.mk (conjugateSubgroupEquiv K s k)`.
-/
@[simp]
theorem finiteReciprocityNaturalityConjugation_mk [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) :
    finiteReciprocityNaturalityConjugation K L hLK s (QuotientGroup.mk k) =
      QuotientGroup.mk (conjugateSubgroupEquiv K s k) := by
  exact QuotientGroup.congr_mk' _ _ _ _ k

/-- Conjugation preserves finiteness of the Galois quotient. -/
theorem finite_conjugateExtension [ContinuousMul G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      extensionSubgroup (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)) :=
  Finite.of_equiv
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (relativeConjugateCosetEquiv K L hLK s)

end GroupOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Conjugation intertwines the two relative coset actions. -/
theorem relativeCosetAction_conjugate
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    (a : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A L s a)
        (relativeConjugateCosetEquiv K L hLK s q) =
      A.ρ s⁻¹ (relativeCosetAction A K L hLK a q) := by
  refine Quotient.inductionOn' q ?_
  intro k
  rw [relativeConjugateCosetEquiv_mk, relativeCosetAction_mk,
    relativeCosetAction_mk, conjugateFixedElement_coe]
  calc
    A.ρ (s⁻¹ * k.1 * s) (A.ρ s⁻¹ a.1) =
        A.ρ ((s⁻¹ * k.1 * s) * s⁻¹) a.1 := by
      have hm := congrArg (fun φ => φ a.1)
        (map_mul A.ρ (s⁻¹ * k.1 * s) s⁻¹)
      exact hm.symm
    _ = A.ρ (s⁻¹ * k.1) a.1 := by
      congr 2
      simp [mul_assoc]
    _ = A.ρ s⁻¹ (A.ρ k.1 a.1) := by
      exact congrArg (fun φ => φ a.1) (map_mul A.ρ s⁻¹ k.1)

/-- Relative norms commute with the right conjugation used in the second
diagram of norm--conjugation naturality:
`N_{L^s/K^s}(a^s) = N_{L/K}(a)^s`. -/
theorem relativeNorm_conjugate_apply
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A L) :
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
      finite_conjugateExtension K L hLK s
    relativeNorm A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A L s a) =
      conjugateFixedElement A K s (relativeNorm A K L hLK a) := by
  let hConj := conjugateClosedSubgroup_mono hLK s
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let e := relativeConjugateCosetEquiv K L hLK s
  let conjugateFintype : Fintype
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConj) :=
    Fintype.ofEquiv (K.toSubgroup ⧸ extensionSubgroup K L hLK) e
  have hconjugateFintype : Fintype.ofFinite
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        extensionSubgroup (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConj) = conjugateFintype :=
    Subsingleton.elim _ _
  apply Subtype.ext
  simp only [relativeNorm_apply_coe, relativeNormValue,
    conjugateFixedElement_coe]
  rw [hconjugateFintype]
  calc
    ∑ q, relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConj
        (conjugateFixedElement A L s a) q =
      ∑ q, relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConj
        (conjugateFixedElement A L s a) (e q) := by
          exact (e.sum_comp fun q =>
            relativeCosetAction A (conjugateClosedSubgroup K s)
              (conjugateClosedSubgroup L s) hConj
              (conjugateFixedElement A L s a) q).symm
    _ = ∑ q, A.ρ s⁻¹ (relativeCosetAction A K L hLK a q) := by
      apply Finset.sum_congr rfl
      intro q _
      exact relativeCosetAction_conjugate A K L hLK s a q
    _ = A.ρ s⁻¹ (∑ q, relativeCosetAction A K L hLK a q) := by
      rw [map_sum]

end Representation

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_ValuationLaws
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.conjugateExtension_normal
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.conjugateSubgroupEquiv_apply_coe _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# normalized degree and Frobenius theory: functoriality of normalized valuations

This file proves the two functorial assertions of normalized-valuation functoriality from the
source norm laws.
-/

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- Conjugating an abstract field does not change its degree image. -/
theorem DegreeData.fieldImage_conjugate
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (D : DegreeData G) (K : ClosedSubgroup G) (σ : G) :
    D.fieldImage (conjugateClosedSubgroup K σ) = D.fieldImage K := by
  rw [D.fieldImage_eq_map, D.fieldImage_eq_map]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    let k : K.toSubgroup :=
      ⟨σ * x * σ⁻¹, (conjugateClosedSubgroup_mem K σ x).mp hx⟩
    refine ⟨k.1, k.2, ?_⟩
    simp [k, map_mul, mul_assoc]
  · rintro ⟨k, hk, rfl⟩
    let x : G := σ⁻¹ * k * σ
    have hx : x ∈ conjugateClosedSubgroup K σ := by
      rw [conjugateClosedSubgroup_mem]
      change σ * x * σ⁻¹ ∈ K.toSubgroup
      simpa [x, mul_assoc] using hk
    refine ⟨x, hx, ?_⟩
    simp [x, map_mul, mul_assoc, mul_comm]

/-- Conjugate a field whose actual absolute residue quotient is finite.
The transported field remains in the same residue-finite boundary because
conjugation does not change the degree image. -/
noncomputable def DegreeData.FiniteResidueAbstractField.conjugate
    {G : Type*} [Group G] [TopologicalSpace G] {D : DegreeData G}
    [ContinuousMul G] (K : DegreeData.FiniteResidueAbstractField D) (σ : G) :
    DegreeData.FiniteResidueAbstractField D where
  field := conjugateClosedSubgroup K.field σ
  finiteResidueQuotient := by
    unfold DegreeData.residueQuotient
    rw [D.fieldImage_conjugate K.field σ]
    exact K.finiteResidueQuotient

/-- Conjugation preserves the positive absolute residue degree at the
residue-finite boundary. -/
theorem DegreeData.FiniteResidueAbstractField.residueDegree_conjugate
    {G : Type*} [Group G] [TopologicalSpace G] {D : DegreeData G}
    [ContinuousMul G] (K : DegreeData.FiniteResidueAbstractField D) (σ : G) :
    (K.conjugate σ).residueDegree = K.residueDegree := by
  apply PNat.eq
  change Nat.card
      (D.residueQuotient (conjugateClosedSubgroup K.field σ)) =
    Nat.card (D.residueQuotient K.field)
  unfold DegreeData.residueQuotient
  have himage := D.fieldImage_conjugate K.field σ
  apply Nat.card_congr
  exact Subgroup.quotientEquivOfEq
    (congrArg
      (fun H : Subgroup ZHatMul => H.subgroupOf (⊤ : Subgroup ZHatMul))
      himage)

/-- Conjugate a finite abstract field without separating the transported
finiteness proof from the field. -/
noncomputable def FiniteAbstractField.conjugate
    {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (K : FiniteAbstractField G) (σ : G) :
    FiniteAbstractField G where
  field := conjugateClosedSubgroup K.field σ
  finite := Finite.of_equiv
    ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K.field (le_baseField K.field))
    (absoluteConjugateCosetEquiv K.field σ).symm

/-- Conjugation preserves the positive absolute residue degree. -/
theorem FiniteAbstractField.residueDegree_conjugate
    {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (K : FiniteAbstractField G)
    (D : DegreeData G) (σ : G) :
    (K.conjugate σ).residueDegree D = K.residueDegree D := by
  apply PNat.eq
  change Nat.card
      (D.residueQuotient (conjugateClosedSubgroup K.field σ)) =
    Nat.card (D.residueQuotient K.field)
  unfold DegreeData.residueQuotient
  have himage := D.fieldImage_conjugate K.field σ
  apply Nat.card_congr
  exact Subgroup.quotientEquivOfEq
    (congrArg
      (fun H : Subgroup ZHatMul => H.subgroupOf (⊤ : Subgroup ZHatMul))
      himage)

namespace ValuationData

/-- **conjugation compatibility of normalized valuations.** The normalized valuations are compatible with
conjugation: `v_{K^σ}(a^σ) = v_K(a)` (the right-action notation). -/
theorem normalizedValuation_conjugate [ContinuousMul G]
    (v : ValuationData D A) (K : FiniteAbstractField G) (σ : G)
    (a : ambientFixedAddSubgroup A K.field) :
    v.valuationAt (K.conjugate σ)
        (conjugateFixedElement A K.field σ a) =
      v.valuationAt K a := by
  let : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) (conjugateClosedSubgroup K.field σ)
        (le_baseField (conjugateClosedSubgroup K.field σ))) :=
    (K.conjugate σ).finite
  apply Subtype.ext
  apply zHatMulNat_injective (K.residueDegree D).property
  calc
    (K.residueDegree D : ℕ) •
        v.dividedAt (K.conjugate σ)
          (conjugateFixedElement A K.field σ a) =
      ((K.conjugate σ).residueDegree D : ℕ) •
        v.dividedAt (K.conjugate σ)
          (conjugateFixedElement A K.field σ a) := by
            rw [K.residueDegree_conjugate D σ]
    _ = v.normCompositeAt (K.conjugate σ)
        (conjugateFixedElement A K.field σ a) :=
      v.residueDegree_nsmul_dividedAt (K.conjugate σ) _
    _ = v.normCompositeAt K a := by
      change v.toAddMonoidHom
          (normToBase A (conjugateClosedSubgroup K.field σ)
            (conjugateFixedElement A K.field σ a)) =
        v.toAddMonoidHom (normToBase A K.field a)
      congr 1
      apply Subtype.ext
      calc
        ((normToBase A (conjugateClosedSubgroup K.field σ)
            (conjugateFixedElement A K.field σ a) :
              ambientFixedAddSubgroup A (baseField G)) : A.V) =
          A.ρ σ⁻¹
            ((normToBase A K.field a :
              ambientFixedAddSubgroup A (baseField G)) : A.V) := by
                simpa [normToBase] using
                  (relativeNorm_absoluteConjugate_apply A K.field σ a)
        _ = ((normToBase A K.field a :
              ambientFixedAddSubgroup A (baseField G)) : A.V) := by
                exact (normToBase A K.field a).2 ⟨σ⁻¹, trivial⟩
    _ = (K.residueDegree D : ℕ) • v.dividedAt K a :=
      (v.residueDegree_nsmul_dividedAt K a).symm

/-- **the norm--valuation formula.** For a finite tower `L | K`,
`v_K ∘ N_{L|K} = f_{L|K} v_L`. -/
theorem normalizedValuation_tower (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (a : ambientFixedAddSubgroup A E.field.field) :
    let ER := E.toFiniteResidueAbstractExtension D
    (ER.residueDegree : ℕ) •
        ((v.valuationAt E.field a : v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below a) : v.valueGroup) : ZHat) := by
  let ER := E.toFiniteResidueAbstractExtension D
  apply zHatMulNat_injective (E.base.residueDegree D).property
  change (ER.base.residueDegree : ℕ) •
      ((ER.residueDegree : ℕ) • v.dividedAt E.field a) =
    (ER.base.residueDegree : ℕ) •
      v.dividedAt E.base
        (relativeNorm A E.base.field E.field.field E.below a)
  rw [smul_smul, Nat.mul_comm (ER.base.residueDegree : ℕ),
    ER.residueDegree_mul_absoluteResidueDegree D]
  change (E.field.residueDegree D : ℕ) • v.dividedAt E.field a =
    (E.base.residueDegree D : ℕ) •
      v.dividedAt E.base
        (relativeNorm A E.base.field E.field.field E.below a)
  rw [v.residueDegree_nsmul_dividedAt E.field,
    v.residueDegree_nsmul_dividedAt E.base]
  change v.toAddMonoidHom (normToBase A E.field.field a) =
    v.toAddMonoidHom
      (normToBase A E.base.field
        (relativeNorm A E.base.field E.field.field E.below a))
  let T : DegreeData.FiniteTower G := {
    top := E.field.field
    middle := E.base.field
    base := baseField G
    top_le_middle := E.below
    middle_le_base := le_baseField E.base.field
    finiteTopQuotient := E.finiteQuotient
    finiteBaseQuotient := E.base.finite }
  exact congrArg v.toAddMonoidHom
    (by simpa [T, normToBase] using (T.norm_trans_apply A a).symm)

end ValuationData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_PrimeElements
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.conjugateExtension_normal
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# normalized degree and Frobenius theory: prime elements and units

This file formalizes the prime-element definition and its two immediate consequences for
unramified and totally ramified extensions.
-/

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- Inclusion `A_K → A_L` for an extension `L | K`. -/
def fixedFieldInclusion (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    ambientFixedAddSubgroup A K →+ ambientFixedAddSubgroup A L where
  toFun a := ⟨a.1, fun l => a.2 ⟨l.1, hLK l.2⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/--
Establishes the identity `((fixedFieldInclusion A K L hLK a : ambientFixedAddSubgroup A L) : A.V)
= a.1`.
-/
@[simp]
theorem fixedFieldInclusion_coe (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A K) :
    ((fixedFieldInclusion A K L hLK a : ambientFixedAddSubgroup A L) : A.V) = a.1 :=
  rfl

/-- The norm of an element already fixed over `K` is its `[L:K]`-fold sum. -/
theorem relativeNorm_fixedFieldInclusion
    (A : Rep ℤ G) (E : DegreeData.FiniteAbstractExtension G)
    (a : ambientFixedAddSubgroup A E.base) :
    relativeNorm A E.base E.field E.below
        (fixedFieldInclusion A E.base E.field E.below a) =
      (E.degree : ℕ) • a := by
  apply Subtype.ext
  let := Fintype.ofFinite
    (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below)
  have hterm : ∀ q : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below,
      relativeCosetAction A E.base E.field E.below
        (fixedFieldInclusion A E.base E.field E.below a) q = a.1 := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro k
    rw [relativeCosetAction_mk, fixedFieldInclusion_coe]
    exact a.2 k
  simp only [relativeNorm_apply_coe, relativeNormValue]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ]
  change Fintype.card
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) • a.1 =
    (E.degree : ℕ) • a.1
  rw [← E.extensionSubgroup_index_eq_degree,
    Subgroup.index, Nat.card_eq_fintype_card]

/-- The norm of the trivial extension is the identity. -/
@[simp]
theorem relativeNorm_self
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K K le_rfl)]
    (a : ambientFixedAddSubgroup A K) :
    relativeNorm A K K le_rfl a = a := by
  apply Subtype.ext
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K K le_rfl)
  have hterm : ∀ q : K.toSubgroup ⧸ extensionSubgroup K K le_rfl,
      relativeCosetAction A K K le_rfl a q = a.1 := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro k
    rw [relativeCosetAction_mk]
    exact a.2 k
  simp only [relativeNorm_apply_coe, relativeNormValue]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ]
  have htop : extensionSubgroup K K le_rfl = ⊤ := by
    change K.toSubgroup.subgroupOf K.toSubgroup = ⊤
    exact Subgroup.subgroupOf_self _
  have hcard :
      Fintype.card (K.toSubgroup ⧸ extensionSubgroup K K le_rfl) = 1 := by
    rw [← Nat.card_eq_fintype_card,
      ← Subgroup.index_eq_card (extensionSubgroup K K le_rfl),
      htop, Subgroup.index_top]
  rw [hcard, one_nsmul]

namespace ValuationData

/-- The value `1` belongs to `Z`, by the valuation-quotient axiom. -/
def oneValue (v : ValuationData D A) : v.valueGroup :=
  ⟨1, by
    obtain ⟨a, ha⟩ := v.integers_mem 1
    exact ⟨a, by simpa using ha⟩⟩

/-- Establishes the identity `(v.oneValue : ZHat) = 1`. -/
@[simp]
theorem oneValue_coe (v : ValuationData D A) :
    (v.oneValue : ZHat) = 1 :=
  rfl

/-- **the prime-element definition.** A prime element has normalized value `1`. -/
def IsPrimeElement (v : ValuationData D A) (K : FiniteAbstractField G)
    (π : ambientFixedAddSubgroup A K.field) : Prop :=
  v.valuationAt K π = v.oneValue

/-- **the prime-element definition.** The additive form of the unit group
`U_K = {u | v_K(u)=0}`. -/
def unitAddSubgroup (v : ValuationData D A) (K : FiniteAbstractField G) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) :=
  (v.valuationAt K).ker

/-- Characterizes `u ∈ v.unitAddSubgroup K` by the equivalent condition `v.valuationAt K u = 0`. -/
@[simp]
theorem mem_unitAddSubgroup_iff (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (u : ambientFixedAddSubgroup A K.field) :
    u ∈ v.unitAddSubgroup K ↔ v.valuationAt K u = 0 :=
  Iff.rfl

/-- Over an unramified extension, the normalized valuation restricts to the
valuation below. -/
theorem valuationAt_fixedFieldInclusion_of_unramified
    (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hUn : E.IsUnramified D)
    (a : ambientFixedAddSubgroup A E.base.field) :
    v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below a) =
      v.valuationAt E.base a := by
  let EF := E.toFiniteAbstractExtension
  have hfeq : (E.residueDegree D : ℕ) = (E.degree : ℕ) :=
    E.residueDegree_eq_degree_of_isUnramified D hUn
  apply Subtype.ext
  apply zHatMulNat_injective (E.residueDegree D).property
  calc
    (E.residueDegree D : ℕ) •
        ((v.valuationAt E.field
          (fixedFieldInclusion A E.base.field E.field.field E.below a) :
          v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below
          (fixedFieldInclusion A E.base.field E.field.field E.below a)) :
          v.valueGroup) : ZHat) :=
        v.normalizedValuation_tower E
          (fixedFieldInclusion A E.base.field E.field.field E.below a)
    _ = ((v.valuationAt E.base ((E.degree : ℕ) • a) :
          v.valueGroup) : ZHat) := by
        rw [show relativeNorm A E.base.field E.field.field E.below
            (fixedFieldInclusion A E.base.field E.field.field E.below a) =
              (E.degree : ℕ) • a by
          simpa [EF, FiniteAbstractFieldExtension.toFiniteAbstractExtension,
              FiniteAbstractFieldExtension.degree] using
                relativeNorm_fixedFieldInclusion A EF a]
    _ = (E.degree : ℕ) •
        ((v.valuationAt E.base a : v.valueGroup) : ZHat) := by
          exact congrArg Subtype.val
            (map_nsmul (v.valuationAt E.base) (E.degree : ℕ) a)
    _ = (E.residueDegree D : ℕ) •
        ((v.valuationAt E.base a : v.valueGroup) : ZHat) := by
          rw [hfeq]

/-- A prime element remains prime in an unramified extension. -/
theorem prime_of_unramified (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hUn : E.IsUnramified D)
    (π : ambientFixedAddSubgroup A E.base.field)
    (hπ : v.IsPrimeElement E.base π) :
    v.IsPrimeElement E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below π) := by
  rw [IsPrimeElement,
    v.valuationAt_fixedFieldInclusion_of_unramified E hUn π]
  exact hπ

/-- The norm of a prime element is prime in a totally ramified extension. -/
theorem norm_prime_of_totallyRamified (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (π : ambientFixedAddSubgroup A E.field.field) :
    v.IsPrimeElement E.field π →
      v.IsPrimeElement E.base
        (relativeNorm A E.base.field E.field.field E.below π) := by
  intro hπ
  have htower := v.normalizedValuation_tower E π
  have hresidue : (E.residueDegree D : ℕ) = 1 :=
    E.toFiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified D hTot
  change (E.residueDegree D : ℕ) •
      ((v.valuationAt E.field π : v.valueGroup) : ZHat) =
    ((v.valuationAt E.base
      (relativeNorm A E.base.field E.field.field E.below π) :
        v.valueGroup) : ZHat) at htower
  rw [hresidue, one_nsmul] at htower
  rw [IsPrimeElement] at hπ ⊢
  apply Subtype.ext
  exact htower.symm.trans (congrArg Subtype.val hπ)

end ValuationData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_UnitCohomologyAxiom
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.conjugateExtension_normal
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.relativeConjugateCosetEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- A finite cyclic extension of a bundled finite abstract field.  The
generator and its cyclicity proof travel with the finite normal extension. -/
structure FiniteCyclicSubextension (K : FiniteAbstractField G) where
  /-- The closed subgroup representing the top field. -/
  field : ClosedSubgroup G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.toSubgroup ≤ K.field.toSubgroup
  /-- The top-field subgroup is normal inside the base-field subgroup. -/
  normal : (extensionSubgroup K.field field below).Normal
  /-- The relative Galois quotient is finite. -/
  finite : Finite (K.field.toSubgroup ⧸
    extensionSubgroup K.field field below)
  /-- A chosen generator of the relative Galois quotient. -/
  generator : K.field.toSubgroup ⧸ extensionSubgroup K.field field below
  /-- Every quotient element is a power of the chosen generator. -/
  generates : ∀ x, x ∈ Subgroup.zpowers generator

namespace FiniteCyclicSubextension

variable {K : FiniteAbstractField G}

/-- Forget the cyclic generator and normality, retaining the underlying finite
abstract extension. -/
@[implicit_reducible]
def toFiniteAbstractExtension (E : FiniteCyclicSubextension K) :
    DegreeData.FiniteAbstractExtension G where
  field := E.field
  base := K.field
  below := E.below
  finiteQuotient := E.finite

/-- Structural unramifiedness of the underlying finite extension. -/
def IsUnramified (E : FiniteCyclicSubextension K) (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsUnramified D

/-- Retain the finite-over-base endpoint bundles as well as the relative
finite quotient. -/
@[implicit_reducible]
noncomputable def toFiniteAbstractFieldExtension
    (E : FiniteCyclicSubextension K) : FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
    E.finite
  exact FiniteAbstractFieldExtension.ofInclusion E.field K E.below

/-- A finite cyclic subextension supplies normality of its representing subgroup. -/
instance instNormalSubtypeMemSubgroupFieldExtensionSubgroupField (E : FiniteCyclicSubextension K) :
    (extensionSubgroup K.field E.field E.below).Normal :=
  E.normal

/-- A finite cyclic subextension supplies finiteness of its Galois quotient. -/
instance instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField (E : FiniteCyclicSubextension K) :
    Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  E.finite

/-- The finite quotient of a cyclic subextension carries its canonical `Fintype`. -/
noncomputable instance instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField (E : FiniteCyclicSubextension K) :
    Fintype (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  Fintype.ofFinite _

end FiniteCyclicSubextension

end Generic

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- A finite cyclic extension together with the assertion that it is
unramified for the fixed degree datum. -/
structure FiniteUnramifiedCyclicExtension
    (D : DegreeData G) (K : FiniteAbstractField G)
    extends FiniteCyclicSubextension K where
  /-- The underlying finite cyclic extension is unramified for `D`. -/
  unramified : toFiniteCyclicSubextension.IsUnramified D

namespace FiniteUnramifiedCyclicExtension

variable {K : FiniteAbstractField G}

/-- Forget cyclic and unramified structure while retaining both finite
endpoint fields and the relative finite quotient. -/
@[implicit_reducible]
noncomputable def toFiniteAbstractFieldExtension
    (E : FiniteUnramifiedCyclicExtension D K) :
    FiniteAbstractFieldExtension G :=
  E.toFiniteCyclicSubextension.toFiniteAbstractFieldExtension

/-- The unramified proof transported to the canonical finite field-extension
bundle. -/
theorem toFiniteAbstractFieldExtension_isUnramified
    (E : FiniteUnramifiedCyclicExtension D K) :
    E.toFiniteAbstractFieldExtension.IsUnramified D := by
  exact E.unramified

/-- A finite unramified cyclic extension supplies normality of its representing subgroup. -/
instance instNormalSubtypeMemSubgroupFieldExtensionSubgroupField (E : FiniteUnramifiedCyclicExtension D K) :
    (extensionSubgroup K.field E.field E.below).Normal :=
  E.normal

/-- The quotient over `K` attached to a finite unramified cyclic extension is finite. -/
instance instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField (E : FiniteUnramifiedCyclicExtension D K) :
    Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  E.finite

/-- The finite quotient over `K` carries the canonical `Fintype` structure. -/
noncomputable instance instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField (E : FiniteUnramifiedCyclicExtension D K) :
    Fintype (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  Fintype.ofFinite _

end FiniteUnramifiedCyclicExtension

namespace FiniteCyclicSubextension

variable {K : FiniteAbstractField G}

/-- The fixed coefficient representation attached to a bundled cyclic
extension. -/
noncomputable def fixedRepresentation (E : FiniteCyclicSubextension K)
    (A : Rep ℤ G) :
    Rep ℤ (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  extensionFixedRepresentation A K.field E.field E.below E.normal

end FiniteCyclicSubextension

/-- Elementwise content of `H⁰(Q,M)=0`: every element fixed by a cyclic
generator is an actual norm. -/
theorem exists_norm_eq_of_tateHZero_isZero
    {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (M : Rep ℤ Q) (g : Q) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hzero : Limits.IsZero (tateCohomology M 0)) :
    ∀ x : M.V, M.ρ g x = x → ∃ y : M.V, M.norm.hom y = x := by
  let : IsCyclic Q := isCyclic_of_generator g hg
  let : CommGroup Q := IsCyclic.commGroup (α := Q)
  let S := Rep.FiniteCyclicGroup.normHomCompSub M g
  have hSzero : Limits.IsZero S.homology := by
    exact Limits.IsZero.of_iso hzero
      (TateCohomology.isoFiniteCyclicZero M g hg).symm
  have hS : S.Exact := (S.exact_iff_isZero_homology).2 hSzero
  intro x hx
  have hxker : S.g x = 0 := by
    change M.ρ g x - x = 0
    exact sub_eq_zero.mpr hx
  rcases (S.moduleCat_exact_iff.mp hS x hxker) with ⟨y, hy⟩
  exact ⟨y, hy⟩

namespace ValuationData

/-- Normalized valuation is invariant under the Galois action in a finite
tower.  The proof uses transitivity of the actual norm and its invariance
under the normal-extension action. -/
theorem valuationAt_normalExtensionAction
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (k : E.base.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E.field.field) :
    v.valuationAt E.field
        (normalExtensionAction A E.base.field E.field.field E.below
          hnormal k a) =
      v.valuationAt E.field a := by
  apply Subtype.ext
  apply zHatMulNat_injective (E.field.residueDegree D).property
  calc
    (E.field.residueDegree D : ℕ) •
        ((v.valuationAt E.field
          (normalExtensionAction A E.base.field E.field.field E.below
            hnormal k a) : v.valueGroup) : ZHat) =
      v.normCompositeAt E.field
        (normalExtensionAction A E.base.field E.field.field E.below
          hnormal k a) :=
        v.residueDegree_nsmul_dividedAt E.field _
    _ = v.normCompositeAt E.field a := by
      change v.toAddMonoidHom
          (normToBase A E.field.field
            (normalExtensionAction A E.base.field E.field.field E.below
              hnormal k a)) =
        v.toAddMonoidHom (normToBase A E.field.field a)
      congr 1
      let T : DegreeData.FiniteTower G := {
        top := E.field.field
        middle := E.base.field
        base := baseField G
        top_le_middle := E.below
        middle_le_base := le_baseField E.base.field
        finiteTopQuotient := E.finiteQuotient
        finiteBaseQuotient := E.base.finite }
      calc
        relativeNorm A (baseField G) E.field.field
            (E.below.trans (le_baseField E.base.field))
            (normalExtensionAction A E.base.field E.field.field E.below
              hnormal k a) =
          relativeNorm A (baseField G) E.base.field
            (le_baseField E.base.field)
            (relativeNorm A E.base.field E.field.field E.below
              (normalExtensionAction A E.base.field E.field.field E.below
                hnormal k a)) :=
          (T.norm_trans_apply A _).symm
        _ = relativeNorm A (baseField G) E.base.field
            (le_baseField E.base.field)
            (relativeNorm A E.base.field E.field.field E.below a) := by
          rw [relativeNorm_normalExtensionAction A E.base.field E.field.field
            E.below hnormal k a]
        _ = relativeNorm A (baseField G) E.field.field
            (E.below.trans (le_baseField E.base.field)) a :=
          T.norm_trans_apply A a
    _ = (E.field.residueDegree D : ℕ) •
        ((v.valuationAt E.field a : v.valueGroup) : ZHat) :=
      (v.residueDegree_nsmul_dividedAt E.field a).symm

/-- The action of `G_K` on the actual unit subgroup `U_L`. -/
noncomputable def unitActionLinearMap
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (k : E.base.field.toSubgroup) :
    v.unitAddSubgroup E.field →ₗ[ℤ] v.unitAddSubgroup E.field where
  toFun u := ⟨normalExtensionAction A E.base.field E.field.field E.below
      hnormal k u.1, by
    rw [mem_unitAddSubgroup_iff,
      v.valuationAt_normalExtensionAction E hnormal k u.1]
    exact u.2⟩
  map_add' u w := by
    apply Subtype.ext
    apply Subtype.ext
    change A.ρ k.1 (u.1.1 + w.1.1) = A.ρ k.1 u.1.1 + A.ρ k.1 w.1.1
    exact map_add (A.ρ k.1) _ _
  map_smul' n u := by
    apply Subtype.ext
    apply Subtype.ext
    change A.ρ k.1 (n • u.1.1) = n • A.ρ k.1 u.1.1
    exact map_zsmul (A.ρ k.1) n u.1.1

/-- The `G_K`-representation on `U_L` before descending through `G_L`. -/
noncomputable def unitRepresentationOverK
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal) :
    Rep ℤ E.base.field.toSubgroup :=
  Rep.of
    { toFun := fun k => v.unitActionLinearMap E hnormal k
      map_one' := by
        ext u
        change A.ρ (1 : G) u.1.1 = u.1.1
        simp
      map_mul' := by
        intro k₁ k₂
        ext u
        change A.ρ (k₁.1 * k₂.1) u.1.1 =
          A.ρ k₁.1 (A.ρ k₂.1 u.1.1)
        rw [map_mul]
        rfl }

theorem unitRepresentationOverK_isTrivialOnExtension
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal) :
    Representation.IsTrivial
      ((v.unitRepresentationOverK E hnormal).ρ.comp
        (extensionSubgroup E.base.field E.field.field E.below).subtype) := by
  constructor
  intro s
  ext u
  apply Subtype.ext
  apply Subtype.ext
  change A.ρ s.1.1 u.1.1 = u.1.1
  exact u.1.2
    ⟨s.1.1, (mem_extensionSubgroup_iff E.base.field E.field.field E.below s.1).1 s.2⟩

/-- The actual quotient representation on the unit group `U_L`. -/
noncomputable def unitRepresentation
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal) :
    Rep ℤ (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below) := by
  letI := hnormal
  letI : Representation.IsTrivial
      ((v.unitRepresentationOverK E hnormal).ρ.comp
        (extensionSubgroup E.base.field E.field.field E.below).subtype) :=
    v.unitRepresentationOverK_isTrivialOnExtension E hnormal
  exact (v.unitRepresentationOverK E hnormal).ofQuotient
    (extensionSubgroup E.base.field E.field.field E.below)

end ValuationData

namespace FiniteUnramifiedCyclicExtension

variable {K : FiniteAbstractField G}

/-- The unit representation carried by a bundled finite unramified cyclic
extension. -/
noncomputable def unitRepresentation
    (E : FiniteUnramifiedCyclicExtension D K) (v : ValuationData D A) :
    Rep ℤ (K.field.toSubgroup ⧸ extensionSubgroup K.field E.field E.below) :=
  v.unitRepresentation E.toFiniteAbstractFieldExtension E.normal

end FiniteUnramifiedCyclicExtension

namespace ValuationData

/-- The quotient unit representation acts on a representative through the original unit action. -/
@[simp]
theorem unitRepresentation_quotient_mk_apply
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (k : E.base.field.toSubgroup) (u : v.unitAddSubgroup E.field) :
    (v.unitRepresentation E hnormal).ρ
        ((QuotientGroup.mk'
          (extensionSubgroup E.base.field E.field.field E.below)) k) u =
      v.unitActionLinearMap E hnormal k u :=
  rfl

/-- Inclusion of units along an unramified finite extension. -/
def unitInclusion
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hUnramified : E.IsUnramified D) :
    v.unitAddSubgroup E.base →+ v.unitAddSubgroup E.field where
  toFun u := ⟨fixedFieldInclusion A E.base.field E.field.field E.below u.1, by
    rw [mem_unitAddSubgroup_iff]
    exact (v.valuationAt_fixedFieldInclusion_of_unramified E hUnramified u.1).trans
      u.2⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl

/-- On underlying coefficients, the quotient action on `U_L` is the same
coset action used in the relative norm. -/
theorem unitRepresentation_action_coe
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (q : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (u : v.unitAddSubgroup E.field) :
    (((v.unitRepresentation E hnormal).ρ q u).1 :
        ambientFixedAddSubgroup A E.field.field).1 =
      relativeCosetAction A E.base.field E.field.field E.below u.1 q := by
  refine Quotient.inductionOn' q ?_
  intro k
  rw [relativeCosetAction_mk]
  rfl

/-- The representation norm on `U_L` is the relative field norm on
underlying coefficients. -/
theorem unitRepresentation_norm_coe
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (u : v.unitAddSubgroup E.field) :
    letI := Fintype.ofFinite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below)
    ((((v.unitRepresentation E hnormal).norm.hom u).1 :
        ambientFixedAddSubgroup A E.field.field) : A.V) =
      ((relativeNorm A E.base.field E.field.field E.below u.1 :
        ambientFixedAddSubgroup A E.base.field) : A.V) := by
  let := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
  rw [relativeNorm_apply_coe]
  change
    (((Representation.norm (v.unitRepresentation E hnormal).ρ) u).1 :
      ambientFixedAddSubgroup A E.field.field).1 =
      relativeNormValue A E.base.field E.field.field E.below u.1
  rw [Representation.norm, relativeNormValue]
  let coeToAmbient : v.unitAddSubgroup E.field →+ A.V :=
    (ambientFixedAddSubgroup A E.field.field).subtype.comp
      (v.unitAddSubgroup E.field).subtype
  change coeToAmbient
      ((∑ q, (v.unitRepresentation E hnormal).ρ q) u) =
    ∑ q, relativeCosetAction A E.base.field E.field.field E.below u.1 q
  refine (congrArg coeToAmbient (LinearMap.sum_apply Finset.univ
    (fun q : E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below =>
      (v.unitRepresentation E hnormal).ρ q) u)).trans ?_
  refine (map_sum coeToAmbient _ _).trans ?_
  apply Finset.sum_congr rfl
  intro q _
  exact v.unitRepresentation_action_coe E hnormal q u

/-- Actual `H⁰=0` eliminator needed after the reciprocity construction: every unit of
`K` is the relative norm of a unit of an unramified Galois extension `L`. -/
theorem exists_unit_relativeNorm_eq_of_tateHZero_isZero
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (hUnramified : E.IsUnramified D)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := Fintype.ofFinite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below)
    Limits.IsZero
        (tateCohomology (v.unitRepresentation E hnormal) 0) →
      ∀ u : v.unitAddSubgroup E.base, ∃ ε : v.unitAddSubgroup E.field,
        relativeNorm A E.base.field E.field.field E.below ε.1 = u.1 := by
  let := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
  intro hzero u
  let U := v.unitRepresentation E hnormal
  let uL := v.unitInclusion E hUnramified u
  have hfixed : U.ρ g uL = uL := by
    refine Quotient.inductionOn' g ?_
    intro k
    apply Subtype.ext
    apply Subtype.ext
    change A.ρ k.1 u.1.1 = u.1.1
    exact u.1.2 k
  obtain ⟨ε, hε⟩ := exists_norm_eq_of_tateHZero_isZero
    U g hg hzero uL hfixed
  refine ⟨ε, ?_⟩
  apply Subtype.ext
  calc
    ((relativeNorm A E.base.field E.field.field E.below ε.1 :
        ambientFixedAddSubgroup A E.base.field) : A.V) =
        ((((v.unitRepresentation E hnormal).norm.hom ε).1 :
          ambientFixedAddSubgroup A E.field.field) : A.V) :=
      (v.unitRepresentation_norm_coe E hnormal ε).symm
    _ = ((uL.1 : ambientFixedAddSubgroup A E.field.field) : A.V) :=
      congrArg
        (fun z : v.unitAddSubgroup E.field =>
          ((z.1 : ambientFixedAddSubgroup A E.field.field) : A.V)) hε
    _ = u.1.1 := rfl

/-- Actual `H⁻¹=0` eliminator on units: a unit of relative norm zero is
in the image of `g-1`. -/
theorem exists_unit_sigma_sub_eq_of_tateHMinusOne_isZero
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := Fintype.ofFinite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below)
    Limits.IsZero
        (tateCohomology (v.unitRepresentation E hnormal) (-1)) →
      ∀ u : (v.unitRepresentation E hnormal).V,
        (v.unitRepresentation E hnormal).norm.hom u = 0 →
        ∃ ε : (v.unitRepresentation E hnormal).V,
          (v.unitRepresentation E hnormal).ρ g ε - ε = u := by
  let := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
  intro hzero u hu
  let U := v.unitRepresentation E hnormal
  exact CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
    U g hg hzero u hu

/-- **the unit-cohomology axiom.** For every finite unramified Galois extension `L/K`,
`H⁰(G(L/K),U_L)` and `H⁻¹(G(L/K),U_L)` vanish.

This is a predicate on the abstract valuation datum.  It is the source axiom
used in the subsequent proofs of independence and multiplicativity in ;
it is not introduced as a Lean axiom. -/
def SatisfiesUnramifiedUnitCohomology
    (D : DegreeData G) (v : ValuationData D A) : Prop :=
  ∀ (K : FiniteAbstractField G)
    (E : FiniteUnramifiedCyclicExtension D K),
    Limits.IsZero (tateCohomology (E.unitRepresentation v) 0) ∧
      Limits.IsZero (tateCohomology (E.unitRepresentation v) (-1))

end ValuationData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_ClassFieldAxiom
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.conjugateExtension_normal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The finite cohomology data asserted at one finite cyclic extension.
Finiteness is stored before either natural-valued cardinality is formed. -/
structure ClassFieldAxiomCohomologyData (A : Rep ℤ G)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) : Prop where
  /-- The degree-zero Tate cohomology group is finite. -/
  finiteTateHZero : Finite (tateCohomology (E.fixedRepresentation A) 0)
  /-- The degree-minus-one Tate cohomology group is finite. -/
  finiteTateHMinusOne :
    Finite (tateCohomology (E.fixedRepresentation A) (-1))
  /-- Degree-zero Tate cohomology has cardinality equal to the extension degree. -/
  tateHZero_card :
    Nat.card (tateCohomology (E.fixedRepresentation A) 0) =
      (E.toFiniteAbstractExtension.degree : ℕ)
  /-- Degree-minus-one Tate cohomology is trivial by cardinality. -/
  tateHMinusOne_card :
    Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1

/-- **The class-field axiom.**  For every finite cyclic extension `L / K`
with `K` finite over the distinguished base field,
`#H⁰(G(L/K), A_L) = [L : K]` and `#H⁻¹(G(L/K), A_L) = 1`.

Both the base field and the cyclic extension are bundled, so containment,
finiteness, normality, and the chosen generator cannot become detached from
the subgroups to which they belong. -/
def SatisfiesClassFieldAxiom (A : Rep ℤ G) : Prop :=
  ∀ (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K),
    ClassFieldAxiomCohomologyData A K E

namespace SatisfiesClassFieldAxiom

variable {A : Rep ℤ G}

/-- The degree-zero half of the class-field axiom for a bundled cyclic
extension. -/
theorem tateHZero_card
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    Nat.card (tateCohomology (E.fixedRepresentation A) 0) =
      (E.toFiniteAbstractExtension.degree : ℕ) :=
  (hcf K E).tateHZero_card

end SatisfiesClassFieldAxiom

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_DoubleCosetOrbitGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Orbit quotients and double-coset geometry

This module contains the group-theoretic geometry used by the transfer formula:
orbit quotients of coset spaces, inversion of double cosets, transport along
surjective equivariant maps, and replacement of a cyclic subgroup by its
topological closure.  It has no class-formation or field-theoretic input.
-/

universe u

namespace ClassFormation

noncomputable section

open MulAction

/-- Orbits of `S` on `Q/H` are the double cosets `S \\ Q / H`.
This makes the indexing set in Mathlib's transfer formula literally the
double-coset set used by the abstract class-field construction. -/
noncomputable def orbitQuotientEquivDoubleCoset
    {Q : Type u} [Group Q] (S H : Subgroup Q) :
    Quotient (orbitRel S (Q ⧸ H)) ≃
      DoubleCoset.Quotient (S : Set Q) (H : Set Q) where
  toFun z := Quotient.liftOn' z
    (fun q => DoubleCoset.mk S H q.out) (by
      intro q₁ q₂ hq
      rw [orbitRel_apply, mem_orbit_iff] at hq
      obtain ⟨s, hs⟩ := hq
      symm
      apply (DoubleCoset.eq _ _ _ _).mpr
      have hcoset :
          (QuotientGroup.mk q₁.out : Q ⧸ H) =
            QuotientGroup.mk (s.1 * q₂.out) := by
        calc
          QuotientGroup.mk q₁.out = q₁ := Quotient.out_eq' q₁
          _ = s • q₂ := hs.symm
          _ = s • (QuotientGroup.mk q₂.out : Q ⧸ H) :=
            congrArg (s • ·) (Quotient.out_eq' q₂).symm
          _ = QuotientGroup.mk (s.1 * q₂.out) := rfl
      have hh : q₁.out⁻¹ * (s.1 * q₂.out) ∈ H :=
        QuotientGroup.eq.mp hcoset
      refine ⟨s.1, s.2, (q₁.out⁻¹ * (s.1 * q₂.out))⁻¹,
        H.inv_mem hh, ?_⟩
      simp [mul_assoc])
  invFun z := Quotient.liftOn' z
    (fun x => Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H)) (by
      intro x y hxy
      rw [DoubleCoset.rel_iff] at hxy
      obtain ⟨s, hs, h, hh, rfl⟩ := hxy
      apply Quotient.eq''.mpr
      rw [orbitRel_apply, mem_orbit_iff]
      refine ⟨⟨s⁻¹, S.inv_mem hs⟩, ?_⟩
      apply QuotientGroup.eq.mpr
      simpa [mul_assoc] using hh)
  left_inv z := by
    refine Quotient.inductionOn' z ?_
    intro q
    change Quotient.mk'' (QuotientGroup.mk q.out : Q ⧸ H) = Quotient.mk'' q
    exact congrArg Quotient.mk'' (Quotient.out_eq' q)
  right_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    change DoubleCoset.mk S H (Quotient.out
      (QuotientGroup.mk x : Q ⧸ H)) = DoubleCoset.mk S H x
    apply (DoubleCoset.eq _ _ _ _).mpr
    have hh : (Quotient.out (QuotientGroup.mk x : Q ⧸ H))⁻¹ * x ∈ H :=
      QuotientGroup.leftRel_apply.mp
        (Quotient.exact' (Quotient.out_eq' (QuotientGroup.mk x : Q ⧸ H)))
    exact ⟨1, S.one_mem,
      (Quotient.out (QuotientGroup.mk x : Q ⧸ H))⁻¹ * x,
      hh, by simp⟩

/-- The orbit-to-double-coset equivalence sends the orbit represented by
`x` to its double coset.  This exposes that the definition is independent
of the representative selected by `Quotient.out`. -/
@[simp]
theorem orbitQuotientEquivDoubleCoset_mk
    {Q : Type u} [Group Q] (S H : Subgroup Q) (x : Q) :
    orbitQuotientEquivDoubleCoset S H
        (Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H)) =
      DoubleCoset.mk S H x := by
  change DoubleCoset.mk S H
      (Quotient.out (QuotientGroup.mk x : Q ⧸ H)) =
    DoubleCoset.mk S H x
  apply (DoubleCoset.eq _ _ _ _).mpr
  have hh :
      (Quotient.out (QuotientGroup.mk x : Q ⧸ H))⁻¹ * x ∈ H :=
    QuotientGroup.leftRel_apply.mp
      (Quotient.exact'
        (Quotient.out_eq' (QuotientGroup.mk x : Q ⧸ H)))
  exact ⟨1, S.one_mem,
    (Quotient.out (QuotientGroup.mk x : Q ⧸ H))⁻¹ * x,
    hh, by simp⟩

/-- The inverse double-coset equivalence sends a represented double coset
to the corresponding represented orbit. -/
@[simp]
theorem orbitQuotientEquivDoubleCoset_symm_mk
    {Q : Type u} [Group Q] (S H : Subgroup Q) (x : Q) :
    (orbitQuotientEquivDoubleCoset S H).symm (DoubleCoset.mk S H x) =
      Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H) :=
  rfl

/-- Inversion exchanges the two sides of a double-coset space. -/
noncomputable def doubleCosetInversionEquiv
    {Q : Type u} [Group Q] (S H : Subgroup Q) :
    DoubleCoset.Quotient (S : Set Q) (H : Set Q) ≃
      DoubleCoset.Quotient (H : Set Q) (S : Set Q) where
  toFun z := Quotient.liftOn' z
    (fun x => DoubleCoset.mk H S x⁻¹) (by
      intro x y hxy
      rw [DoubleCoset.rel_iff] at hxy
      obtain ⟨s, hs, h, hh, rfl⟩ := hxy
      apply (DoubleCoset.eq _ _ _ _).mpr
      exact ⟨h⁻¹, H.inv_mem hh, s⁻¹, S.inv_mem hs,
        by simp [mul_assoc]⟩)
  invFun z := Quotient.liftOn' z
    (fun x => DoubleCoset.mk S H x⁻¹) (by
      intro x y hxy
      rw [DoubleCoset.rel_iff] at hxy
      obtain ⟨h, hh, s, hs, rfl⟩ := hxy
      apply (DoubleCoset.eq _ _ _ _).mpr
      exact ⟨s⁻¹, S.inv_mem hs, h⁻¹, H.inv_mem hh,
        by simp [mul_assoc]⟩)
  left_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    change DoubleCoset.mk S H (x⁻¹)⁻¹ = DoubleCoset.mk S H x
    rw [inv_inv]
  right_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    change DoubleCoset.mk H S (x⁻¹)⁻¹ = DoubleCoset.mk H S x
    rw [inv_inv]

/-- Orbit sets on the two quotient spaces are exchanged by inversion.
This is the reindexing between the transfer and norm double-coset
decompositions in the proof of transfer--norm naturality. -/
noncomputable def orbitQuotientSwapEquiv
    {Q : Type u} [Group Q] (S H : Subgroup Q) :
    Quotient (orbitRel S (Q ⧸ H)) ≃
      Quotient (orbitRel H (Q ⧸ S)) :=
  (orbitQuotientEquivDoubleCoset S H).trans
    ((doubleCosetInversionEquiv S H).trans
      (orbitQuotientEquivDoubleCoset H S).symm)

/-- The double-coset swap sends the orbit represented by `x` to the orbit
represented by `x⁻¹`; this proposition records that fact independently of
the representatives selected by `Quotient.out`. -/
@[simp]
theorem orbitQuotientSwapEquiv_mk
    {Q : Type u} [Group Q] (S H : Subgroup Q) (x : Q) :
    orbitQuotientSwapEquiv S H
        (Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H)) =
      Quotient.mk'' (QuotientGroup.mk x⁻¹ : Q ⧸ S) := by
  change (orbitQuotientEquivDoubleCoset H S).symm
      (doubleCosetInversionEquiv S H
        (orbitQuotientEquivDoubleCoset S H
          (Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H)))) = _
  unfold orbitQuotientEquivDoubleCoset doubleCosetInversionEquiv
  simp only [Equiv.coe_fn_mk, Quotient.liftOn'_mk'', Equiv.coe_fn_symm_mk]
  let u : Q := Quotient.out (QuotientGroup.mk x : Q ⧸ H)
  have hu : u⁻¹ * x ∈ H := by
    apply QuotientGroup.eq.mp
    exact Quotient.out_eq' (QuotientGroup.mk x : Q ⧸ H)
  apply Quotient.sound'
  rw [orbitRel_apply, mem_orbit_iff]
  refine ⟨⟨u⁻¹ * x, hu⟩, ?_⟩
  change QuotientGroup.mk ((u⁻¹ * x) * x⁻¹) =
    (QuotientGroup.mk u⁻¹ : Q ⧸ S)
  simp [mul_assoc]

/-- A surjective homomorphism and an equivariant equivalence of the acted-on
sets induce an equivalence of orbit sets. -/
noncomputable def orbitQuotientEquivOfSurjectiveEquivariant
    {M : Type*} {N : Type*} {X : Type*} {Y : Type*} [Group M] [Group N]
    [MulAction M X] [MulAction N Y]
    (f : M →* N) (hf : Function.Surjective f) (e : X ≃ Y)
    (he : ∀ (m : M) (x : X), e (m • x) = f m • e x) :
    Quotient (orbitRel M X) ≃ Quotient (orbitRel N Y) :=
  { toFun := Quotient.map' e (by
      intro x y hxy
      rw [orbitRel_apply, mem_orbit_iff] at hxy ⊢
      obtain ⟨m, hm⟩ := hxy
      exact ⟨f m, (he m y).symm.trans (congrArg e hm)⟩)
    invFun := Quotient.map' e.symm (by
      intro x y hxy
      rw [orbitRel_apply, mem_orbit_iff] at hxy ⊢
      obtain ⟨n, hn⟩ := hxy
      obtain ⟨m, rfl⟩ := hf n
      refine ⟨m, ?_⟩
      apply e.injective
      rw [he, e.apply_symm_apply, e.apply_symm_apply]
      exact hn)
    left_inv := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      change Quotient.mk'' (e.symm (e x)) = Quotient.mk'' x
      rw [e.symm_apply_apply]
    right_inv := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro y
      change Quotient.mk'' (e (e.symm y)) = Quotient.mk'' y
      rw [e.apply_symm_apply] }

/-- The orbit-quotient equivalence sends a represented orbit to the image representative. -/
@[simp]
theorem orbitQuotientEquivOfSurjectiveEquivariant_mk
    {M : Type*} {N : Type*} {X : Type*} {Y : Type*} [Group M] [Group N]
    [MulAction M X] [MulAction N Y]
    (f : M →* N) (hf : Function.Surjective f) (e : X ≃ Y)
    (he : ∀ (m : M) (x : X), e (m • x) = f m • e x) (x : X) :
    orbitQuotientEquivOfSurjectiveEquivariant f hf e he
        (Quotient.mk'' x) = Quotient.mk'' (e x) :=
  rfl

/-- The inverse orbit-quotient equivalence lifts a representative to its source orbit. -/
@[simp]
theorem orbitQuotientEquivOfSurjectiveEquivariant_symm_mk
    {M : Type*} {N : Type*} {X : Type*} {Y : Type*} [Group M] [Group N]
    [MulAction M X] [MulAction N Y]
    (f : M →* N) (hf : Function.Surjective f) (e : X ≃ Y)
    (he : ∀ (m : M) (x : X), e (m • x) = f m • e x) (y : Y) :
    (orbitQuotientEquivOfSurjectiveEquivariant f hf e he).symm
        (Quotient.mk'' y) = Quotient.mk'' (e.symm y) :=
  rfl

/-- A group equivalence transports left cosets along the image of a
subgroup; no normality hypothesis is required. -/
noncomputable def leftCosetEquivOfMulEquiv
    {Q : Type*} {R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (S : Subgroup Q) :
    Q ⧸ S ≃ R ⧸ S.map e.toMonoidHom where
  toFun := Quotient.map' e (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    exact ⟨x⁻¹ * y, hxy, by simp⟩)
  invFun := Quotient.map' e.symm (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    obtain ⟨z, hz, heq⟩ := hxy
    have hzEq : e.symm (x⁻¹ * y) = z := by
      rw [← heq]
      simp
    have hxyEq : (e.symm x)⁻¹ * e.symm y = z := by
      calc
        (e.symm x)⁻¹ * e.symm y = e.symm (x⁻¹ * y) := by simp
        _ = z := hzEq
    rw [hxyEq]
    exact hz)
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change QuotientGroup.mk (e.symm (e x)) = QuotientGroup.mk x
    rw [e.symm_apply_apply]
  right_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change QuotientGroup.mk (e (e.symm x)) = QuotientGroup.mk x
    rw [e.apply_symm_apply]

/-- A multiplicative equivalence transports a left-coset representative as expected. -/
@[simp]
theorem leftCosetEquivOfMulEquiv_mk
    {Q : Type*} {R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (S : Subgroup Q) (x : Q) :
    leftCosetEquivOfMulEquiv e S (QuotientGroup.mk x) =
      QuotientGroup.mk (e x) :=
  rfl

/-- Closing a cyclic subgroup does not change its double cosets against a
closed finite-index subgroup.  This is the density/open-subgroup step which
passes from the algebraic powers of a Frobenius to its closed procyclic
subgroup in the classical argument. -/
theorem doubleCoset_closedCyclic_eq
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (H : Subgroup Q) [H.FiniteIndex] (hHclosed : IsClosed (H : Set Q))
    (g x y : Q) :
    DoubleCoset.mk H (Subgroup.zpowers g) x =
        DoubleCoset.mk H (Subgroup.zpowers g) y ↔
      DoubleCoset.mk H
          (closedSubgroupGenerated ({g} : Set Q)).toSubgroup x =
        DoubleCoset.mk H
          (closedSubgroupGenerated ({g} : Set Q)).toSubgroup y := by
  let C := (closedSubgroupGenerated ({g} : Set Q)).toSubgroup
  have hzC : Subgroup.zpowers g ≤ C := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.le_topologicalClosure _
  constructor
  · intro hxy
    rw [DoubleCoset.eq] at hxy ⊢
    obtain ⟨h, hh, s, hs, hsxy⟩ := hxy
    exact ⟨h, hh, s, hzC hs, hsxy⟩
  · intro hxy
    rw [DoubleCoset.eq] at hxy ⊢
    obtain ⟨h, hh, c, hc, rfl⟩ := hxy
    have hcclosure : c ∈ closure
        ((Subgroup.zpowers g : Subgroup Q) : Set Q) := by
      rw [Subgroup.zpowers_eq_closure]
      rw [← Subgroup.topologicalClosure_coe]
      change c ∈
        ((Subgroup.closure ({g} : Set Q)).topologicalClosure : Set Q) at hc
      exact hc
    let U : Set Q :=
      (fun s : Q => x * c * s⁻¹ * x⁻¹) ⁻¹' (H : Set Q)
    have hUopen : IsOpen U := by
      apply (((continuous_const.mul continuous_inv).mul
        continuous_const).isOpen_preimage (H : Set Q))
      exact H.isOpen_of_isClosed_of_finiteIndex hHclosed
    have hcU : c ∈ U := by
      change x * c * c⁻¹ * x⁻¹ ∈ H
      simp [mul_assoc]
    obtain ⟨s, hsU, hs⟩ :=
      (mem_closure_iff.mp hcclosure U hUopen hcU)
    have hsH : x * c * s⁻¹ * x⁻¹ ∈ H := hsU
    refine ⟨h * (x * c * s⁻¹ * x⁻¹), H.mul_mem hh hsH,
      s, hs, ?_⟩
    simp [mul_assoc]

/-- Double-coset equivalence induced by the preceding density argument. -/
noncomputable def doubleCosetClosedCyclicEquiv
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (H : Subgroup Q) [H.FiniteIndex] (hHclosed : IsClosed (H : Set Q))
    (g : Q) :
    DoubleCoset.Quotient (H : Set Q) (Subgroup.zpowers g : Set Q) ≃
      DoubleCoset.Quotient (H : Set Q)
        ((closedSubgroupGenerated ({g} : Set Q)).toSubgroup : Set Q) where
  toFun z := Quotient.liftOn' z
    (fun x => DoubleCoset.mk H
      (closedSubgroupGenerated ({g} : Set Q)).toSubgroup x)
    (fun x y hxy =>
      (doubleCoset_closedCyclic_eq H hHclosed g x y).mp
        (Quotient.sound' hxy))
  invFun z := Quotient.liftOn' z
    (fun x => DoubleCoset.mk H (Subgroup.zpowers g) x)
    (fun x y hxy =>
      (doubleCoset_closedCyclic_eq H hHclosed g x y).mpr
        (Quotient.sound' hxy))
  left_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    rfl
  right_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    rfl

/-- On orbit sets, replacing the powers of a Frobenius by their closure is
an equivalence whenever the subgroup acting on the other side has finite
index and is closed. -/
noncomputable def orbitQuotientClosedCyclicEquiv
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (H : Subgroup Q) [H.FiniteIndex] (hHclosed : IsClosed (H : Set Q))
    (g : Q) :
    Quotient (orbitRel H (Q ⧸ Subgroup.zpowers g)) ≃
      Quotient (orbitRel H
        (Q ⧸ (closedSubgroupGenerated ({g} : Set Q)).toSubgroup)) :=
  (orbitQuotientEquivDoubleCoset H (Subgroup.zpowers g)).trans
    ((doubleCosetClosedCyclicEquiv H hHclosed g).trans
      (orbitQuotientEquivDoubleCoset H
        (closedSubgroupGenerated ({g} : Set Q)).toSubgroup).symm)

/-- Passing from the powers of `g` to their closure preserves the orbit
represented by every literal group element. -/
@[simp]
theorem orbitQuotientClosedCyclicEquiv_mk
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (H : Subgroup Q) [H.FiniteIndex] (hHclosed : IsClosed (H : Set Q))
    (g x : Q) :
    orbitQuotientClosedCyclicEquiv H hHclosed g
        (Quotient.mk'' (QuotientGroup.mk x : Q ⧸ Subgroup.zpowers g)) =
      Quotient.mk'' (QuotientGroup.mk x :
        Q ⧸ (closedSubgroupGenerated ({g} : Set Q)).toSubgroup) := by
  let C := (closedSubgroupGenerated ({g} : Set Q)).toSubgroup
  change (orbitQuotientEquivDoubleCoset H C).symm
      (doubleCosetClosedCyclicEquiv H hHclosed g
        (orbitQuotientEquivDoubleCoset H (Subgroup.zpowers g)
          (Quotient.mk''
            (QuotientGroup.mk x : Q ⧸ Subgroup.zpowers g)))) = _
  unfold orbitQuotientEquivDoubleCoset doubleCosetClosedCyclicEquiv
  simp only [Equiv.coe_fn_mk, Quotient.liftOn'_mk'', Equiv.coe_fn_symm_mk]
  let a := Quotient.out (QuotientGroup.mk x : Q ⧸ Subgroup.zpowers g)
  have ha : a⁻¹ * x ∈ Subgroup.zpowers g :=
    QuotientGroup.leftRel_apply.mp
      (Quotient.exact' (Quotient.out_eq'
        (QuotientGroup.mk x : Q ⧸ Subgroup.zpowers g)))
  have haC : a⁻¹ * x ∈ C := by
    apply Subgroup.le_topologicalClosure _
    simpa [Subgroup.zpowers_eq_closure] using ha
  apply congrArg Quotient.mk''
  apply QuotientGroup.eq.mpr
  exact haC

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_NormSubgroup
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction: norm subgroups for infinite extensions

For an infinite abstract extension `E | K`, the abstract class-field construction defines
`N_{E|K} A_E` as the intersection of the norm images from all finite
intermediate fields.  This file records that definition literally.
-/

noncomputable section

section finiteIntermediateFields

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A finite intermediate field `M` of an abstract extension `E | K`.
Contravariantly, its subgroup lies between `G_E` and `G_K`. -/
structure FiniteIntermediateField (E K : ClosedSubgroup G) where
  /-- The closed subgroup representing the intermediate field. -/
  field : ClosedSubgroup G
  /-- The extension endpoint lies below the intermediate-field subgroup. -/
  above : E.toSubgroup ≤ field.toSubgroup
  /-- The intermediate-field subgroup lies below the base endpoint. -/
  below : field.toSubgroup ≤ K.toSubgroup
  /-- The intermediate field has finite degree over the base endpoint. -/
  finite : Finite
    (K.toSubgroup ⧸ extensionSubgroup K field below)

namespace FiniteIntermediateField

/-- The base field itself is a finite intermediate field. -/
def base (E K : ClosedSubgroup G) (hEK : E.toSubgroup ≤ K.toSubgroup) :
    FiniteIntermediateField E K where
  field := K
  above := hEK
  below := le_rfl
  finite := by
    have htop : extensionSubgroup K K le_rfl = ⊤ := by
      ext x
      constructor
      · intro _
        trivial
      · intro _
        exact x.2
    rw [htop]
    infer_instance

end FiniteIntermediateField

end finiteIntermediateFields

section infiniteNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The norm image from a finite intermediate field `M` to `K`. -/
def finiteIntermediateNormRange
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (M : FiniteIntermediateField E K) :
    AddSubgroup (ambientFixedAddSubgroup A K) := by
  letI := M.finite
  exact (relativeNorm A K M.field M.below).range

/-- The norm subgroup for a possibly infinite extension:
`N_{E|K} A_E = ⋂_M N_{M|K} A_M`, where `M` runs through the finite
intermediate fields. -/
def infiniteNormSubgroup
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    AddSubgroup (ambientFixedAddSubgroup A K) :=
  ⨅ M : FiniteIntermediateField E K,
    finiteIntermediateNormRange A E K M

/-- Membership in the infinite norm subgroup is characterized by norms from every finite level. -/
@[simp]
theorem mem_infiniteNormSubgroup_iff
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    a ∈ infiniteNormSubgroup A E K ↔
      ∀ M : FiniteIntermediateField E K,
        a ∈ finiteIntermediateNormRange A E K M := by
  simp [infiniteNormSubgroup]

/-- The quotient `A_K / N_{E|K} A_E` used by the reciprocity map.

This public object is opaque: clients use `infiniteNormClass`,
`InfiniteNormQuotient.induction_on`, or `infiniteNormQuotientLift` instead of
depending on the concrete quotient representation. -/
def InfiniteNormQuotient
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :=
  ambientFixedAddSubgroup A K ⧸ infiniteNormSubgroup A E K

/-- The additive group structure on the infinite norm quotient. -/
instance infiniteNormQuotientAddCommGroup
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    AddCommGroup (InfiniteNormQuotient A E K) := by
  unfold InfiniteNormQuotient
  infer_instance

/-- The explicit boundary to the concrete quotient implementation. -/
def infiniteNormQuotientConcreteEquiv
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    InfiniteNormQuotient A E K ≃+
      ambientFixedAddSubgroup A K ⧸ infiniteNormSubgroup A E K := by
  unfold InfiniteNormQuotient
  exact AddEquiv.refl _

/-- The canonical class map into the infinite norm quotient. -/
def infiniteNormClass
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    ambientFixedAddSubgroup A K →+
      InfiniteNormQuotient A E K := by
  unfold InfiniteNormQuotient
  exact QuotientAddGroup.mk' (infiniteNormSubgroup A E K)

/-- The concrete infinite-norm quotient equivalence sends a class to its
canonical quotient class. -/
@[simp]
theorem infiniteNormQuotientConcreteEquiv_infiniteNormClass
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    infiniteNormQuotientConcreteEquiv A E K (infiniteNormClass A E K a) =
      QuotientAddGroup.mk' (infiniteNormSubgroup A E K) a := by
  rfl

/-- An infinite norm class vanishes exactly when its representative lies in the norm subgroup. -/
@[simp]
theorem infiniteNormClass_eq_zero_iff
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    infiniteNormClass A E K a = 0 ↔
      a ∈ infiniteNormSubgroup A E K := by
  unfold infiniteNormClass InfiniteNormQuotient
  exact QuotientAddGroup.eq_zero_iff a

/-- Descend an additive homomorphism that kills the infinite norm subgroup. -/
def infiniteNormQuotientLift
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : infiniteNormSubgroup A E K ≤ f.ker) :
    InfiniteNormQuotient A E K →+ B := by
  unfold InfiniteNormQuotient
  exact QuotientAddGroup.lift (infiniteNormSubgroup A E K) f hf

/-- Lifting the canonical infinite norm class recovers its representative in the
concrete quotient. -/
@[simp]
theorem infiniteNormQuotientLift_infiniteNormClass
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : infiniteNormSubgroup A E K ≤ f.ker)
    (a : ambientFixedAddSubgroup A K) :
    infiniteNormQuotientLift A E K f hf (infiniteNormClass A E K a) = f a := by
  rfl

end infiniteNorms

section maximalUnramifiedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The maximal unramified extension `\widetilde L`, represented by
`I_L = G_L ∩ ker(d)`. -/
def maximalUnramifiedField (D : DegreeData G) (L : ClosedSubgroup G) :
    ClosedSubgroup G :=
  D.fieldInertia L

/-- The implementation theorem identifying the maximal unramified field
with absolute inertia.  Downstream code should use this theorem instead of
unfolding `maximalUnramifiedField`. -/
theorem maximalUnramifiedField_eq_fieldInertia
    (D : DegreeData G) (L : ClosedSubgroup G) :
    D.maximalUnramifiedField L = D.fieldInertia L := by
  rfl

/-- Membership in the maximal unramified field is the expected inertia
condition. -/
@[simp]
theorem mem_maximalUnramifiedField_iff
    (D : DegreeData G) (L : ClosedSubgroup G) (g : G) :
    g ∈ D.maximalUnramifiedField L ↔ g ∈ L ∧ D.degree g = 1 := by
  rw [D.maximalUnramifiedField_eq_fieldInertia]
  exact D.mem_fieldInertia_iff L g

/-- Every finite unramified field lies below the maximal unramified field. -/
theorem maximalUnramifiedField_le (D : DegreeData G) (L : ClosedSubgroup G) :
    (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup := by
  rw [D.maximalUnramifiedField_eq_fieldInertia]
  exact inf_le_left

/-- A field containing all finite unramified fields contains the maximal unramified field. -/
theorem maximalUnramifiedField_le_of_le (D : DegreeData G)
    {L K : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (D.maximalUnramifiedField L).toSubgroup ≤ K.toSubgroup :=
  (D.maximalUnramifiedField_le L).trans hLK

/-- Monotonicity of maximal unramified fields. -/
theorem maximalUnramifiedField_mono (D : DegreeData G)
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (D.maximalUnramifiedField L).toSubgroup ≤
      (D.maximalUnramifiedField K).toSubgroup := by
  intro g hg
  have hg' : g ∈ D.maximalUnramifiedField L := hg
  obtain ⟨hgL, hgd⟩ := (D.mem_maximalUnramifiedField_iff L g).1 hg'
  exact (D.mem_maximalUnramifiedField_iff K g).2 ⟨hLK hgL, hgd⟩

/-- Inside `G_K`, the absolute subgroup of `\widetilde L` is the relative
inertia subgroup. -/
theorem extensionSubgroup_maximalUnramifiedField (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    extensionSubgroup K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK) =
      D.extensionInertiaWithin K L hLK := by
  ext k
  constructor
  · intro hk
    have hkMax : k.1 ∈ D.maximalUnramifiedField L :=
      (mem_extensionSubgroup_iff K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK) k).1 hk
    have hkData := (D.mem_maximalUnramifiedField_iff L k.1).1 hkMax
    exact ⟨(mem_extensionSubgroup_iff K L hLK k).2 hkData.1,
      (D.mem_fieldInertiaWithin_iff K k).2 hkData.2⟩
  · intro hk
    apply (mem_extensionSubgroup_iff K (D.maximalUnramifiedField L)
      (D.maximalUnramifiedField_le_of_le hLK) k).2
    apply (D.mem_maximalUnramifiedField_iff L k.1).2
    exact ⟨(mem_extensionSubgroup_iff K L hLK k).1 hk.1,
      (D.mem_fieldInertiaWithin_iff K k).1 hk.2⟩

/-- The subgroup representing the maximal unramified field is normal in the base subgroup. -/
theorem extensionSubgroup_maximalUnramifiedField_normal (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (extensionSubgroup K (D.maximalUnramifiedField L)
      (D.maximalUnramifiedField_le_of_le hLK)).Normal := by
  rw [D.extensionSubgroup_maximalUnramifiedField K L hLK]
  infer_instance

end DegreeData

end maximalUnramifiedFields

section maximalUnramifiedNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- `N_{\widetilde L|K} A_{\widetilde L}` in the reciprocity construction. -/
def maximalUnramifiedNormSubgroup (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) :
    AddSubgroup (ambientFixedAddSubgroup A K) :=
  infiniteNormSubgroup A (D.maximalUnramifiedField L) K

/-- The maximal-unramified norm subgroup is the infinite norm subgroup for
the maximal unramified field. -/
theorem maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    D.maximalUnramifiedNormSubgroup A K L =
      infiniteNormSubgroup A (D.maximalUnramifiedField L) K := by
  rfl

/-- Membership in the maximal unramified norm subgroup is characterized levelwise. -/
@[simp]
theorem mem_maximalUnramifiedNormSubgroup_iff
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    a ∈ D.maximalUnramifiedNormSubgroup A K L ↔
      a ∈ infiniteNormSubgroup A (D.maximalUnramifiedField L) K := by
  rw [D.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup]

/-- `A_K / N_{\widetilde L|K} A_{\widetilde L}`.

This is an opaque public object, not a reducible alias for the infinite norm
quotient. -/
def MaximalUnramifiedNormQuotient (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) :=
  InfiniteNormQuotient A (D.maximalUnramifiedField L) K

/-- The additive group structure on the maximal-unramified norm quotient. -/
instance maximalUnramifiedNormQuotientAddCommGroup
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    AddCommGroup (D.MaximalUnramifiedNormQuotient A K L) := by
  unfold MaximalUnramifiedNormQuotient
  infer_instance

/-- The explicit boundary to the corresponding infinite norm quotient. -/
def maximalUnramifiedNormQuotientInfiniteEquiv
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    D.MaximalUnramifiedNormQuotient A K L ≃+
      InfiniteNormQuotient A (D.maximalUnramifiedField L) K := by
  unfold MaximalUnramifiedNormQuotient
  exact AddEquiv.refl _

/-- The canonical class map into the maximal-unramified norm quotient. -/
def maximalUnramifiedNormClass
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    ambientFixedAddSubgroup A K →+
      D.MaximalUnramifiedNormQuotient A K L := by
  unfold MaximalUnramifiedNormQuotient
  exact infiniteNormClass A (D.maximalUnramifiedField L) K

/-- The infinite quotient equivalence preserves the canonical maximal-unramified norm class. -/
@[simp]
theorem maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    D.maximalUnramifiedNormQuotientInfiniteEquiv A K L
        (D.maximalUnramifiedNormClass A K L a) =
      infiniteNormClass A (D.maximalUnramifiedField L) K a := by
  rfl

/-- A maximal-unramified norm class vanishes exactly on its defining norm subgroup. -/
@[simp]
theorem maximalUnramifiedNormClass_eq_zero_iff
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    D.maximalUnramifiedNormClass A K L a = 0 ↔
      a ∈ D.maximalUnramifiedNormSubgroup A K L := by
  unfold maximalUnramifiedNormClass MaximalUnramifiedNormQuotient
  exact infiniteNormClass_eq_zero_iff A (D.maximalUnramifiedField L) K a

/-- Descend an additive homomorphism that kills the maximal-unramified norm subgroup. -/
def maximalUnramifiedNormQuotientLift
    {B : Type*} [AddCommGroup B]
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : D.maximalUnramifiedNormSubgroup A K L ≤ f.ker) :
    D.MaximalUnramifiedNormQuotient A K L →+ B := by
  unfold MaximalUnramifiedNormQuotient
  refine infiniteNormQuotientLift A (D.maximalUnramifiedField L) K f ?_
  intro a ha
  exact hf ((D.mem_maximalUnramifiedNormSubgroup_iff A K L a).2 ha)

/-- The quotient lift sends a maximal-unramified norm class back to its representative. -/
@[simp]
theorem maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass
    {B : Type*} [AddCommGroup B]
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : D.maximalUnramifiedNormSubgroup A K L ≤ f.ker)
    (a : ambientFixedAddSubgroup A K) :
    D.maximalUnramifiedNormQuotientLift A K L f hf
        (D.maximalUnramifiedNormClass A K L a) = f a := by
  unfold maximalUnramifiedNormQuotientLift maximalUnramifiedNormClass
    MaximalUnramifiedNormQuotient
  exact infiniteNormQuotientLift_infiniteNormClass
    A (D.maximalUnramifiedField L) K f (by
      intro b hb
      exact hf ((D.mem_maximalUnramifiedNormSubgroup_iff A K L b).2 hb)) a

end DegreeData

end maximalUnramifiedNorms

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_FiniteNormQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.relativeConjugateCosetEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The finite norm subgroup `N_{L|K}A_L`. -/
def finiteNormSubgroup (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    AddSubgroup (ambientFixedAddSubgroup A K) :=
  (relativeNorm A K L hLK).range

/-- The finite norm quotient in the finite reciprocity equivalence.

This is a stable public object rather than an `abbrev`: downstream APIs do
not acquire a reducibility dependency on the concrete quotient
representation. -/
def FiniteNormQuotient (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :=
  ambientFixedAddSubgroup A K ⧸ finiteNormSubgroup A K L hLK

/-- The additive group structure of the finite norm quotient.  It is
exported explicitly so typeclass search does not unfold the stable public
type synonym. -/
instance finiteNormQuotientAddCommGroup
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    AddCommGroup (FiniteNormQuotient A K L hLK) := by
  unfold FiniteNormQuotient
  infer_instance

/-- The canonical equivalence with the concrete quotient implementation.
Clients that genuinely need quotient-level operations can use this boundary
without relying on reducible unfolding. -/
def finiteNormQuotientConcreteEquiv
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    FiniteNormQuotient A K L hLK ≃+
      ambientFixedAddSubgroup A K ⧸ finiteNormSubgroup A K L hLK := by
  unfold FiniteNormQuotient
  exact AddEquiv.refl _

/-- The canonical class map into the finite norm quotient. -/
def finiteNormClassHom
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    ambientFixedAddSubgroup A K →+ FiniteNormQuotient A K L hLK := by
  unfold FiniteNormQuotient
  exact QuotientAddGroup.mk' (finiteNormSubgroup A K L hLK)

/-- The class of an element modulo the finite norm subgroup. -/
def finiteNormClass
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A K) :
    FiniteNormQuotient A K L hLK :=
  finiteNormClassHom A K L hLK a

/-- The finite norm-class map sends zero to the trivial quotient class. -/
@[simp]
theorem finiteNormClass_zero
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    finiteNormClass A K L hLK 0 = 0 := by
  exact map_zero (finiteNormClassHom A K L hLK)

/-- Finite norm classes preserve addition of representatives. -/
@[simp]
theorem finiteNormClass_add
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a b : ambientFixedAddSubgroup A K) :
    finiteNormClass A K L hLK (a + b) =
      finiteNormClass A K L hLK a + finiteNormClass A K L hLK b := by
  exact map_add (finiteNormClassHom A K L hLK) a b

/-- Finite norm classes preserve subtraction of representatives. -/
@[simp]
theorem finiteNormClass_sub
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a b : ambientFixedAddSubgroup A K) :
    finiteNormClass A K L hLK (a - b) =
      finiteNormClass A K L hLK a - finiteNormClass A K L hLK b := by
  exact map_sub (finiteNormClassHom A K L hLK) a b

/-- Finite norm classes commute with natural scalar multiplication. -/
@[simp]
theorem finiteNormClass_nsmul
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (n : ℕ) (a : ambientFixedAddSubgroup A K) :
    finiteNormClass A K L hLK (n • a) =
      n • finiteNormClass A K L hLK a := by
  exact map_nsmul (finiteNormClassHom A K L hLK) n a

/-- The concrete quotient equivalence sends a finite norm class to its canonical coset. -/
@[simp]
theorem finiteNormQuotientConcreteEquiv_finiteNormClass
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A K) :
    finiteNormQuotientConcreteEquiv A K L hLK
        (finiteNormClass A K L hLK a) =
      QuotientAddGroup.mk' (finiteNormSubgroup A K L hLK) a := by
  rfl

/-- A finite norm class vanishes exactly when its representative lies in the norm subgroup. -/
@[simp]
theorem finiteNormClass_eq_zero_iff
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A K) :
    finiteNormClass A K L hLK a = 0 ↔
      a ∈ finiteNormSubgroup A K L hLK := by
  unfold finiteNormClass finiteNormClassHom FiniteNormQuotient
  exact QuotientAddGroup.eq_zero_iff _

/-- Every finite norm-quotient class has an ambient representative. -/
theorem finiteNormClass_surjective
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Function.Surjective (finiteNormClass A K L hLK) := by
  intro q
  change ambientFixedAddSubgroup A K ⧸
    finiteNormSubgroup A K L hLK at q
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
    (finiteNormSubgroup A K L hLK) q
  exact ⟨a, rfl⟩

/-- Eliminate a finite norm-quotient class through an ambient representative. -/
@[elab_as_elim]
theorem FiniteNormQuotient.induction_on
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    {motive : FiniteNormQuotient A K L hLK → Prop}
    (q : FiniteNormQuotient A K L hLK)
    (h : ∀ a, motive (finiteNormClass A K L hLK a)) : motive q := by
  obtain ⟨a, rfl⟩ := finiteNormClass_surjective A K L hLK q
  exact h a

/-- Descend an additive homomorphism that kills the finite norm subgroup. -/
def finiteNormQuotientLift
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : finiteNormSubgroup A K L hLK ≤ f.ker) :
    FiniteNormQuotient A K L hLK →+ B := by
  unfold FiniteNormQuotient
  exact QuotientAddGroup.lift (finiteNormSubgroup A K L hLK) f hf

/-- The quotient lift evaluates on a finite norm class by the chosen representative. -/
@[simp]
theorem finiteNormQuotientLift_finiteNormClass
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : finiteNormSubgroup A K L hLK ≤ f.ker)
    (a : ambientFixedAddSubgroup A K) :
    finiteNormQuotientLift A K L hLK f hf
        (finiteNormClass A K L hLK a) = f a := by
  rfl

end finiteNorms

section finiteIntermediateField

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- `L` itself is a finite intermediate field of `\widetilde L | K`. -/
def fieldAsMaximalUnramifiedIntermediate (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    FiniteIntermediateField (D.maximalUnramifiedField L) K where
  field := L
  above := D.maximalUnramifiedField_le L
  below := hLK
  finite := hfinite

end DegreeData

end finiteIntermediateField

section quotientMaps

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The defining intersection for the infinite norm subgroup is contained
in the norm image from the particular finite field `L`. -/
theorem maximalUnramifiedNormSubgroup_le_finiteNormSubgroup
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    D.maximalUnramifiedNormSubgroup A K L ≤
      finiteNormSubgroup A K L hLK := by
  rw [D.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup]
  rw [infiniteNormSubgroup]
  refine iInf_le_of_le (D.fieldAsMaximalUnramifiedIntermediate K L hLK) ?_
  rfl

theorem maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    D.maximalUnramifiedNormSubgroup A K L ≤
      (finiteNormClassHom A K L hLK).ker := by
  intro a ha
  exact (finiteNormClass_eq_zero_iff A K L hLK a).2
    (D.maximalUnramifiedNormSubgroup_le_finiteNormSubgroup A K L hLK ha)

/-- The canonical quotient map
`A_K/N_{\widetilde L|K}A_{\widetilde L} → A_K/N_{L|K}A_L`. -/
def maximalUnramifiedToFiniteNormQuotient
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    D.MaximalUnramifiedNormQuotient A K L →+
      FiniteNormQuotient A K L hLK :=
  D.maximalUnramifiedNormQuotientLift A K L
    (finiteNormClassHom A K L hLK)
    (D.maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker A K L hLK)

/-- The comparison to a finite norm quotient carries the maximal-unramified
class to its finite-level class. -/
@[simp]
theorem maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A K) :
    D.maximalUnramifiedToFiniteNormQuotient A K L hLK
        (D.maximalUnramifiedNormClass A K L a) =
      finiteNormClass A K L hLK a := by
  exact D.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass
    A K L (finiteNormClassHom A K L hLK)
    (D.maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker A K L hLK) a

end DegreeData

end quotientMaps

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_TransferOrbitClosure
attribute [-simp] _root_.ClassFormation.orbitQuotientClosedCyclicEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ClassFormation

/-!
# The closed cyclic subgroup attached to one transfer orbit

For a finite-index subgroup `H` and an element `g`, the intersection of
the closed cyclic subgroup generated by `g` with the stabilizer of a coset
is generated by the power whose exponent is that orbit's minimal period.
This is the topological group calculation used in transfer--norm naturality.
-/

noncomputable section

open MulAction

/-- Conjugation carries membership in the closed cyclic subgroup generated by
`x` to membership in the closed cyclic subgroup generated by the conjugate of
`x`. -/
theorem mem_closedSubgroupGenerated_conjugate_iff
    {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (q x c : Q) :
    c ∈ (closedSubgroupGenerated ({x} : Set Q)).toSubgroup ↔
      q * c * q⁻¹ ∈
        (closedSubgroupGenerated ({q * x * q⁻¹} : Set Q)).toSubgroup := by
  let conjugationHom (g : Q) : Q →ₜ* Q :=
    { toMonoidHom := (MulAut.conj g).toMonoidHom
      continuous_toFun := IsTopologicalGroup.continuous_conj g }
  constructor
  · intro hc
    exact map_mem_closedSubgroupGenerated_singleton
      (conjugationHom q) x hc
  · intro hc
    have h := map_mem_closedSubgroupGenerated_singleton
      (conjugationHom q⁻¹) (q * x * q⁻¹) hc
    change q⁻¹ * (q * c * q⁻¹) * (q⁻¹)⁻¹ ∈
      (closedSubgroupGenerated
        ({q⁻¹ * (q * x * q⁻¹) * (q⁻¹)⁻¹} : Set Q)).toSubgroup at h
    simpa [mul_assoc] using h

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_PrimeChoice
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.infiniteNormQuotientAddCommGroup
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.maximalUnramifiedNormClass_eq_zero_iff _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.mem_maximalUnramifiedField_iff _root_.ClassFormation.DegreeData.mem_maximalUnramifiedNormSubgroup_iff _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.infiniteNormClass_eq_zero_iff _root_.ClassFormation.infiniteNormQuotientConcreteEquiv_infiniteNormClass _root_.ClassFormation.infiniteNormQuotientLift_infiniteNormClass _root_.ClassFormation.mem_infiniteNormSubgroup_iff _root_.ClassFormation.zHatPowNat_apply_toAdd _root_.ClassFormation.zHatPowNat_one _root_.ClassFormation.zHatReductionMul_apply_toAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction: choosing prime elements

Surjectivity of the normalized valuation supplies a prime element in every
finite abstract field.  Any two choices differ by a unit (additively, their
difference has value zero).
-/

noncomputable section

namespace ValuationData

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- A chosen prime element of a finite abstract field.  Later independence
lemmas show that the reciprocity class does not depend on this choice. -/
def chosenPrimeElement (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field :=
  Classical.choose (v.normalizedValuation_surjective K v.oneValue)

/-- Establishes the identity `v.valuationAt K (v.chosenPrimeElement K) = v.oneValue`. -/
@[simp]
theorem valuationAt_chosenPrimeElement (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    v.valuationAt K (v.chosenPrimeElement K) = v.oneValue :=
  Classical.choose_spec (v.normalizedValuation_surjective K v.oneValue)

/-- The chosen prime element has valuation equal to the distinguished degree-one value. -/
theorem chosenPrimeElement_isPrime (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    v.IsPrimeElement K (v.chosenPrimeElement K) :=
  v.valuationAt_chosenPrimeElement K

/-- In additive notation, two prime elements differ by a unit. -/
theorem sub_mem_unitAddSubgroup_of_prime
    (v : ValuationData D A) (K : FiniteAbstractField G)
    {π π' : ambientFixedAddSubgroup A K.field}
    (hπ : v.IsPrimeElement K π) (hπ' : v.IsPrimeElement K π') :
    π' - π ∈ v.unitAddSubgroup K := by
  rw [v.mem_unitAddSubgroup_iff, map_sub, hπ, hπ']
  exact sub_self _

/-- Establishes the membership statement `π - v.chosenPrimeElement K ∈ v.unitAddSubgroup K`. -/
theorem sub_chosenPrimeElement_mem_unitAddSubgroup
    (v : ValuationData D A) (K : FiniteAbstractField G)
    {π : ambientFixedAddSubgroup A K.field}
    (hπ : v.IsPrimeElement K π) :
    π - v.chosenPrimeElement K ∈ v.unitAddSubgroup K :=
  v.sub_mem_unitAddSubgroup_of_prime
    K (v.chosenPrimeElement_isPrime K) hπ

end ValuationData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_ReciprocityIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction: independence of the prime element

This file supplies the finite-Galois cofinality and compositum argument used to prove that the reciprocity construction is independent of its prime element.
-/

noncomputable section

section groupTheoreticRefinements

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- The field compositum `MΣ`, contravariantly represented by
`G_M ∩ G_Σ`. -/
def compositumWith
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) : ClosedSubgroup G :=
  M.field ⊓ S

/-- The common compositum refinement maps below its left input field. -/
theorem compositumWith_le_left
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) :
    (M.compositumWith S).toSubgroup ≤ M.field.toSubgroup :=
  inf_le_left

/-- The common compositum refinement maps below its right input field. -/
theorem compositumWith_le_right
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) :
    (M.compositumWith S).toSubgroup ≤ S.toSubgroup :=
  inf_le_right

end FiniteIntermediateField

end groupTheoreticRefinements

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_FiniteGaloisSubextension
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.relativeConjugateCosetEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- A finite Galois extension `L / K`, represented by `G_L ≤ G_K`. -/
structure FiniteGaloisSubextension (K : ClosedSubgroup G) where
  /-- The closed subgroup representing the top field. -/
  field : ClosedSubgroup G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.toSubgroup ≤ K.toSubgroup
  /-- The top-field subgroup is normal inside the base-field subgroup. -/
  normal : (extensionSubgroup K field below).Normal
  /-- The relative Galois quotient is finite. -/
  finite : Finite (K.toSubgroup ⧸ extensionSubgroup K field below)

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- Forget only finiteness from a finite Galois subextension. -/
def toGaloisSubextension (L : FiniteGaloisSubextension K) :
    DegreeData.GaloisSubextension K where
  field := L.field
  below := L.below
  normal := L.normal

/-- Forget normality, retaining the underlying finite abstract extension.
This is the canonical bridge from a finite Galois subextension to the degree
and ramification API. -/
def toFiniteAbstractExtension (L : FiniteGaloisSubextension K) :
    DegreeData.FiniteAbstractExtension G where
  field := L.field
  base := K
  below := L.below
  finiteQuotient := L.finite

/-- The actual finite quotient `G(L/K)`, kept behind a named object
boundary. -/
def extensionQuotient (L : FiniteGaloisSubextension K) : Type u :=
  K.toSubgroup ⧸ extensionSubgroup K L.field L.below

/-- Structural unramifiedness of the underlying finite extension. -/
def IsUnramified (L : FiniteGaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toFiniteAbstractExtension.IsUnramified D

/-- Structural total ramification of the underlying finite extension. -/
def IsTotallyRamified (L : FiniteGaloisSubextension K)
    (D : DegreeData G) : Prop :=
  L.toFiniteAbstractExtension.IsTotallyRamified D

/-- A finite Galois subextension is represented by a normal subgroup. -/
instance extensionSubgroup_normalInstance (L : FiniteGaloisSubextension K) :
    (extensionSubgroup K L.field L.below).Normal :=
  L.normal

/-- The group structure transported across the named finite quotient
boundary. -/
instance extensionQuotient_groupInstance (L : FiniteGaloisSubextension K) :
    Group L.extensionQuotient := by
  change Group
    (K.toSubgroup ⧸ extensionSubgroup K L.field L.below)
  infer_instance

/-- The quotient represented by a finite Galois subextension is finite. -/
instance extensionQuotient_finiteInstance (L : FiniteGaloisSubextension K) :
    Finite L.extensionQuotient :=
  L.finite

/-- Comparison with the quotient presentation used by the underlying group
library. -/
def extensionQuotientMulEquiv (L : FiniteGaloisSubextension K) :
    L.extensionQuotient ≃*
      (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  MulEquiv.refl _

/-- The canonical quotient projection for a finite Galois subextension. -/
def extensionQuotientMk (L : FiniteGaloisSubextension K) :
    K.toSubgroup →* L.extensionQuotient :=
  QuotientGroup.mk' (extensionSubgroup K L.field L.below)

/-- The named finite Galois quotient projection agrees with `QuotientGroup.mk`. -/
@[simp]
theorem extensionQuotientMk_apply (L : FiniteGaloisSubextension K)
    (k : K.toSubgroup) :
    L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k :
        K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  rfl

/-- A quotient representative is trivial exactly when it lies in the extension subgroup. -/
@[simp]
theorem extensionQuotientMk_eq_one_iff (L : FiniteGaloisSubextension K)
    (k : K.toSubgroup) :
    L.extensionQuotientMk k = 1 ↔
      k ∈ extensionSubgroup K L.field L.below := by
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff k).1
    calc
      (QuotientGroup.mk k :
          K.toSubgroup ⧸ extensionSubgroup K L.field L.below) =
          L.extensionQuotientMulEquiv (L.extensionQuotientMk k) :=
        (L.extensionQuotientMk_apply k).symm
      _ = L.extensionQuotientMulEquiv 1 := congrArg L.extensionQuotientMulEquiv h
      _ = 1 := L.extensionQuotientMulEquiv.map_one
  · intro hk
    apply L.extensionQuotientMulEquiv.injective
    rw [L.extensionQuotientMk_apply, L.extensionQuotientMulEquiv.map_one]
    exact (QuotientGroup.eq_one_iff k).2 hk

/-- The canonical projection onto the finite Galois quotient is surjective. -/
theorem extensionQuotientMk_surjective (L : FiniteGaloisSubextension K) :
    Function.Surjective L.extensionQuotientMk := by
  intro q
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
    (extensionSubgroup K L.field L.below) (L.extensionQuotientMulEquiv q)
  refine ⟨k, L.extensionQuotientMulEquiv.injective ?_⟩
  rw [L.extensionQuotientMk_apply]
  exact hk

/-- The finite and non-finite Galois bundles have the same quotient; this
named equivalence is the only public comparison needed by clients. -/
def toGaloisExtensionQuotientMulEquiv (L : FiniteGaloisSubextension K) :
    L.extensionQuotient ≃* L.toGaloisSubextension.extensionQuotient :=
  L.extensionQuotientMulEquiv.trans
    L.toGaloisSubextension.extensionQuotientMulEquiv.symm

/-- Bundling a finite Galois extension preserves its unramified predicate. -/
@[simp]
theorem toGaloisSubextension_isUnramified_iff
    (L : FiniteGaloisSubextension K) (D : DegreeData G) :
    L.toGaloisSubextension.IsUnramified D ↔ L.IsUnramified D :=
  Iff.rfl

/-- Bundling a finite Galois extension preserves its total-ramification predicate. -/
@[simp]
theorem toGaloisSubextension_isTotallyRamified_iff
    (L : FiniteGaloisSubextension K) (D : DegreeData G) :
    L.toGaloisSubextension.IsTotallyRamified D ↔ L.IsTotallyRamified D :=
  Iff.rfl

/-- Transport a total-ramification proof through the finite-to-Galois
forgetful map. -/
theorem isTotallyRamified_toGaloisSubextension
    (L : FiniteGaloisSubextension K) (D : DegreeData G)
    (hL : L.IsTotallyRamified D) :
    L.toGaloisSubextension.IsTotallyRamified D :=
  (L.toGaloisSubextension_isTotallyRamified_iff D).2 hL

/-- Finiteness is transitive in a tower of abstract fields. -/
theorem finite_extension_trans
    {P L K : ClosedSubgroup G}
    (hPL : P.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hPLfinite : Finite
      (L.toSubgroup ⧸ extensionSubgroup L P hPL)]
    [hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Finite (K.toSubgroup ⧸ extensionSubgroup K P (hPL.trans hLK)) := by
  have hPL0 : P.toSubgroup.relIndex L.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite L.toSubgroup _
      (extensionSubgroup L P hPL) hPLfinite
  have hLK0 : L.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (extensionSubgroup K L hLK) hLKfinite
  apply Nat.finite_of_card_ne_zero
  change (extensionSubgroup K P (hPL.trans hLK)).index ≠ 0
  simpa [Subgroup.relIndex] using
    Subgroup.relIndex_ne_zero_trans hPL0 hLK0

/-- A finite extension remains finite over every intermediate field. -/
theorem finite_extension_over_intermediate
    {P M K : ClosedSubgroup G}
    (hPK : P.toSubgroup ≤ K.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    (hPM : P.toSubgroup ≤ M.toSubgroup)
    [hPKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K P hPK)] :
    Finite (M.toSubgroup ⧸ extensionSubgroup M P hPM) := by
  have hPK0 : P.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (extensionSubgroup K P hPK) hPKfinite
  have hPM0 : P.toSubgroup.relIndex M.toSubgroup ≠ 0 := by
    intro hzero
    have hmul := Subgroup.relIndex_mul_relIndex
      P.toSubgroup M.toSubgroup K.toSubgroup hPM hMK
    rw [hzero, zero_mul] at hmul
    exact hPK0 hmul.symm
  apply Nat.finite_of_card_ne_zero
  change (extensionSubgroup M P hPM).index ≠ 0
  simpa [Subgroup.relIndex] using hPM0

/-- The trivial extension `K / K`. -/
def refl (K : ClosedSubgroup G) : FiniteGaloisSubextension K where
  field := K
  below := le_rfl
  normal := by
    have htop : extensionSubgroup K K le_rfl = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact x.2
    rw [htop]
    infer_instance
  finite := by
    have htop : extensionSubgroup K K le_rfl = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact x.2
    rw [htop]
    infer_instance

end FiniteGaloisSubextension

end GroupOnly

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_Construction_MainMultiplicativity_CorrectionSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Correction sums for reciprocity multiplicativity

This file packages the three correction coefficients and action elements,
proves their degree-zero property, and identifies their action-difference sum.
-/

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory
open scoped BigOperators

/-- The corresponding left-action elements are `τ₄,τ₁,τ₄`.
The last action is `τ₄` because the product in the actual `(*)`
identity is `τ₄τ₁`. -/
def frobeniusMultiplicativityCorrectionAction {R : Type*} [Group R]
    (τ₁ τ₄ : R) : Fin 3 → R :=
  ![τ₄, τ₁, τ₄]

end

end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_FieldRepresentation
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.ClassFormation.infiniteNormQuotientAddCommGroup
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.maximalUnramifiedNormClass_eq_zero_iff _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass _root_.ClassFormation.DegreeData.mem_maximalUnramifiedNormSubgroup_iff _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff _root_.ClassFormation.ValuationData.mem_unitAddSubgroup_iff _root_.ClassFormation.ValuationData.oneValue_coe _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.ValuationData.valuationAt_chosenPrimeElement _root_.ClassFormation.finiteNormClass_add _root_.ClassFormation.finiteNormClass_eq_zero_iff _root_.ClassFormation.finiteNormClass_nsmul _root_.ClassFormation.finiteNormClass_sub _root_.ClassFormation.finiteNormClass_zero _root_.ClassFormation.finiteNormQuotientConcreteEquiv_finiteNormClass _root_.ClassFormation.finiteNormQuotientLift_finiteNormClass _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.fixedFieldInclusion_coe _root_.ClassFormation.infiniteNormClass_eq_zero_iff _root_.ClassFormation.infiniteNormQuotientConcreteEquiv_infiniteNormClass _root_.ClassFormation.infiniteNormQuotientLift_infiniteNormClass _root_.ClassFormation.mem_infiniteNormSubgroup_iff _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.relativeNorm_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The invariant carrier in the descended quotient representation is the
actual fixed group `A_L`. -/
def extensionFixedRepresentationEquiv
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    (extensionFixedRepresentation A K L hLK hnormal).V ≃+
      ambientFixedAddSubgroup A L where
  toFun x := ⟨x.1, by
    intro l
    exact x.2 ⟨⟨l.1, hLK l.2⟩, l.2⟩⟩
  invFun a := ⟨a.1, by
    intro s
    let l : L.toSubgroup := ⟨s.1.1, s.2⟩
    change A.ρ s.1.1 a.1 = a.1
    exact a.2 l⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv a := by
    apply Subtype.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl

/--
Establishes the identity `((extensionFixedRepresentationEquiv A K L hLK hnormal a :
ambientFixedAddSubgroup A L) : A.V) = a.1`.
-/
@[simp]
theorem extensionFixedRepresentationEquiv_apply_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) :
    ((extensionFixedRepresentationEquiv A K L hLK hnormal a :
        ambientFixedAddSubgroup A L) : A.V) = a.1 :=
  rfl

/--
Establishes the identity `((extensionFixedRepresentationEquiv A K L hLK hnormal).symm a).1 = a.1`.
-/
@[simp]
theorem extensionFixedRepresentationEquiv_symm_apply_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (a : ambientFixedAddSubgroup A L) :
    ((extensionFixedRepresentationEquiv A K L hLK hnormal).symm a).1 = a.1 :=
  rfl

/-- The quotient action on `A_L` is the same coset action used by the
relative norm. -/
theorem extensionFixedRepresentation_action_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) :
    ((extensionFixedRepresentation A K L hLK hnormal).ρ q a).1 =
      relativeCosetAction A K L hLK
        (extensionFixedRepresentationEquiv A K L hLK hnormal a) q := by
  let := hnormal
  refine Quotient.inductionOn' q ?_
  intro k
  rw [relativeCosetAction_mk]
  rfl

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Reciprocity_IntermediateExtension
attribute [-instance] _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal
attribute [-simp] _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.ValuationData.unitRepresentation_quotient_mk_apply _root_.ClassFormation.extensionFixedRepresentationEquiv_apply_coe _root_.ClassFormation.extensionFixedRepresentationEquiv_symm_apply_coe _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.relativeConjugateCosetEquiv_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- The inverse image in `G_K` of a subgroup of `G(L/K)`. -/
def intermediateSubgroup (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : Subgroup K.toSubgroup := by
  exact S.comap L.extensionQuotientMk

omit [IsTopologicalGroup G] in
/-- Membership in the intermediate subgroup is characterized by membership of
the underlying ambient element. -/
@[simp]
theorem mem_intermediateSubgroup_iff
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (k : K.toSubgroup) :
    k ∈ L.intermediateSubgroup S ↔ L.extensionQuotientMk k ∈ S :=
  Iff.rfl

omit [IsTopologicalGroup G] in
/-- The original `G_L` lies in every inverse-image subgroup. -/
theorem extensionSubgroup_le_intermediateSubgroup
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    extensionSubgroup K L.field L.below ≤ L.intermediateSubgroup S := by
  intro x hx
  apply (L.mem_intermediateSubgroup_iff S x).2
  have hmk : L.extensionQuotientMk x = 1 :=
    (L.extensionQuotientMk_eq_one_iff x).2 hx
  rw [hmk]
  exact S.one_mem

/-- The `G_L`-coset classified by `q ∈ G(L/K)`, defined canonically as a
fiber of the quotient map.  In particular, its public definition does not
choose a representative of `q`. -/
def intermediateCoset (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : Set K.toSubgroup :=
  {x | L.extensionQuotientMk x = q}

/-- A representative-based description used only to prove topological facts
about the canonical quotient fiber. -/
def representativeIntermediateCoset (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : Set K.toSubgroup :=
  (fun x : K.toSubgroup =>
      x * Quotient.out (L.extensionQuotientMulEquiv q)) ''
    (extensionSubgroup K L.field L.below : Set K.toSubgroup)

omit [IsTopologicalGroup G] in
/-- Membership in the canonical coset is equality with its quotient class. -/
theorem mem_intermediateCoset_iff (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) (x : K.toSubgroup) :
    x ∈ L.intermediateCoset q ↔
      L.extensionQuotientMk x = q :=
  Iff.rfl

omit [IsTopologicalGroup G] in
theorem mem_representativeIntermediateCoset_iff
    (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) (x : K.toSubgroup) :
    x ∈ representativeIntermediateCoset L q ↔
      L.extensionQuotientMk x = q := by
  let : (extensionSubgroup K L.field L.below).Normal := L.normal
  constructor
  · rintro ⟨h, hh, rfl⟩
    apply L.extensionQuotientMulEquiv.injective
    rw [L.extensionQuotientMk_apply]
    rw [← Quotient.out_eq' (L.extensionQuotientMulEquiv q)]
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa [div_eq_mul_inv, mul_assoc] using hh
  · intro hx
    have hxout :
        (QuotientGroup.mk' (extensionSubgroup K L.field L.below)) x =
          (QuotientGroup.mk'
            (extensionSubgroup K L.field L.below))
              (Quotient.out (L.extensionQuotientMulEquiv q)) := by
      calc
        (QuotientGroup.mk'
            (extensionSubgroup K L.field L.below)) x =
              L.extensionQuotientMulEquiv (L.extensionQuotientMk x) :=
          (L.extensionQuotientMk_apply x).symm
        _ = L.extensionQuotientMulEquiv q :=
          congrArg L.extensionQuotientMulEquiv hx
        _ = (QuotientGroup.mk'
            (extensionSubgroup K L.field L.below))
              (Quotient.out (L.extensionQuotientMulEquiv q)) :=
          (Quotient.out_eq' (L.extensionQuotientMulEquiv q)).symm
    have hdiv : x / Quotient.out (L.extensionQuotientMulEquiv q) ∈
        extensionSubgroup K L.field L.below :=
      QuotientGroup.eq_iff_div_mem.mp hxout
    refine ⟨x / Quotient.out (L.extensionQuotientMulEquiv q), hdiv, ?_⟩
    simp [div_eq_mul_inv, mul_assoc]

omit [IsTopologicalGroup G] in
theorem intermediateCoset_eq_representativeIntermediateCoset
    (L : FiniteGaloisSubextension K) (q : L.extensionQuotient) :
    L.intermediateCoset q = representativeIntermediateCoset L q := by
  ext x
  exact (mem_representativeIntermediateCoset_iff L q x).symm

omit [IsTopologicalGroup G] in
/-- The inverse image of `S` is literally the finite union of the `G_L`
cosets indexed by the elements of `S`. -/
theorem intermediateSubgroup_eq_iUnion_cosets
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (L.intermediateSubgroup S : Set K.toSubgroup) =
      ⋃ q ∈ (S : Set L.extensionQuotient), L.intermediateCoset q := by
  ext x
  constructor
  · intro hx
    have hxS := (L.mem_intermediateSubgroup_iff S x).1 hx
    refine Set.mem_iUnion₂.mpr ⟨
      L.extensionQuotientMk x, hxS, ?_⟩
    exact (mem_intermediateCoset_iff L _ x).2 rfl
  · intro hx
    rcases Set.mem_iUnion₂.mp hx with ⟨q, hqS, hxq⟩
    apply (L.mem_intermediateSubgroup_iff S x).2
    rw [(mem_intermediateCoset_iff L q x).1 hxq]
    exact hqS

theorem representativeIntermediateCoset_isClosed
    (L : FiniteGaloisSubextension K) (q : L.extensionQuotient) :
    IsClosed (representativeIntermediateCoset L q) := by
  exact isClosedMap_mul_right
    (Quotient.out (L.extensionQuotientMulEquiv q)) _
    (extensionSubgroup_isClosed K L.field L.below)

/-- Every coset in the preceding union is closed: it is the image of the
closed subgroup `G_L ≤ G_K` under right translation. -/
theorem intermediateCoset_isClosed (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : IsClosed (L.intermediateCoset q) := by
  rw [intermediateCoset_eq_representativeIntermediateCoset]
  exact representativeIntermediateCoset_isClosed L q

/-- Closedness of the inverse image, proved by its finite coset
decomposition rather than postulated as a Galois-correspondence property. -/
theorem intermediateSubgroup_isClosed (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    IsClosed (L.intermediateSubgroup S : Set K.toSubgroup) := by
  let : Finite L.extensionQuotient := L.finite
  rw [intermediateSubgroup_eq_iUnion_cosets]
  have hfinite : (S : Set L.extensionQuotient).Finite := Set.toFinite _
  exact hfinite.isClosed_biUnion fun q _ => intermediateCoset_isClosed L q

/-- The closed intermediate field cut out by `S ≤ G(L/K)`. -/
def intermediateField (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : ClosedSubgroup G where
  toSubgroup := (L.intermediateSubgroup S).map K.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      ((fun x : K.toSubgroup => (x : G)) ''
        (L.intermediateSubgroup S : Set K.toSubgroup))
    exact K.isClosed'.isClosedMap_subtype_val _
      (intermediateSubgroup_isClosed L S)

/-- The constructed intermediate field lies over `K`. -/
theorem intermediateField_le_base (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.intermediateField S).toSubgroup ≤ K.toSubgroup := by
  rintro _ ⟨m, hm, rfl⟩
  exact m.property

/-- Pulling the constructed field back to `G_K` recovers exactly the
inverse-image subgroup. -/
theorem extensionSubgroup_intermediateField_eq
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    extensionSubgroup K (L.intermediateField S)
        (L.intermediateField_le_base S) =
      L.intermediateSubgroup S := by
  ext x
  simp [extensionSubgroup, intermediateField]
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := Subtype.ext hxy
    simpa [hyx] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The constructed field is intermediate: `L ≤ M`. -/
theorem field_le_intermediateField (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    L.field.toSubgroup ≤ (L.intermediateField S).toSubgroup := by
  intro x hx
  let xK : K.toSubgroup := ⟨x, L.below hx⟩
  have hxH : xK ∈ extensionSubgroup K L.field L.below :=
    (mem_extensionSubgroup_iff K L.field L.below xK).2 hx
  have hxP : xK ∈ L.intermediateSubgroup S :=
    L.extensionSubgroup_le_intermediateSubgroup S hxH
  exact ⟨xK, hxP, rfl⟩

/-- The extension subgroup for `L/M` is the pullback of `G_L ◁ G_K`
along `G_M → G_K`. -/
theorem extensionSubgroup_over_intermediate_eq_comap
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S) =
      (extensionSubgroup K L.field L.below).comap
        (Subgroup.inclusion (L.intermediateField_le_base S)) := by
  ext x
  rw [mem_extensionSubgroup_iff, Subgroup.mem_comap,
    mem_extensionSubgroup_iff]
  rfl

/-- `L/M` is normal because it is obtained by restricting the normal
subgroup `G_L ◁ G_K` to `G_M`. -/
theorem extensionSubgroup_over_intermediate_normal
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal := by
  rw [extensionSubgroup_over_intermediate_eq_comap]
  infer_instance

/-- The extension subgroup over an intermediate field is normal in the intermediate subgroup. -/
instance extensionSubgroup_over_intermediate_normalInstance
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
  L.extensionSubgroup_over_intermediate_normal S

/-- The lower extension `L/M` is finite. -/
theorem extension_over_intermediate_finite
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    Finite ((L.intermediateField S).toSubgroup ⧸
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S)) := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  exact FiniteGaloisSubextension.finite_extension_over_intermediate
    L.below (L.intermediateField_le_base S)
      (L.field_le_intermediateField S)

/-- The intermediate extension `M/K` is finite, since its subgroup contains
the finite-index subgroup `G_L`. -/
theorem intermediateField_finite
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K (L.intermediateField S)
      (L.intermediateField_le_base S)) := by
  rw [extensionSubgroup_intermediateField_eq]
  let : (extensionSubgroup K L.field L.below).FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
      (extensionSubgroup K L.field L.below) L.finite
  let : (L.intermediateSubgroup S).FiniteIndex :=
    Subgroup.finiteIndex_of_le (L.extensionSubgroup_le_intermediateSubgroup S)
  exact Subgroup.finite_quotient_of_finiteIndex

omit [IsTopologicalGroup G] in
/-- A normal subgroup `S ◁ G(L/K)` has normal inverse image in `G_K`. -/
theorem intermediateSubgroup_normal
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (hS : S.Normal) : (L.intermediateSubgroup S).Normal := by
  let : S.Normal := hS
  exact hS.comap L.extensionQuotientMk

/-- Hence `M/K` is normal whenever `S` is normal. -/
theorem intermediateField_normal
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (hS : S.Normal) :
    (extensionSubgroup K (L.intermediateField S)
      (L.intermediateField_le_base S)).Normal := by
  rw [extensionSubgroup_intermediateField_eq]
  exact L.intermediateSubgroup_normal S hS

/-- The actual finite Galois extension `L/M`. -/
def lowerFiniteGalois (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    FiniteGaloisSubextension (L.intermediateField S) where
  field := L.field
  below := L.field_le_intermediateField S
  normal := L.extensionSubgroup_over_intermediate_normal S
  finite := L.extension_over_intermediate_finite S

/-- If `S` is normal, the actual finite Galois extension `M/K`. -/
def intermediateFiniteGalois (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) (hS : S.Normal) :
    FiniteGaloisSubextension K where
  field := L.intermediateField S
  below := L.intermediateField_le_base S
  normal := L.intermediateField_normal S hS
  finite := L.intermediateField_finite S

/-- Restriction from `G_M` to the subgroup `S ≤ G(L/K)`.  The codomain
membership proof is supplied by the defining inverse-image equation for
`M`. -/
def lowerRestrictionHom (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.intermediateField S).toSubgroup →* S :=
  (L.extensionQuotientMk.comp
      (Subgroup.inclusion (L.intermediateField_le_base S))).codRestrict S
    (by
      intro m
      apply (L.mem_intermediateSubgroup_iff S _).1
      rw [← extensionSubgroup_intermediateField_eq L S]
      exact
        (mem_extensionSubgroup_iff K (L.intermediateField S)
          (L.intermediateField_le_base S)
          (Subgroup.inclusion (L.intermediateField_le_base S) m)).2
          m.property)

/-- The lower restriction homomorphism evaluates by restricting the underlying
ambient automorphism. -/
@[simp]
theorem lowerRestrictionHom_apply_coe (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    ((L.lowerRestrictionHom S m : S) : L.extensionQuotient) =
      L.extensionQuotientMk
        (Subgroup.inclusion (L.intermediateField_le_base S) m) :=
  rfl

/-- Every element of `S` is represented by an element of `G_M`; hence the
restriction map is onto. -/
theorem lowerRestrictionHom_surjective (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    Function.Surjective (L.lowerRestrictionHom S) := by
  intro s
  rcases L.extensionQuotientMk_surjective s.1 with ⟨k, hk⟩
  have hkP : k ∈ L.intermediateSubgroup S := by
    apply (L.mem_intermediateSubgroup_iff S k).2
    rw [hk]
    exact s.property
  let m : (L.intermediateField S).toSubgroup :=
    ⟨k.1, ⟨k, hkP, rfl⟩⟩
  refine ⟨m, ?_⟩
  apply Subtype.ext
  rw [lowerRestrictionHom_apply_coe]
  change L.extensionQuotientMk k = s
  exact hk

/-- The kernel of restriction is exactly `G_L` viewed inside `G_M`. -/
theorem lowerRestrictionHom_ker (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    MonoidHom.ker (L.lowerRestrictionHom S) =
      extensionSubgroup (L.intermediateField S) L.field
        (L.field_le_intermediateField S) := by
  ext m
  rw [MonoidHom.mem_ker, mem_extensionSubgroup_iff]
  constructor
  · intro hm
    let mK : K.toSubgroup :=
      ⟨m.1, L.intermediateField_le_base S m.property⟩
    have hq :
        ((L.lowerRestrictionHom S m : S) : L.extensionQuotient) = 1 :=
      congrArg Subtype.val hm
    rw [lowerRestrictionHom_apply_coe] at hq
    have hH : mK ∈ extensionSubgroup K L.field L.below :=
      (L.extensionQuotientMk_eq_one_iff mK).1 hq
    exact (mem_extensionSubgroup_iff K L.field L.below
      mK).1 hH
  · intro hm
    let mK : K.toSubgroup :=
      ⟨m.1, L.intermediateField_le_base S m.property⟩
    have hH : mK ∈ extensionSubgroup K L.field L.below :=
      (mem_extensionSubgroup_iff K L.field L.below mK).2 hm
    have hq : L.extensionQuotientMk mK = 1 :=
      (L.extensionQuotientMk_eq_one_iff mK).2 hH
    apply Subtype.ext
    rw [lowerRestrictionHom_apply_coe]
    exact hq

/-- The first actual Galois-group identification used:
`G(L/M) ≃ S`. -/
noncomputable def lowerQuotientEquiv (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.lowerFiniteGalois S).extensionQuotient ≃* S := by
  letI : (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  exact (L.lowerFiniteGalois S).extensionQuotientMulEquiv.trans
    ((QuotientGroup.quotientMulEquivOfEq
        (L.lowerRestrictionHom_ker S).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (L.lowerRestrictionHom S) (L.lowerRestrictionHom_surjective S)))

/-- Representative formula for `G(L/M) ≃ S`. -/
@[simp]
theorem lowerQuotientEquiv_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    L.lowerQuotientEquiv S
        ((L.lowerFiniteGalois S).extensionQuotientMk m) =
      L.lowerRestrictionHom S m := by
  let : (extensionSubgroup (L.intermediateField S) L.field
      (L.field_le_intermediateField S)).Normal :=
    L.extensionSubgroup_over_intermediate_normal S
  change
    ((QuotientGroup.quotientMulEquivOfEq
        (L.lowerRestrictionHom_ker S).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (L.lowerRestrictionHom S) (L.lowerRestrictionHom_surjective S)))
      (QuotientGroup.mk m) = L.lowerRestrictionHom S m
  rfl

/-- The same representative formula after forgetting the subtype `S`; this
is the form used when composing restriction maps in the reduction diagram. -/
@[simp]
theorem lowerQuotientEquiv_mk_coe (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    ((L.lowerQuotientEquiv S
        ((L.lowerFiniteGalois S).extensionQuotientMk m) : S) :
          L.extensionQuotient) =
      L.extensionQuotientMk
        ⟨m.1, L.intermediateField_le_base S m.property⟩ := by
  rw [lowerQuotientEquiv_mk, lowerRestrictionHom_apply_coe]
  apply congrArg L.extensionQuotientMk
  exact Subtype.ext (by rfl)

omit [IsTopologicalGroup G] in
/-- Mapping the inverse image of `S` back to `G(L/K)` recovers `S`
itself. -/
theorem intermediateSubgroup_map_quotient_eq
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (L.intermediateSubgroup S).map L.extensionQuotientMk = S := by
  exact Subgroup.map_comap_eq_self_of_surjective
    L.extensionQuotientMk_surjective S

/-- The field represented by a normal intermediate subgroup is a normal subextension. -/
instance intermediateField_normalInstance
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    [hS : S.Normal] :
    (extensionSubgroup K (L.intermediateField S)
      (L.intermediateField_le_base S)).Normal :=
  L.intermediateField_normal S hS

/-- The third-isomorphism identification used in the normal-subextension
diagram: `G(L/K)/S ≃ G(M/K)`. -/
def upperQuotient (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : Type _ :=
  L.extensionQuotient ⧸ S

/-- The upper quotient over an intermediate field carries its canonical group structure. -/
instance upperQuotient_groupInstance (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    Group (L.upperQuotient S) := by
  change Group (L.extensionQuotient ⧸ S)
  infer_instance

/-- Comparison with the group-library presentation of the upper quotient. -/
def upperQuotientMulEquiv (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.upperQuotient S ≃* (L.extensionQuotient ⧸ S) :=
  MulEquiv.refl _

/-- The canonical projection to the named upper quotient. -/
def upperQuotientMk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.extensionQuotient →* L.upperQuotient S :=
  QuotientGroup.mk' S

omit [IsTopologicalGroup G] in
/-- The named upper quotient projection agrees with the underlying quotient-group projection. -/
@[simp]
theorem upperQuotientMk_apply (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal]
    (q : L.extensionQuotient) :
    L.upperQuotientMulEquiv S (L.upperQuotientMk S q) =
      (QuotientGroup.mk q : L.extensionQuotient ⧸ S) :=
  rfl

/-- The third-isomorphism identification, with both source and target kept
behind their named finite-Galois quotient boundaries. -/
noncomputable def upperQuotientEquiv (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.upperQuotient S ≃*
      (L.intermediateFiniteGalois S inferInstance).extensionQuotient := by
  let H := extensionSubgroup K L.field L.below
  let P := L.intermediateSubgroup S
  let π : K.toSubgroup →* L.extensionQuotient := L.extensionQuotientMk
  have hHP : H ≤ P := L.extensionSubgroup_le_intermediateSubgroup S
  have hmap : P.map π = S := L.intermediateSubgroup_map_quotient_eq S
  have hupper : extensionSubgroup K (L.intermediateField S)
      (L.intermediateField_le_base S) = P :=
    L.extensionSubgroup_intermediateField_eq S
  letI : H.Normal := L.normal
  letI : P.Normal := L.intermediateSubgroup_normal S inferInstance
  letI : (P.map π).Normal := by rw [hmap]; infer_instance
  exact (L.upperQuotientMulEquiv S).trans
    ((QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      ((QuotientGroup.quotientQuotientEquivQuotient H P hHP).trans
        ((QuotientGroup.quotientMulEquivOfEq hupper.symm).trans
          (L.intermediateFiniteGalois S inferInstance).extensionQuotientMulEquiv.symm)))

/-- Representative formula for `G(L/K)/S ≃ G(M/K)`. -/
@[simp]
theorem upperQuotientEquiv_mk_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] (k : K.toSubgroup) :
    L.upperQuotientEquiv S
        (L.upperQuotientMk S (L.extensionQuotientMk k)) =
      (L.intermediateFiniteGalois S inferInstance).extensionQuotientMk k := by
  let H := extensionSubgroup K L.field L.below
  let P := L.intermediateSubgroup S
  let π : K.toSubgroup →* L.extensionQuotient := L.extensionQuotientMk
  have hHP : H ≤ P := L.extensionSubgroup_le_intermediateSubgroup S
  have hmap : P.map π = S := L.intermediateSubgroup_map_quotient_eq S
  have hupper : extensionSubgroup K (L.intermediateField S)
      (L.intermediateField_le_base S) = P :=
    L.extensionSubgroup_intermediateField_eq S
  let : H.Normal := L.normal
  let : P.Normal := L.intermediateSubgroup_normal S inferInstance
  let : (P.map π).Normal := by rw [hmap]; infer_instance
  change
    (L.intermediateFiniteGalois S
        inferInstance).extensionQuotientMulEquiv.symm
      ((QuotientGroup.quotientMulEquivOfEq hupper.symm)
        ((QuotientGroup.quotientQuotientEquivQuotient H P hHP)
          ((QuotientGroup.quotientMulEquivOfEq hmap.symm)
            (QuotientGroup.mk (L.extensionQuotientMk k))))) =
      (L.intermediateFiniteGalois S inferInstance).extensionQuotientMk k
  apply
    (L.intermediateFiniteGalois S inferInstance).extensionQuotientMulEquiv.injective
  refine ((L.intermediateFiniteGalois S
    inferInstance).extensionQuotientMulEquiv.apply_symm_apply _).trans ?_
  refine Eq.trans ?_
    ((L.intermediateFiniteGalois S inferInstance).extensionQuotientMk_apply k).symm
  have hmk :
      L.extensionQuotientMk k =
        (QuotientGroup.mk k : K.toSubgroup ⧸ H) := by
    change L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k : K.toSubgroup ⧸ H)
    exact L.extensionQuotientMk_apply k
  have hthird :
      (QuotientGroup.quotientQuotientEquivQuotient H P hHP)
          ((QuotientGroup.mk
            (QuotientGroup.mk k : K.toSubgroup ⧸ H)) :
              (K.toSubgroup ⧸ H) ⧸
                P.map (QuotientGroup.mk' H)) =
        (QuotientGroup.mk k : K.toSubgroup ⧸ P) := by
    exact
      QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk H P hHP k
  calc
    _ =
        (QuotientGroup.quotientMulEquivOfEq hupper.symm)
          ((QuotientGroup.quotientQuotientEquivQuotient H P hHP)
            (QuotientGroup.mk (L.extensionQuotientMk k))) :=
      congrArg
        (fun q => (QuotientGroup.quotientMulEquivOfEq hupper.symm)
          ((QuotientGroup.quotientQuotientEquivQuotient H P hHP) q))
        (QuotientGroup.quotientMulEquivOfEq_mk hmap.symm (L.extensionQuotientMk k))
    _ =
        (QuotientGroup.quotientMulEquivOfEq hupper.symm)
          ((QuotientGroup.quotientQuotientEquivQuotient H P hHP)
            (QuotientGroup.mk (QuotientGroup.mk k : K.toSubgroup ⧸ H))) :=
      congrArg
        (fun q : K.toSubgroup ⧸ H =>
          (QuotientGroup.quotientMulEquivOfEq hupper.symm)
            ((QuotientGroup.quotientQuotientEquivQuotient H P hHP)
              (QuotientGroup.mk q))) hmk
    _ =
        (QuotientGroup.quotientMulEquivOfEq hupper.symm)
          (QuotientGroup.mk k : K.toSubgroup ⧸ P) :=
      congrArg (QuotientGroup.quotientMulEquivOfEq hupper.symm) hthird
    _ = _ := QuotientGroup.quotientMulEquivOfEq_mk hupper.symm k

end FiniteGaloisSubextension

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_LocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Local compactness of the idele group

The topology on the finite ideles is the restricted-product topology from
`AlgebraicNumberTheory.Idele.Topology`.  We prove local compactness by showing
that every finite completion is proper, that its integral unit group is
compact, and then applying the restricted-product theorem.
-/

open scoped NumberField RestrictedProduct Valued
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

/-- An element integral at a finite place can be approximated by an
algebraic integer to positive valuation. -/
theorem exists_ringOfIntegers_approximation
    (v : HeightOneSpectrum (𝓞 K)) (y : K)
    (hy : v.valuation K y ≤ 1) :
    ∃ r : 𝓞 K, v.valuation K (y - algebraMap (𝓞 K) K r) < 1 := by
  let : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hy' : y ∈ v.valuationSubringAtPrime K := by
    rw [v.valuationSubringAtPrime_eq_valuationSubring]
    exact hy
  let y' : v.valuationSubringAtPrime K := ⟨y, hy'⟩
  obtain ⟨⟨a, d⟩, had⟩ := IsLocalization.surj v.asIdeal.primeCompl y'
  have hd : d.1 ∉ v.asIdeal := d.2
  have hdmk : Ideal.Quotient.mk v.asIdeal d.1 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk v.asIdeal a /
      Ideal.Quotient.mk v.asIdeal d.1)
  refine ⟨r, ?_⟩
  have hard : a - r * d.1 ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub, map_mul, hr]
    field_simp
    simp
  have hvalard :
      v.valuation K (algebraMap (𝓞 K) K (a - r * d.1)) < 1 :=
    (v.valuation_lt_one_iff_mem (K := K) (a - r * d.1)).2 hard
  have hdval : v.valuation K (algebraMap (𝓞 K) K d.1) = 1 := by
    exact le_antisymm (v.valuation_le_one d.1)
      (not_lt.mp ((v.valuation_lt_one_iff_mem (K := K) d.1).not.mpr hd))
  have hadK :
      y * algebraMap (𝓞 K) K d.1 = algebraMap (𝓞 K) K a := by
    exact congrArg Subtype.val had
  rw [← mul_lt_mul_iff_right₀ (show
    0 < v.valuation K (algebraMap (𝓞 K) K d.1) by simp [hdval])]
  rw [← map_mul, mul_sub, mul_comm _ y, hadK, mul_comm _ (algebraMap (𝓞 K) K r),
    ← map_mul, ← map_sub, hdval, mul_one]
  exact hvalard

namespace GlobalClassFieldTheory.ClassFieldAxiom

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The residue field of the adic completion at `v` is the global
ring-of-integers quotient by `v`. -/
noncomputable def ringOfIntegersQuotientEquivAdicResidueField
    (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 K ⧸ v.asIdeal) ≃+*
      Valued.ResidueField (v.adicCompletion K) := by
  let integerMap :
      𝓞 K →+* Valued.integer (v.adicCompletion K) := {
    toFun r :=
      ⟨algebraMap (𝓞 K) (v.adicCompletion K) r, by
        change
          Valued.v
            (algebraMap
              (𝓞 K) (v.adicCompletion K) r) ≤ 1
        rw [show
          Valued.v
              (algebraMap
                (𝓞 K) (v.adicCompletion K) r) =
            v.valuation K
              (algebraMap (𝓞 K) K r) from
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation
            (v := v) r]
        exact v.valuation_le_one r⟩
    map_one' := by
      ext
      simp
    map_mul' _ _ := by
      ext
      simp
    map_zero' := by
      ext
      simp
    map_add' _ _ := by
      ext
      simp
  }
  let residueMap :
      𝓞 K →+*
        Valued.ResidueField (v.adicCompletion K) :=
    (IsLocalRing.residue
      (Valued.integer
        (v.adicCompletion K))).comp integerMap
  have hker :
      RingHom.ker residueMap = v.asIdeal := by
    ext r
    change residueMap r = 0 ↔ r ∈ v.asIdeal
    change
      IsLocalRing.residue
          (Valued.integer (v.adicCompletion K))
          (integerMap r) = 0 ↔
        r ∈ v.asIdeal
    rw [IsLocalRing.residue_eq_zero_iff]
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit (integerMap r) ↔ r ∈ v.asIdeal
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    change
      Valued.v
          (algebraMap
            (𝓞 K) (v.adicCompletion K) r) < 1 ↔
        r ∈ v.asIdeal
    rw [show
      Valued.v
          (algebraMap
            (𝓞 K) (v.adicCompletion K) r) =
        v.valuation K
          (algebraMap (𝓞 K) K r) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation
        (v := v) r]
    exact v.valuation_lt_one_iff_mem (K := K) r
  have hsur : Function.Surjective residueMap := by
    intro z
    obtain ⟨x, hx⟩ :=
      (IsLocalRing.residue_surjective
        (R :=
          Valued.integer
            (v.adicCompletion K))) z
    obtain ⟨y, hy⟩ :=
      (v.denseRange_algebraMap K).exists_dist_lt
        (x : v.adicCompletion K) zero_lt_one
    have hxy :
        Valued.v
            ((x : v.adicCompletion K) -
              algebraMap K
                (v.adicCompletion K) y) < 1 := by
      rw [← Valued.toNormedField.norm_lt_one_iff]
      simpa only [dist_eq_norm] using hy
    have hy_integral : v.valuation K y ≤ 1 := by
      rw [show
        v.valuation K y =
          Valued.v
            (algebraMap K
              (v.adicCompletion K) y) from
        (HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
          (v := v) y).symm]
      rw [show
        algebraMap K (v.adicCompletion K) y =
          (x : v.adicCompletion K) -
            ((x : v.adicCompletion K) -
              algebraMap K
                (v.adicCompletion K) y) by
        ring]
      exact Valued.v.map_sub_le x.2 hxy.le
    obtain ⟨r, hyr⟩ :=
      _root_.exists_ringOfIntegers_approximation
        K v y hy_integral
    have hyr' :
        Valued.v
            (algebraMap K
                (v.adicCompletion K) y -
              algebraMap (𝓞 K)
                (v.adicCompletion K) r) < 1 := by
      rw [IsScalarTower.algebraMap_apply
        (𝓞 K) K, ← map_sub]
      rw [show
        Valued.v
            (algebraMap K
              (v.adicCompletion K)
              (y - algebraMap (𝓞 K) K r)) =
          v.valuation K
            (y - algebraMap (𝓞 K) K r) from
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
          (v := v)
          (y - algebraMap (𝓞 K) K r)]
      exact hyr
    have hxr :
        Valued.v
            ((x : v.adicCompletion K) -
              algebraMap (𝓞 K)
                (v.adicCompletion K) r) < 1 := by
      rw [show
        (x : v.adicCompletion K) -
            algebraMap (𝓞 K)
              (v.adicCompletion K) r =
          ((x : v.adicCompletion K) -
              algebraMap K
                (v.adicCompletion K) y) +
            (algebraMap K
                (v.adicCompletion K) y -
              algebraMap (𝓞 K)
                (v.adicCompletion K) r) by
        ring]
      exact Valued.v.map_add_lt hxy hyr'
    refine ⟨r, ?_⟩
    rw [← hx]
    change
      IsLocalRing.residue
          (Valued.integer
            (v.adicCompletion K))
          (integerMap r) =
        IsLocalRing.residue
          (Valued.integer
            (v.adicCompletion K)) x
    apply sub_eq_zero.mp
    rw [← map_sub, IsLocalRing.residue_eq_zero_iff]
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit (integerMap r - x)
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    change
      Valued.v
          ((integerMap r : v.adicCompletion K) -
            (x : v.adicCompletion K)) < 1
    rw [Valued.v.map_sub_swap]
    exact hxr
  exact
    (Ideal.quotEquivOfEq hker).symm.trans
      (RingHom.quotientKerEquivOfSurjective hsur)

end GlobalClassFieldTheory.ClassFieldAxiom

/-- The residue field of a number-field completion at a finite place is
finite. -/
theorem finite_adicCompletion_residueField
    (v : HeightOneSpectrum (𝓞 K)) :
    Finite (Valued.ResidueField (v.adicCompletion K)) := by
  let : Finite (𝓞 K ⧸ v.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Finite.of_equiv (𝓞 K ⧸ v.asIdeal)
    (GlobalClassFieldTheory.ClassFieldAxiom.ringOfIntegersQuotientEquivAdicResidueField
      (K := K) v).toEquiv

/-- Every nonarchimedean completion of a number field is a proper metric
space. -/
instance adicCompletionProperSpace
    (v : HeightOneSpectrum (𝓞 K)) :
    ProperSpace (v.adicCompletion K) := by
  apply
    Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
  refine ⟨inferInstance, ?_, finite_adicCompletion_residueField K v⟩
  change IsDiscreteValuationRing (v.adicCompletionIntegers K)
  infer_instance
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ValuativeExtension
attribute [-instance] _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-!
# Valuative extensions

Records when the valuation ring of an extension field is integral over the
base valuation ring, the hypothesis needed to restrict field norms integrally.
-/

set_option autoImplicit false

namespace Valuation

/-- A nontrivial valuation stays nontrivial after passing to any valuation
which extends it along an algebra map. -/
theorem IsNontrivial.of_hasExtension
    {R A ΓR ΓA : Type*}
    [CommRing R] [Ring A]
    [LinearOrderedCommMonoidWithZero ΓR]
    [LinearOrderedCommMonoidWithZero ΓA]
    [Algebra R A]
    (vR : Valuation R ΓR) (vA : Valuation A ΓA)
    [vR.IsNontrivial] [vR.HasExtension vA] :
    vA.IsNontrivial := {
  exists_val_nontrivial := by
    rcases Valuation.IsNontrivial.exists_val_nontrivial
        (v := vR) with ⟨x, hx0, hx1⟩
    refine ⟨algebraMap R A x, ?_, ?_⟩
    · intro h
      have hm :
          vA (algebraMap R A x) =
            vA (algebraMap R A 0) := by
        simpa using h
      exact hx0 (by
        simpa using
          ((HasExtension.val_map_eq_iff vR vA x 0).1 hm))
    · intro h
      have hm :
          vA (algebraMap R A x) =
            vA (algebraMap R A 1) := by
        simpa using h
      exact hx1 (by
        simpa using
          ((HasExtension.val_map_eq_iff vR vA x 1).1 hm)) }

end Valuation
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ResidueExtension
attribute [-instance] _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-!
# Residue extensions

Constructs the maps induced on valuation rings, residue fields, and residue
units by a valued extension, with degree, trace, norm, and Frobenius results.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The residue-field automorphism group has order the finite residue-field
extension degree. -/
theorem residueAlgEquiv_card_eq_finrank (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) = Module.finrank 𝓀[K] 𝓀[L] :=
  IsGalois.card_aut_eq_finrank (F := 𝓀[K]) (E := 𝓀[L])

/-- The mathlib inertia degree of the maximal ideals agrees with the concrete
degree of the canonical residue-field extension supplied by a valuation
extension. -/
theorem maximalIdeal_inertiaDeg_eq_residue_finrank (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    (𝓂[L] : Ideal 𝒪[L]).inertiaDeg 𝒪[K] =
      Module.finrank 𝓀[K] 𝓀[L] := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L])]
  rfl

/-- The actual ramification index and inertia degree of the valuation-integer
ring extension satisfy the local ramification identity. -/
theorem maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    Ideal.ramificationIdx' (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) *
      (𝓂[L] : Ideal 𝒪[L]).inertiaDeg 𝒪[K] =
        Module.finrank K L := by
  classical
  have := FaithfulSMul.of_field_isFractionRing 𝒪[K] 𝒪[L] K L
  have hp := IsDiscreteValuationRing.not_a_field 𝒪[K]
  have hprimes := IsLocalRing.primesOver_eq (A := 𝒪[L]) hp
  have hq (q : (𝓂[K] : Ideal 𝒪[K]).primesOver 𝒪[L]) :
      (q : Ideal 𝒪[L]) = 𝓂[L] :=
    Set.mem_singleton_iff.mp (hprimes ▸ q.property)
  let : Unique ((𝓂[K] : Ideal 𝒪[K]).primesOver 𝒪[L]) :=
    { default := ⟨𝓂[L], hprimes ▸ Set.mem_singleton _⟩
      uniq := fun q => Subtype.ext (Set.mem_singleton_iff.mp (hprimes ▸ q.property)) }
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp,
    IsFractionRing.finrank_eq 𝒪[K] K 𝒪[L] L]
  simpa only [Fintype.sum_unique, hq] using
    (Ideal.sum_ramification_inertia_eq_finrank (𝓂[K] : Ideal 𝒪[K]) 𝒪[L])

/-- The local ramification identity with the inertia degree rewritten as the
finite-dimensional degree of the canonical residue-field extension. -/
theorem maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] :
    Ideal.ramificationIdx' (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) *
      Module.finrank 𝓀[K] 𝓀[L] =
        Module.finrank K L := by
  rw [← maximalIdeal_inertiaDeg_eq_residue_finrank K L]
  exact maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank K L

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ValuedTopology
attribute [-instance] _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Valued-field topology and the induced valuative relation

This file records the topology bridge used when a nonarchimedean norm is
turned into a `ValuativeRel`: the topology already carried by a nontrivially
valued field is the valuative topology for that induced relation.
-/

noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel

universe u v

/-- The topology of a nontrivially valued field is valuative for the
valuative relation induced by its distinguished valuation. -/
theorem isValuativeTopology_of_valued_ofValuation
    (F : Type u) (Γ : Type v)
    [Field F] [LinearOrderedCommGroupWithZero Γ]
    [MulArchimedean Γ] [Valued F Γ]
    [Valuation.IsNontrivial (Valued.v : Valuation F Γ)] :
    letI := ValuativeRel.ofValuation (Valued.v : Valuation F Γ)
    IsValuativeTopology F := by
  let v : Valuation F Γ := Valued.v
  let : ValuativeRel F := ValuativeRel.ofValuation v
  let : v.Compatible := Valuation.Compatible.ofValuation v
  let : ValuativeRel.IsNontrivial F :=
    (ValuativeRel.isNontrivial_iff_isNontrivial v).2 inferInstance
  apply IsValuativeTopology.of_zero
  intro s
  rw [Valued.mem_nhds_zero]
  constructor
  · rintro ⟨δ, hδ⟩
    refine
      ⟨δ.mapEquiv
          (ValuativeRel.ValueGroupWithZero.orderMonoidIso v).symm, ?_⟩
    intro z hz
    apply hδ
    exact
      (ValuativeRel.valuation_lt_symm_orderMonoidIso
        v (δ : MonoidWithZeroHom.ValueGroup₀ (.ofClass v)) z).1
        (by simpa using hz)
  · rintro ⟨γ, hγ⟩
    refine
      ⟨γ.mapEquiv
          (ValuativeRel.ValueGroupWithZero.orderMonoidIso v), ?_⟩
    intro z hz
    apply hγ
    have hz' :
        v.restrict z <
          (ValuativeRel.ValueGroupWithZero.orderMonoidIso v)
            (γ : ValuativeRel.ValueGroupWithZero F) := by
      exact hz
    exact
      (ValuativeRel.restrict_lt_orderMonoidIso
        v (γ : ValuativeRel.ValueGroupWithZero F) z).1 hz'

end LocalFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormApproximation_FinitePlaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The canonical dense embedding used to compare the absolute-value
completion at `v` with the concrete adic completion. -/
noncomputable def finitePlaceCompletionBaseMap
    (v : HeightOneSpectrum (𝓞 K)) :
    WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) →+*
      v.adicCompletion K :=
  (FinitePlace.embedding v).comp
    (WithAbs.equiv
      (NumberField.HeightOneSpectrum.adicAbv K v)).toRingHom

@[simp]
theorem finitePlaceCompletionBaseMap_apply
    (v : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K v)) :
    finitePlaceCompletionBaseMap v x =
      FinitePlace.embedding v
        (WithAbs.equiv
          (NumberField.HeightOneSpectrum.adicAbv K v) x) :=
  rfl

theorem finitePlaceCompletionBaseMap_norm
    (v : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K v)) :
    ‖finitePlaceCompletionBaseMap v x‖ = ‖x‖ := by
  rw [finitePlaceCompletionBaseMap_apply,
    FinitePlace.norm_embedding]
  rfl

/-- The base embedding is an isometry. -/
theorem finitePlaceCompletionBaseMap_isometry
    (v : HeightOneSpectrum (𝓞 K)) :
    Isometry (finitePlaceCompletionBaseMap v) :=
  AddMonoidHomClass.isometry_of_norm _
    (finitePlaceCompletionBaseMap_norm v)

/-- Extension of the base embedding to the absolute-value completion. -/
noncomputable def finitePlaceCompletionRingHom
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion →+*
      v.adicCompletion K :=
  UniformSpace.Completion.extensionHom
    (finitePlaceCompletionBaseMap v)
    (finitePlaceCompletionBaseMap_isometry v).continuous

@[simp]
theorem finitePlaceCompletionRingHom_coe
    (v : HeightOneSpectrum (𝓞 K))
    (x : WithAbs
      (NumberField.HeightOneSpectrum.adicAbv K v)) :
    finitePlaceCompletionRingHom v
        (x :
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion) =
      finitePlaceCompletionBaseMap v x :=
  UniformSpace.Completion.extensionHom_coe
    (finitePlaceCompletionBaseMap v)
    (finitePlaceCompletionBaseMap_isometry v).continuous x

theorem finitePlaceCompletionRingHom_isometry
    (v : HeightOneSpectrum (𝓞 K)) :
    Isometry (finitePlaceCompletionRingHom v) :=
  (finitePlaceCompletionBaseMap_isometry v).completion_extension

/-- The completed comparison map is onto the concrete adic
completion. -/
theorem finitePlaceCompletionRingHom_surjective
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (finitePlaceCompletionRingHom v) := by
  let f := finitePlaceCompletionRingHom v
  have hrangeClosed : IsClosed (Set.range f) :=
    (finitePlaceCompletionRingHom_isometry v).isClosedEmbedding.isClosed_range
  have hdense :
      DenseRange (algebraMap K (v.adicCompletion K)) :=
    v.denseRange_algebraMap K
  have hrange :
      Set.range (algebraMap K (v.adicCompletion K)) ⊆
        Set.range f := by
    rintro _ ⟨x, rfl⟩
    let x' : WithAbs
        (NumberField.HeightOneSpectrum.adicAbv K v) :=
      (WithAbs.equiv
        (NumberField.HeightOneSpectrum.adicAbv K v)).symm x
    refine
      ⟨(x' :
          (NumberField.HeightOneSpectrum.adicAbv K v).Completion),
        ?_⟩
    rw [finitePlaceCompletionRingHom_coe]
    rfl
  intro x
  have hx :
      x ∈ closure
        (Set.range (algebraMap K (v.adicCompletion K))) := by
    rw [hdense.closure_range]
    trivial
  exact closure_minimal hrange hrangeClosed hx

/-- The two concrete models of `K_v` are canonically isomorphic. -/
noncomputable def finitePlaceCompletionRingEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion ≃+*
      v.adicCompletion K :=
  RingEquiv.ofBijective (finitePlaceCompletionRingHom v)
    ⟨(finitePlaceCompletionRingHom_isometry v).injective,
      finitePlaceCompletionRingHom_surjective v⟩

/-- The preceding ring equivalence, with its native topologies. -/
noncomputable def finitePlaceCompletionContinuousMulEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completion ≃ₜ*
      v.adicCompletion K where
  __ := (finitePlaceCompletionRingEquiv v).toMulEquiv
  continuous_toFun :=
    (finitePlaceCompletionRingHom_isometry v).continuous
  continuous_invFun :=
    ((finitePlaceCompletionRingHom_isometry v).right_inv
      (finitePlaceCompletionRingEquiv v).right_inv).continuous

/-- The induced topological multiplicative equivalence on unit
groups. -/
noncomputable def finitePlaceCompletionUnitsContinuousMulEquiv
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).Completionˣ ≃ₜ*
      (v.adicCompletion K)ˣ :=
  Units.mapContinuousMulEquiv
    (finitePlaceCompletionContinuousMulEquiv v)
end
end

section
-- module Solutions.OAIQ244_DUKE.Definitions_FrobeniusAndHilbertClassFields_ArithmeticFrobeniusAt
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option autoImplicit false

/-!
# Arithmetic Frobenius at a finite prime
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- Mathlib's chosen arithmetic Frobenius lift at a finite prime of the
extension field.  At a ramified prime such a lift need not be unique. -/
def arithmeticFrobeniusAt
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    (w : HeightOneSpectrum (𝓞 L)) : L ≃ₐ[K] L :=
  arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w.asIdeal

end ClassFieldTheory
end
end


