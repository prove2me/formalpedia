-- Prove2me | Definitions.Def_OAIQ244Duke015
-- name    : OAIQ244Duke015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:16:46.024184+00:00
-- url     : https://prove2.me/theorems/10fc9282-c331-4d7e-8afc-6fb5691a5890
-- title:
--   Definitions bundle OAIQ244Duke015 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 192 declarations of OpenAI's Lean: 63 definitions, 3 instances and 126 theorems. The definitions and types are `AlgebraicNumberTheory.Valuations.LocalizedCompletion`, `AlgebraicNumberTheory.Valuations.henselFactorization_initialPrefixState_of_factor`, `BaseChangedRelativeAdeleRing`, `ClassFormation.DegreeData.frobeniusClosureDegree`, `IntermediateClassNormQuotient`, `LocalClassFieldTheory.conjugateCompletionRingEquiv`, `LocalClassFieldTheory.conjugateWithAbsRingEquiv`, `LocalClassFieldTheory.inducedRightCosetCoordinates`, `LocalClassFieldTheory.localTensorUnitsAction`, `LocalFieldTheory.NormQuotient`, `LocalFieldTheory.galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure`, `LocalFieldTheory.galoisGroupIntegerRingEquivHomOfIsIntegralClosure`, `LocalFieldTheory.galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure`, `LocalFieldTheory.galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure`, `LocalFieldTheory.galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure`, `LocalFieldTheory.galoisGroupMaximalIdealInertiaOfIsIntegralClosure`, `LocalFieldTheory.galoisGroupMaximalIdealStabilizerHomOfIsIntegralClosure`, `LocalFieldTheory.galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure`, `LocalFieldTheory.galoisGroupResidueStabilizerHomOfIsIntegralClosure`, `LocalFieldTheory.integerUnitsModPrincipalUnitsMapOfValuationExtension`, `LocalFieldTheory.localNormSubgroup`, `LocalFieldTheory.maximalIdealPowMapOfUnramifiedValuation`, `LocalFieldTheory.maximalIdealPowMulUniformizerPowMap`, `LocalFieldTheory.maximalIdealPowSuccQuotMulUniformizerPowMap`, `LocalFieldTheory.normClass`, `LocalFieldTheory.normQuotientConcreteEquiv`, `LocalFieldTheory.normQuotientLift`, `LocalFieldTheory.principalUnitsMapOfUnramifiedValuation`, `LocalFieldTheory.principalUnitsSuccQuotAddEquivResidueOfIrreducible`, `LocalFieldTheory.principalUnitsSuccQuotMapOfUnramifiedValuation`, `LocalFieldTheory.principalUnitsSuccQuotUniformizerCoord`, `LocalFieldTheory.principalUnitsSuccQuotUniformizerCoordAddHom`, `LocalFieldTheory.residueAddEquivMaximalIdealPowSuccQuotOfIrreducible`, `LocalFieldTheory.residueLinearEquivMaximalIdealPowSuccQuotOfIrreducible`, `LocalInductionInternal.baseValuativeRel`, `LocalInductionInternal.baseValued`, `TowerCompositeClassNormQuotient`, `TowerRelativeIdeleGroup`, `TowerRelativeIdeleGroup.ClassGroup`, `TowerRelativeIdeleGroup.classGroupEquiv` and 23 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AbstractClassFieldTheory_Degree_FrobeniusFixedField`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice`, `AlgebraicNumberTheory_Adele_IntegralTensorSupport_LocalTensorDecomposition`, `AlgebraicNumberTheory_Completion_ChosenLocalization`, `AlgebraicNumberTheory_Completion_LocalizedValuation`, `AlgebraicNumberTheory_Idele_ClassGroup_BaseChange`, `AlgebraicNumberTheory_Idele_ClassGroup_Tower`, `AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_LocalInduction_Spine`, `AlgebraicNumberTheory_Idele_Extension_GaloisNorm`, `AlgebraicNumberTheory_Idele_Extension_LocalComponent`, `AlgebraicNumberTheory_Idele_Relative_Support`, `LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor`, `LocalField_NonarchimedeanLocalField_FiniteUnramified`, `LocalField_NonarchimedeanLocalField_GaloisIntegerRing`, `LocalField_NonarchimedeanLocalField_IdealQuotients`, `LocalField_NonarchimedeanLocalField_NormQuotient`, `LocalField_NonarchimedeanLocalField_PrincipalUnitActions`, `LocalField_NonarchimedeanLocalField_ResidueExtension`, `LocalField_NonarchimedeanLocalField_ResidueGalois`, `Ramification_HilbertRamification_AbsoluteValueConjugacy`, `Valuation_AbsoluteValue_PrincipalAdicCompleteness`, `Valuation_Completion_FiniteLocalization`, `Valuation_Henselian_Factorization_AdicLimits`, `Valuation_Henselian_Factorization_Basic`, `Valuation_Henselian_Factorization_CoefficientMinimum`, `Valuation_Henselian_Factorization_InfiniteApproximation`, `Valuation_Henselian_Factorization_Iteration`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke000`, `OAIQ244Duke001`, `OAIQ244Duke002`, `OAIQ244Duke003` and `OAIQ244Duke004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke025`, `OAIQ244Duke026`, `OAIQ244Duke027`, `OAIQ244Duke028`, `OAIQ244Duke029`, `OAIQ244Duke030`, `OAIQ244Duke031`, `OAIQ244Duke033` and `OAIQ244Duke034`.
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
import Definitions.Def_OAIQ244Duke000
import Definitions.Def_OAIQ244Duke001
import Definitions.Def_OAIQ244Duke002
import Definitions.Def_OAIQ244Duke003
import Definitions.Def_OAIQ244Duke004

section
-- module Solutions.OAIQ244_DUKE.AbstractClassFieldTheory_Degree_FrobeniusFixedField
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.maximalUnramifiedNormQuotientAddCommGroup _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFintypeQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ClassFormation.finiteNormQuotientAddCommGroup _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

namespace DegreeData

/-- The normalized degree restricted to `Γ`. -/
def frobeniusClosureDegree (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusClosure K L hLK σ →ₜ* ZHatMul :=
  (D.extensionNormalizedDegreeContinuous K L hLK).comp
    (continuousSubgroupSubtype
      (D.frobeniusClosure K L hLK σ).toSubgroup)

end DegreeData

end
end ClassFormation
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_GaloisNorm
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The Galois product formula for the relative idele norm

This file proves that, in the tensor-product presentation
`𝔸_L = 𝔸_K ⊗_K L`, extension of the determinant norm back to `𝔸_L`
is the product of all Galois conjugates.
-/

open scoped BigOperators TensorProduct
open NumberField

noncomputable section


namespace RelativeIdeleGroup

universe u v w

variable
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- Base change carries the regular representation of `L/K` to the regular
representation of `A ⊗[K] L` over `A`. -/
theorem baseChangedLmul_eq
    (A : Type w) [CommRing A] [Algebra K A] :
    LinearMap.tensorProduct K A L L ∘ₗ
        (Algebra.lmul K L).toLinearMap.baseChange A =
      (Algebra.lmul A (A ⊗[K] L)).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using OAI.tensorInductionOn with
  | add z₁ z₂ hz₁ hz₂ =>
      rw [map_add, map_add, hz₁, hz₂]
  | tmul a x =>
      apply LinearMap.ext
      intro y
      induction y using OAI.tensorInductionOn with
      | add y₁ y₂ hy₁ hy₂ =>
          rw [map_add, map_add, hy₁, hy₂]
      | tmul b t =>
          simp [LinearMap.tensorProduct,
            Algebra.TensorProduct.tmul_mul_tmul,
            Algebra.smul_def, mul_comm]

/-- Evaluation of the universal norm polynomial after arbitrary scalar
extension is the determinant norm on the scalar-extended algebra. -/
theorem eval₂_normPolynomial_baseChange
    (A : Type*) [CommRing A] [Algebra K A] [Nontrivial A]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (z : A ⊗[K] L) :
    MvPolynomial.eval₂ (algebraMap K A)
        ((Algebra.TensorProduct.basis A b).repr z)
        (normPolynomial b) =
      Algebra.norm A z := by
  have hcoeff := congrArg
      (fun p : Polynomial (MvPolynomial ι A) ↦ p.coeff 0)
      (LinearMap.polyCharpoly_baseChange
        (Algebra.lmul K L).toLinearMap b A)
  rw [Polynomial.coeff_map] at hcoeff
  rw [normPolynomial, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_neg,
    MvPolynomial.eval₂_one]
  have heval :=
    MvPolynomial.eval₂_eq_eval_map
      (algebraMap K A)
      ((Algebra.TensorProduct.basis A b).repr z)
      (((Algebra.lmul K L).toLinearMap.polyCharpoly b).coeff 0)
  rw [heval, ← hcoeff]
  rw [LinearMap.polyCharpoly_coeff_eval]
  rw [baseChangedLmul_eq (K := K) (L := L) A]
  rw [Algebra.norm_apply,
    LinearMap.det_eq_sign_charpoly_coeff,
    Module.finrank_baseChange]
  rfl

end RelativeIdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Extension_LocalComponent
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.intermediateAdeleInclusion_tmul _root_.topFieldToOneStep_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local components of relative adeles and ideles

For a finite place `v` of `K`, evaluation on the finite-adele coordinate is
a `K`-algebra homomorphism `𝔸_K → K_v`.  Scalar extension along `L/K`
therefore gives the actual local component map

`𝔸_K ⊗[K] L → K_v ⊗[K] L`.

This is the map needed to apply the local tensor decomposition and the local
norm calculation to a genuine relative idele.
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

omit [NumberField K] [NumberField L] in
/-- Determinant norm commutes with scalar extension along a homomorphism
of coefficient algebras.  This is the base-change identity needed to
compare the global relative-idele norm with each local tensor norm. -/
theorem map_norm_tensorProduct_baseChange
    {A : Type*} {B : Type*}
    [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    [Nontrivial A] [Nontrivial B]
    (f : A →ₐ[K] B) (z : A ⊗[K] L) :
    f (Algebra.norm A z) =
      Algebra.norm B
        (Algebra.TensorProduct.map f (AlgHom.id K L) z) := by
  classical
  let b := Module.Free.chooseBasis K L
  have hrepr :
      ∀ i,
        (Algebra.TensorProduct.basis B b).repr
            (Algebra.TensorProduct.map f
              (AlgHom.id K L) z) i =
          f ((Algebra.TensorProduct.basis A b).repr z i) := by
    intro i
    induction z using OAI.tensorInductionOn with
    | add x y hx hy =>
        simp [map_add, hx, hy]
    | tmul a x =>
        simp
  calc
    f (Algebra.norm A z) =
        f
          (MvPolynomial.eval₂ (algebraMap K A)
            ((Algebra.TensorProduct.basis A b).repr z)
            (RelativeIdeleGroup.normPolynomial b)) := by
      rw [RelativeIdeleGroup.eval₂_normPolynomial_baseChange]
    _ =
        MvPolynomial.eval₂
          (f.toRingHom.comp (algebraMap K A))
          (fun i => f
            ((Algebra.TensorProduct.basis A b).repr z i))
          (RelativeIdeleGroup.normPolynomial b) :=
      MvPolynomial.hom_eval₂
        (RelativeIdeleGroup.normPolynomial b)
        (algebraMap K A) f.toRingHom _
    _ =
        MvPolynomial.eval₂ (algebraMap K B)
          ((Algebra.TensorProduct.basis B b).repr
            (Algebra.TensorProduct.map f
              (AlgHom.id K L) z))
          (RelativeIdeleGroup.normPolynomial b) := by
      congr 1
      · ext x
        exact f.commutes x
      · funext i
        exact (hrepr i).symm
    _ =
        Algebra.norm B
          (Algebra.TensorProduct.map f
            (AlgHom.id K L) z) :=
      RelativeIdeleGroup.eval₂_normPolynomial_baseChange
        B b _

omit [NumberField L] in
/-- The finite component of the global relative-idele norm is the
determinant norm of the corresponding local tensor component. -/
@[simp]
theorem RelativeIdeleGroup.finiteComponent_norm
    (v : HeightOneSpectrum (𝓞 K))
    (a : RelativeIdeleGroup K L) :
    IdeleGroup.finiteComponent v
        (RelativeIdeleGroup.norm K L a) =
      localTensorNorm (K := K) (L := L) v
        (RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) v a) := by
  apply Units.ext
  change
    finiteAdeleComponentAlgHom v
        (Algebra.norm
          (NumberField.AdeleRing (𝓞 K) K)
          (a : RelativeAdeleRing K L)) =
      Algebra.norm (v.adicCompletion K)
        (relativeAdeleFiniteComponent
          (K := K) (L := L) v
          (a : RelativeAdeleRing K L))
  exact map_norm_tensorProduct_baseChange
    (K := K) (L := L)
    (finiteAdeleComponentAlgHom v)
    (a : RelativeAdeleRing K L)

omit [NumberField L] in
/-- The infinite component of the global relative-idele norm is the
determinant norm of the corresponding archimedean tensor component. -/
@[simp]
theorem RelativeIdeleGroup.infiniteComponent_norm
    (v : InfinitePlace K)
    (a : RelativeIdeleGroup K L) :
    IdeleGroup.infiniteComponent v
        (RelativeIdeleGroup.norm K L a) =
      Units.map (Algebra.norm v.Completion)
        (RelativeIdeleGroup.infiniteComponent
          (K := K) (L := L) v a) := by
  apply Units.ext
  change
    infiniteAdeleComponentAlgHom v
        (Algebra.norm
          (NumberField.AdeleRing (𝓞 K) K)
          (a : RelativeAdeleRing K L)) =
      Algebra.norm v.Completion
        (relativeAdeleInfiniteComponent
          (K := K) (L := L) v
          (a : RelativeAdeleRing K L))
  exact map_norm_tensorProduct_baseChange
    (K := K) (L := L)
    (infiniteAdeleComponentAlgHom v)
    (a : RelativeAdeleRing K L)

omit [NumberField L] [FiniteDimensional K L] in
/-- The infinite component of a globally included idele is scalar
extension of its ordinary infinite component. -/
@[simp]
theorem RelativeIdeleGroup.infiniteComponent_inclusion
    (v : InfinitePlace K)
    (a : IdeleGroup K) :
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) v
        (RelativeIdeleGroup.inclusion K L a) =
      infiniteLocalIdeleInclusion
        (K := K) (L := L) v
        (IdeleGroup.infiniteComponent v a) := by
  apply Units.ext
  rfl

omit [NumberField L] [FiniteDimensional K L] in
/-- The infinite component of a principal relative idele is the
diagonal extension-field unit in the local tensor algebra. -/
@[simp]
theorem RelativeIdeleGroup.infiniteComponent_principalIdele
    (v : InfinitePlace K) (x : Lˣ) :
    RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) v
        (RelativeIdeleGroup.principalIdele K L x) =
      infiniteLocalFieldIdeleInclusion
        (K := K) (L := L) v x := by
  apply Units.ext
  rfl

omit [NumberField L] [FiniteDimensional K L] in
/-- The local component of the globally included idele is the scalar
extension of its ordinary local component. -/
@[simp]
theorem RelativeIdeleGroup.finiteComponent_inclusion
    (v : HeightOneSpectrum (𝓞 K))
    (a : IdeleGroup K) :
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) v
        (RelativeIdeleGroup.inclusion K L a) =
      localIdeleInclusion (K := K) (L := L) v
        (IdeleGroup.finiteComponent v a) := by
  apply Units.ext
  rfl

omit [NumberField L] [FiniteDimensional K L] in
/-- The local component of a principal relative idele is the diagonal
extension-field unit in the local tensor algebra. -/
@[simp]
theorem RelativeIdeleGroup.finiteComponent_principalIdele
    (v : HeightOneSpectrum (𝓞 K)) (x : Lˣ) :
    RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) v
        (RelativeIdeleGroup.principalIdele K L x) =
      localFieldIdeleInclusion (K := K) (L := L) v x := by
  apply Units.ext
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_Tower
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RelativeIdeleGroup.finiteComponent_coe _root_.RelativeIdeleGroup.finiteComponent_inclusion _root_.RelativeIdeleGroup.finiteComponent_norm _root_.RelativeIdeleGroup.finiteComponent_principalIdele _root_.RelativeIdeleGroup.infiniteComponent_coe _root_.RelativeIdeleGroup.infiniteComponent_inclusion _root_.RelativeIdeleGroup.infiniteComponent_norm _root_.RelativeIdeleGroup.infiniteComponent_principalIdele _root_.RelativeIdeleGroup.scalarConjugation_baseAdele_apply _root_.relativeAdeleFiniteComponent_tmul _root_.relativeAdeleInfiniteComponent_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Idele-class norms in a field tower

For a tower `K ⊂ M ⊂ L`, keep the bottom field `K` fixed and write

`𝔸_M = 𝔸_K ⊗[K] M`,
`𝔸_L = (𝔸_K ⊗[K] M) ⊗[M] L`.

This gives an actual norm `C_L → C_M` whose composite with
`C_M → C_K` is the tower norm.  The resulting three concrete norm
quotients form a natural right-exact sequence.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

universe u

variable
    (K M L : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
@[simp]
theorem towerRelativeAdeleFlatten_tmul
    (b : RelativeAdeleRing K M)
    (x : L) :
    towerRelativeAdeleFlatten K M L (b ⊗ₜ[M] x) =
      intermediateAdeleInclusion K M L b *
        topFieldToOneStep K M L x := by
  induction b using OAI.tensorInductionOn with
  | add b₁ b₂ hb₁ hb₂ =>
      simp only [TensorProduct.add_tmul, map_add,
        add_mul, hb₁, hb₂]
  | tmul a m =>
      simp [towerRelativeAdeleFlatten,
        towerRelativeAdeleRingEquiv,
        intermediateAdeleInclusion_tmul,
        topFieldToOneStep_apply,
        Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.smul_def]

/-- Embed the bottom adele algebra into the iterated tensor model. -/
def bottomAdeleToTower :
    NumberField.AdeleRing (𝓞 K) K →ₐ[K]
      TowerRelativeAdeleRing K M L :=
  (Algebra.TensorProduct.includeLeft
      (R := M) (S := K)
      (A := RelativeAdeleRing K M) (B := L)).comp
    (Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := NumberField.AdeleRing (𝓞 K) K) (B := M))

omit [NumberField M] [NumberField L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
@[simp]
theorem bottomAdeleToTower_apply
    (a : NumberField.AdeleRing (𝓞 K) K) :
    bottomAdeleToTower K M L a =
      (a ⊗ₜ[K] (1 : M)) ⊗ₜ[M] (1 : L) :=
  rfl

/-- Embed `L` into the iterated tensor model. -/
def topFieldToTower :
    L →ₐ[K] TowerRelativeAdeleRing K M L :=
  { (Algebra.TensorProduct.includeRight
      (R := M)
      (A := RelativeAdeleRing K M) (B := L)).toRingHom with
    commutes' := by
      intro k
      rw [IsScalarTower.algebraMap_apply K M L]
      change
        1 ⊗ₜ[M]
            algebraMap M L (algebraMap K M k) =
          algebraMap K
            (TowerRelativeAdeleRing K M L) k
      rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul
        (R := M)
        (A := RelativeAdeleRing K M)
        (B := L)]
      change
        ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K]
            algebraMap K M k) ⊗ₜ[M] (1 : L) =
          ((algebraMap K
              (NumberField.AdeleRing (𝓞 K) K) k) ⊗ₜ[K]
                (1 : M)) ⊗ₜ[M] (1 : L)
      rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul
        (R := K)
        (A := NumberField.AdeleRing (𝓞 K) K)
        (B := M)]
      }

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
@[simp]
theorem topFieldToTower_apply
    (x : L) :
    topFieldToTower K M L x =
      (1 : RelativeAdeleRing K M) ⊗ₜ[M] x :=
  rfl

/-- Expand the one-step tensor model back to the iterated tower model. -/
def towerRelativeAdeleUnflatten :
    RelativeAdeleRing K L →ₐ[K]
      TowerRelativeAdeleRing K M L :=
  { (towerRelativeAdeleRingEquiv K M L).symm.toRingHom with
    commutes' := by
      intro k
      simp [towerRelativeAdeleRingEquiv] }

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
@[simp]
theorem towerRelativeAdeleUnflatten_tmul
    (a : NumberField.AdeleRing (𝓞 K) K)
    (x : L) :
    towerRelativeAdeleUnflatten K M L (a ⊗ₜ[K] x) =
      bottomAdeleToTower K M L a *
        topFieldToTower K M L x := by
  simp [towerRelativeAdeleUnflatten,
    towerRelativeAdeleRingEquiv,
    bottomAdeleToTower_apply,
    topFieldToTower_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- Unit group of the tower presentation of the relative adeles of
`L`. -/
abbrev TowerRelativeIdeleGroup :=
  (TowerRelativeAdeleRing K M L)ˣ

/-- The canonical equivalence from the tower presentation of the
relative ideles of `L` to the one-step presentation over `K`. -/
def towerRelativeIdeleEquiv :
    TowerRelativeIdeleGroup K M L ≃*
      RelativeIdeleGroup K L :=
  Units.mapEquiv
    (towerRelativeAdeleRingEquiv K M L).toMulEquiv

-- Fix the canonical commutativity proof for the tower's tensor-product units.
local instance instIsMulCommutativeTowerRelativeIdeleGroup : IsMulCommutative (TowerRelativeIdeleGroup K M L) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance instIsMulCommutativeClassGroup : IsMulCommutative (RelativeIdeleGroup.ClassGroup K L) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

namespace TowerRelativeIdeleGroup

attribute [local instance] instIsMulCommutativeIdeleClassGroup
/-- The diagonal copy of `Lˣ` in the tower relative idele group. -/
def principalIdele :
    Lˣ →* TowerRelativeIdeleGroup K M L :=
  Units.map
    (Algebra.TensorProduct.includeRight
      (R := M) (A := RelativeAdeleRing K M) (B := L)).toRingHom

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
/-- Flattening the tower presentation preserves the diagonal copy of
`Lˣ`. -/
@[simp]
theorem towerRelativeIdeleEquiv_principalIdele
    (x : Lˣ) :
    towerRelativeIdeleEquiv K M L
        (principalIdele K M L x) =
      RelativeIdeleGroup.principalIdele K L x := by
  apply Units.ext
  change
    towerRelativeAdeleFlatten K M L
        ((1 : RelativeAdeleRing K M) ⊗ₜ[M] (x : L)) =
      (1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] (x : L)
  rw [towerRelativeAdeleFlatten_tmul]
  simp [topFieldToOneStep_apply]

/-- Principal ideles in the tower presentation. -/
def principalSubgroup :
    Subgroup (TowerRelativeIdeleGroup K M L) :=
  (principalIdele K M L).range

/-- The idele class group of `L` in the tower presentation. -/
abbrev ClassGroup :=
  TowerRelativeIdeleGroup K M L ⧸
    principalSubgroup K M L

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
/-- The canonical equivalence maps tower principal ideles exactly onto
the one-step principal-ideles subgroup. -/
theorem principalSubgroup_map_towerRelativeIdeleEquiv :
    (principalSubgroup K M L).map
        (towerRelativeIdeleEquiv K M L) =
      RelativeIdeleGroup.principalSubgroup K L := by
  rw [principalSubgroup,
    RelativeIdeleGroup.principalSubgroup,
    MonoidHom.map_range]
  congr 1
  ext x
  exact congrArg Units.val
    (towerRelativeIdeleEquiv_principalIdele K M L x)

/-- Canonical equivalence between the tower and one-step presentations
of the relative idele class group of `L`. -/
def classGroupEquiv :
    ClassGroup K M L ≃*
      RelativeIdeleGroup.ClassGroup K L :=
  QuotientGroup.congr
    (principalSubgroup K M L)
    (RelativeIdeleGroup.principalSubgroup K L)
    (towerRelativeIdeleEquiv K M L)
    (principalSubgroup_map_towerRelativeIdeleEquiv K M L)

omit [NumberField M] [NumberField L]
    [FiniteDimensional K M] [FiniteDimensional M L] in
@[simp]
theorem classGroupEquiv_mk
    (a : TowerRelativeIdeleGroup K M L) :
    classGroupEquiv K M L
        (QuotientGroup.mk' (principalSubgroup K M L) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L)
        (towerRelativeIdeleEquiv K M L a) :=
  rfl

/-- Determinant norm from the tower presentation of `𝔸_L` to
`𝔸_M = 𝔸_K ⊗[K] M`. -/
def norm :
    TowerRelativeIdeleGroup K M L →*
      RelativeIdeleGroup K M :=
  Units.map (Algebra.norm (RelativeAdeleRing K M))

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] in
/-- Base change of the field norm from `M` to the relative adele
algebra `𝔸_K ⊗[K] M`. -/
theorem norm_fieldInclusion
    (x : L) :
    Algebra.norm (RelativeAdeleRing K M)
        (Algebra.TensorProduct.includeRight
          (R := M) (A := RelativeAdeleRing K M) (B := L) x) =
      algebraMap M (RelativeAdeleRing K M)
        (Algebra.norm M x) := by
  classical
  let b := Module.Free.chooseBasis M L
  let bA := b.baseChange (RelativeAdeleRing K M)
  rw [Algebra.norm_eq_matrix_det bA,
    Algebra.norm_eq_matrix_det b,
    (algebraMap M (RelativeAdeleRing K M)).map_det]
  congr 1
  ext i j
  simp [bA, b, Algebra.smul_def,
    Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.tmul_mul_tmul]

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] in
/-- The tower idele norm carries a principal idele to the principal
idele of the field norm. -/
@[simp]
theorem norm_principalIdele
    (x : Lˣ) :
    norm K M L (principalIdele K M L x) =
      RelativeIdeleGroup.principalIdele K M
        (Units.map (Algebra.norm M) x) := by
  apply Units.ext
  exact norm_fieldInclusion K M L (x : L)

/-- The tower norm descended to actual idele class groups. -/
def classNorm :
    ClassGroup K M L →*
      RelativeIdeleGroup.ClassGroup K M :=
  QuotientGroup.map
    (principalSubgroup K M L)
    (RelativeIdeleGroup.principalSubgroup K M)
    (norm K M L)
    (by
      rintro _ ⟨x, rfl⟩
      exact
        ⟨Units.map (Algebra.norm M) x,
          (norm_principalIdele K M L x).symm⟩)

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] in
@[simp]
theorem classNorm_mk
    (a : TowerRelativeIdeleGroup K M L) :
    classNorm K M L
        (QuotientGroup.mk'
          (principalSubgroup K M L) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (norm K M L a) :=
  rfl

end TowerRelativeIdeleGroup

section NormQuotientSequence

attribute [local instance] instIsMulCommutativeIdeleClassGroup
/-- The norm quotient `C_M / N_{L/M} C_L` in the fixed-bottom-field
tower model. -/
abbrev IntermediateClassNormQuotient :=
  RelativeIdeleGroup.ClassGroup K M ⧸
    (TowerRelativeIdeleGroup.classNorm K M L).range

/-- The composite class norm `C_L → C_M → C_K` in the tower model. -/
def towerCompositeClassNorm :
    TowerRelativeIdeleGroup.ClassGroup K M L →*
      IdeleClassGroup K :=
  (RelativeIdeleGroup.classNorm K M).comp
    (TowerRelativeIdeleGroup.classNorm K M L)

/-- The corresponding concrete quotient `C_K / N_{L/K} C_L`, before
identifying the tower presentation of `C_L` with the one-step
presentation. -/
abbrev TowerCompositeClassNormQuotient :=
  IdeleClassGroup K ⧸
    (towerCompositeClassNorm K M L).range

/-- The norm-induced first map

`C_M / N_{L/M}C_L → C_K / N_{L/K}C_L`.
-/
def intermediateToCompositeNormQuotient :
    IntermediateClassNormQuotient K M L →*
      TowerCompositeClassNormQuotient K M L :=
  QuotientGroup.map
    (TowerRelativeIdeleGroup.classNorm K M L).range
    (towerCompositeClassNorm K M L).range
    (RelativeIdeleGroup.classNorm K M)
    (by
      rintro _ ⟨c, rfl⟩
      exact ⟨c, rfl⟩)

/-- The quotient map

`C_K / N_{L/K}C_L → C_K / N_{M/K}C_M`.
-/
def compositeToBaseNormQuotient :
    TowerCompositeClassNormQuotient K M L →*
      RelativeIdeleGroup.ClassNormQuotient K M :=
  QuotientGroup.map
    (towerCompositeClassNorm K M L).range
    (RelativeIdeleGroup.classNorm K M).range
    (MonoidHom.id (IdeleClassGroup K))
    (by
      rintro _ ⟨c, rfl⟩
      exact
        ⟨TowerRelativeIdeleGroup.classNorm K M L c, rfl⟩)

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L] in
@[simp]
theorem intermediateToCompositeNormQuotient_mk
    (c : RelativeIdeleGroup.ClassGroup K M) :
    intermediateToCompositeNormQuotient K M L
        (QuotientGroup.mk'
          (TowerRelativeIdeleGroup.classNorm K M L).range c) =
      QuotientGroup.mk'
        (towerCompositeClassNorm K M L).range
        (RelativeIdeleGroup.classNorm K M c) :=
  rfl

omit [NumberField M] [NumberField L] [Algebra K L] [IsScalarTower K M L] in
@[simp]
theorem compositeToBaseNormQuotient_mk
    (c : IdeleClassGroup K) :
    compositeToBaseNormQuotient K M L
        (QuotientGroup.mk'
          (towerCompositeClassNorm K M L).range c) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.classNorm K M).range c :=
  rfl

end NormQuotientSequence
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_ClassGroup_BaseChange
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

local instance instIsMulCommutativeTowerRelativeIdeleGroup_1_r8970c2_1 (A B C : Type u) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
local instance instIsMulCommutativeClassGroup_1_r8970c2_1 (A B : Type u) [Field A] [NumberField A]
    [Field B] [Algebra A B] :
    IsMulCommutative (RelativeIdeleGroup.ClassGroup A B) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
local instance instIsMulCommutativeIdeleClassGroup_1_r8970c2_1 (A : Type u) [Field A] [NumberField A] :
    IsMulCommutative (IdeleClassGroup A) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
/-- The scalar extension of the one-step `K`-presentation of the
relative adeles of `L` from the bottom adele ring to
`𝔸_K ⊗[K] M`. -/
abbrev BaseChangedRelativeAdeleRing :=
  RelativeAdeleRing K M ⊗[K] L
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_PrincipalUnitActions
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Actions on principal-unit quotients

Transports valuation-ring automorphisms to maximal-ideal powers, principal
units, and their successive quotients, together with the resulting actions.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The additive equivalence on successive principal-unit quotients agrees with transport of
quotient representatives. -/
@[simp]
theorem principalUnitsSuccQuotAddEquivOfIntegerRingEquiv_apply
    (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (e : 𝒪[K] ≃+* 𝒪[K]) (x : PrincipalUnitsSuccQuot K n) :
    principalUnitsSuccQuotAddEquivOfIntegerRingEquiv K n e (Additive.ofMul x) =
      Additive.ofMul (principalUnitsSuccQuotMapEquivOfIntegerRingEquiv K n e x) :=
  rfl

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ResidueExtension
attribute [-instance] _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
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

/-- Mapping an integer unit to the extension and then reducing agrees with reducing first and
mapping residue units. -/
@[simp]
theorem residueUnitsMap_integerUnitsToResidueUnits (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝒪[K]ˣ) :
    residueUnitsMapOfValuationExtension K L (integerUnitsToResidueUnits K u) =
      integerUnitsToResidueUnits L (integerUnitsMapOfValuationExtension K L u) := by
  ext
  rfl

/-- A first principal unit remains a first principal unit after extension of valued fields. -/
theorem integerUnitsMapOfValuationExtension_mem_principalUnits_one (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝒪[K]ˣ) (hu : u ∈ principalUnits K 1) :
    integerUnitsMapOfValuationExtension K L u ∈ principalUnits L 1 := by
  rw [← integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one L]
  rw [← residueUnitsMap_integerUnitsToResidueUnits K L u]
  rw [(integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one K u).2 hu]
  exact map_one (residueUnitsMapOfValuationExtension K L)

/-- The map on integer-unit residue quotients induced by a valuation extension. -/
def integerUnitsModPrincipalUnitsMapOfValuationExtension (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    IntegerUnitsModPrincipalUnits K →* IntegerUnitsModPrincipalUnits L :=
  integerUnitsModPrincipalUnitsLift
    ((integerUnitsModPrincipalUnitsMk L).comp
      (integerUnitsMapOfValuationExtension K L))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        IntegerUnitsModPrincipalUnits_mk_eq_one_iff]
      exact integerUnitsMapOfValuationExtension_mem_principalUnits_one K L u hu)

/-- The map modulo first principal units sends a class to the class of the extended integer unit. -/
@[simp]
theorem integerUnitsModPrincipalUnitsMapOfValuationExtension_mk (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (u : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapOfValuationExtension K L
        (integerUnitsModPrincipalUnitsMk K u) =
      integerUnitsModPrincipalUnitsMk L
        (integerUnitsMapOfValuationExtension K L u) :=
  rfl

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_GaloisIntegerRing
attribute [-instance] _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul _root_.LocalFieldTheory.galoisGroupResidueFieldEquivOfIsIntegralClosure_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Galois actions on valuation rings

Restricts Galois automorphisms to valuation rings and transports their action
to ideals, ideal-power quotients, principal units, and successive quotients.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Real Galois automorphisms act on `𝒪[L]` through the actual integral-closure
restriction. -/
def galoisGroupIntegerRingEquivHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L / K) →* (𝒪[L] ≃+* 𝒪[L]) where
  toFun := galoisGroupIntegerRingEquivOfIsIntegralClosure K L
  map_one' := by
    ext x
    rfl
  map_mul' := by
    intro σ τ
    ext x
    rfl

/-- The semiring action on the valuation integer ring induced by the actual
integral-closure restriction of `Gal(L / K)`. -/
@[reducible]
def galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    MulSemiringAction (Gal(L / K)) 𝒪[L] :=
  MulSemiringAction.compHom 𝒪[L] (galoisGroupIntegerRingEquivHomOfIsIntegralClosure K L)

/-- The actual integral-closure action commutes with the canonical
`𝒪[K]`-scalar action on `𝒪[L]`. -/
theorem galoisGroupIntegerRingSMulCommClassOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
    SMulCommClass (Gal(L / K)) 𝒪[K] 𝒪[L] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  refine ⟨?_⟩
  intro σ x y
  rw [Algebra.smul_def, Algebra.smul_def]
  change galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
      (algebraMap 𝒪[K] 𝒪[L] x * y) =
    algebraMap 𝒪[K] 𝒪[L] x *
      galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ y
  rw [map_mul]
  have hx : galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
      (algebraMap 𝒪[K] 𝒪[L] x) = algebraMap 𝒪[K] 𝒪[L] x := by
    simpa [integerRingMapOfValuationExtension] using
      galoisGroupIntegerRingEquivOfIsIntegralClosure_integerRingMap K L σ x
  rw [hx]

/-- The actual integral-closure action is compatible with the field-level
`Gal(L / K)` action after coercion to `L`. -/
theorem galoisGroupIntegerRingFieldSMulDistribClassOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
    SMulDistribClass (Gal(L / K)) 𝒪[L] L := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  refine ⟨?_⟩
  intro σ r s
  change σ (((r : 𝒪[L]) : L) * s) =
    ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ r : 𝒪[L]) : L) * σ s
  rw [map_mul]
  rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply]

/-- The actual integral-closure action on valuation integer rings is a mathlib
Galois group.  This is the source-producing version of the ring-level Galois
input needed for inertia/cardinality arguments. -/
theorem galoisGroupIntegerRing_isGaloisGroup_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
    IsGaloisGroup (Gal(L / K)) 𝒪[K] 𝒪[L] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  let := galoisGroupIntegerRingFieldSMulDistribClassOfIsIntegralClosure K L
  let : Algebra.IsIntegral 𝒪[K] 𝒪[L] :=
    IsIntegralClosure.isIntegral_algebra 𝒪[K] L
  exact IsGaloisGroup.of_isFractionRing (Gal(L / K)) 𝒪[K] 𝒪[L] K L

/-- The ideal action induced by the actual integral-closure restriction. -/
@[reducible]
def galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    DistribMulAction (Gal(L / K)) (Ideal 𝒪[L]) := by
  letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  exact Ideal.pointwiseDistribMulAction

/-- The multiplicative ideal action induced by the actual integral-closure
restriction. -/
@[reducible]
def galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    MulAction (Gal(L / K)) (Ideal 𝒪[L]) := by
  exact (galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure K L).toMulAction

/-- The Galois action on an integral-closure valuation ring preserves its maximal ideal. -/
theorem galoisGroupIntegerRingAction_map_maximalIdeal_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) :
    Ideal.map (@MulSemiringAction.toRingHom (Gal(L / K)) _ 𝒪[L] _
        (galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L) σ)
      (𝓂[L] : Ideal 𝒪[L]) =
      (𝓂[L] : Ideal 𝒪[L]) := by
  change Ideal.map
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toRingHom
      (𝓂[L] : Ideal 𝒪[L]) =
    (𝓂[L] : Ideal 𝒪[L])
  exact integerRingEquiv_map_maximalIdeal L
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)

/-- Every Galois automorphism belongs to the stabilizer of the maximal ideal of the integral-closure
valuation ring. -/
theorem galoisGroupIntegerRingAction_mem_maximalIdeal_stabilizer_of_isIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L / K)) :
    σ ∈ @MulAction.stabilizer (Gal(L / K)) (Ideal 𝒪[L]) _
      (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
      (𝓂[L] : Ideal 𝒪[L]) := by
  rw [@MulAction.mem_stabilizer_iff (Gal(L / K)) (Ideal 𝒪[L]) _
    (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)]
  change Ideal.map (@MulSemiringAction.toRingHom (Gal(L / K)) _ 𝒪[L] _
      (galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L) σ)
        (𝓂[L] : Ideal 𝒪[L]) =
    (𝓂[L] : Ideal 𝒪[L])
  exact galoisGroupIntegerRingAction_map_maximalIdeal_of_isIntegralClosure K L σ

/-- Real Galois automorphisms, viewed inside the maximal-ideal stabilizer, using
the actual integral-closure restriction. -/
def galoisGroupMaximalIdealStabilizerHomOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L / K) →* @MulAction.stabilizer (Gal(L / K)) (Ideal 𝒪[L]) _
      (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
      (𝓂[L] : Ideal 𝒪[L]) where
  toFun σ :=
    ⟨σ, galoisGroupIntegerRingAction_mem_maximalIdeal_stabilizer_of_isIntegralClosure K L σ⟩
  map_one' := by
    ext
    rfl
  map_mul' σ τ := by
    ext
    rfl

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_IdealQuotients
attribute [-instance] _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsConcreteEquiv_mk _root_.LocalFieldTheory.integerUnitsModPrincipalUnitsLift_mk _root_.LocalFieldTheory.principalUnitsSuccQuotAddEquivOfIntegerRingEquiv_apply _root_.LocalFieldTheory.residueField_algebraMap_residue
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

/-- Each power of the maximal ideal is generated by the matching power of the chosen uniformizer. -/
theorem maximalIdeal_pow_eq_span_uniformizer_pow
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    (𝓂[K] ^ n : Ideal 𝒪[K]) =
      Ideal.span ({chosenIntegerRingUniformizer K ^ n} : Set 𝒪[K]) :=
  maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducible K
    (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K) n

/-- Multiplication by `ϖ^n`, landing in the ideal `𝓂^n`. -/
def maximalIdealPowMulUniformizerPowMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    𝒪[K] →ₗ[𝒪[K]] ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) where
  toFun r := ⟨r * ϖ ^ n, mul_uniformizer_pow_mem_maximalIdeal_pow K ϖ hϖ n r⟩
  map_add' r s := by
    ext
    simp [add_mul]
  map_smul' a r := by
    ext
    simp [mul_assoc]

/-- The map into a maximal-ideal power multiplies its input by the corresponding uniformizer power.
The map into a maximal-ideal power multiplies its input by the corresponding uniformizer power. -/
@[simp]
theorem maximalIdealPowMulUniformizerPowMap_apply
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (r : 𝒪[K]) :
    (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r : 𝒪[K]) =
      r * ϖ ^ n :=
  rfl

/-- The map `𝒪[K] → 𝓂^n/𝓂^(n+1)` induced by multiplication by `ϖ^n`. -/
def maximalIdealPowSuccQuotMulUniformizerPowMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    𝒪[K] →ₗ[𝒪[K]] MaximalIdealPowSuccQuot K n :=
  (maximalIdealPowSuccQuotMk K n).comp
    (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n)

/-- On successive ideal quotients, multiplication by a uniformizer power sends a residue
representative to its ideal-quotient class. -/
@[simp]
theorem maximalIdealPowSuccQuotMulUniformizerPowMap_apply
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (r : 𝒪[K]) :
    maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n r =
      maximalIdealPowSuccQuotMk K n
        (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r) :=
  rfl

/-- The kernel of multiplication into a successive ideal quotient is the maximal ideal. -/
theorem maximalIdealPowSuccQuotMulUniformizerPowMap_ker
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    LinearMap.ker (maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n) =
      (𝓂[K] : Ideal 𝒪[K]) := by
  ext r
  rw [LinearMap.mem_ker]
  change maximalIdealPowSuccQuotMk K n
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r) = 0 ↔
    r ∈ (𝓂[K] : Ideal 𝒪[K])
  rw [maximalIdealPowSuccQuotMk_eq_zero_iff]
  change r * ϖ ^ n ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) ↔
    r ∈ (𝓂[K] : Ideal 𝒪[K])
  exact mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iff K ϖ hϖ n r

/-- Every class in a successive maximal-ideal quotient is represented by a uniformizer power times
an integer. -/
theorem maximalIdealPowSuccQuotMulUniformizerPowMap_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    Function.Surjective (maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n) := by
  intro x
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun x' =>
      ∃ r, maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n r = x')
    x ?_
  intro a
  have ha_span : (a : 𝒪[K]) ∈ Ideal.span ({ϖ ^ n} : Set 𝒪[K]) := by
    simpa [maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducible K ϖ hϖ n] using a.2
  rcases (Ideal.mem_span_singleton.mp ha_span) with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  change maximalIdealPowSuccQuotMk K n
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r) =
    maximalIdealPowSuccQuotMk K n a
  have hrep : maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r = a := by
    ext
    simp [maximalIdealPowMulUniformizerPowMap, hr, mul_comm]
  rw [hrep]

/-- The DVR comparison `𝒪[K]/𝓂[K] ≃ 𝓂^n/𝓂^(n+1)` attached to an irreducible
uniformizer `ϖ`. -/
def residueLinearEquivMaximalIdealPowSuccQuotOfIrreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    𝓀[K] ≃ₗ[𝒪[K]] MaximalIdealPowSuccQuot K n :=
  (Submodule.quotEquivOfEq (𝓂[K] : Submodule 𝒪[K] 𝒪[K])
      (LinearMap.ker (maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n))
      (maximalIdealPowSuccQuotMulUniformizerPowMap_ker K ϖ hϖ n).symm).trans
    ((maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n).quotKerEquivOfSurjective
      (maximalIdealPowSuccQuotMulUniformizerPowMap_surjective K ϖ hϖ n))

/-- Additive form of `𝒪[K]/𝓂[K] ≃ 𝓂^n/𝓂^(n+1)`. -/
def residueAddEquivMaximalIdealPowSuccQuotOfIrreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    𝓀[K] ≃+ MaximalIdealPowSuccQuot K n :=
  (residueLinearEquivMaximalIdealPowSuccQuotOfIrreducible K ϖ hϖ n).toAddEquiv

/-- The residue-to-ideal-quotient equivalence sends a residue class to the class of its lift times
the uniformizer power. -/
@[simp]
theorem residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (r : 𝒪[K]) :
    residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K ϖ hϖ n
        (IsLocalRing.residue 𝒪[K] r) =
    maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n r := by
  let f := maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n
  let hker : (𝓂[K] : Submodule 𝒪[K] 𝒪[K]) = LinearMap.ker f :=
    (maximalIdealPowSuccQuotMulUniformizerPowMap_ker K ϖ hϖ n).symm
  change (Submodule.quotEquivOfEq (𝓂[K] : Submodule 𝒪[K] 𝒪[K])
        (LinearMap.ker f) hker).trans
      (f.quotKerEquivOfSurjective
        (maximalIdealPowSuccQuotMulUniformizerPowMap_surjective K ϖ hϖ n))
      (Submodule.Quotient.mk r) = f r
  rw [LinearEquiv.trans_apply]
  have hquot :
      Submodule.quotEquivOfEq (𝓂[K] : Submodule 𝒪[K] 𝒪[K])
          (LinearMap.ker f) hker (Submodule.Quotient.mk r) =
        (Submodule.Quotient.mk r : 𝒪[K] ⧸ LinearMap.ker f) := by
    exact Submodule.quotEquivOfEq_mk
      (p := (𝓂[K] : Submodule 𝒪[K] 𝒪[K])) (p' := LinearMap.ker f) hker r
  rw [hquot]
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The unit-quotient coordinate theorem in additive form, using a specified
irreducible uniformizer.  This avoids the independent canonical-uniformizer
choice when comparing an unramified extension with the image of a base
uniformizer upstairs. -/
def principalUnitsSuccQuotAddEquivResidueOfIrreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) :
    Additive (PrincipalUnitsSuccQuot K n) ≃+ 𝓀[K] :=
  (maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot K n hn).symm.trans
    (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K ϖ hϖ n).symm

/-- The inverse residue equivalence extracts the residue coordinate of a successive principal-unit
class. -/
@[simp]
theorem principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_apply
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) (x : 𝓀[K]) :
    (principalUnitsSuccQuotAddEquivResidueOfIrreducible K ϖ hϖ n hn).symm x =
      principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd K n hn
        (residueAddEquivMaximalIdealPowSuccQuotOfIrreducible K ϖ hϖ n x) :=
  rfl

/-- Applying the inverse principal-unit quotient equivalence to a residue representative recovers
that residue. -/
@[simp]
theorem principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_residue
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) (r : 𝒪[K]) :
    (principalUnitsSuccQuotAddEquivResidueOfIrreducible K ϖ hϖ n hn).symm
        (IsLocalRing.residue 𝒪[K] r) =
      Additive.ofMul
        (principalUnitsSuccQuotMk K n
          (principalUnitOneAddOfMemPowSubgroup K hn
            ((maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r :
              (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K])
            (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r).2)) := by
  rw [principalUnitsSuccQuotAddEquivResidueOfIrreducible_symm_apply]
  rw [residueAddEquivMaximalIdealPowSuccQuotOfIrreducible_residue]
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuotAdd_apply]
  rw [maximalIdealPowSuccQuotMulUniformizerPowMap_apply]
  rw [principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_mk]
  rfl

/-- The class of `1 + rϖ^n` in `U^n/U^(n+1)`, for a DVR uniformizer `ϖ`.

This is the concrete coordinate used in the unit-quotient coordinate theorem:
successive principal-unit quotients are residue-field additive quotients. -/
noncomputable def principalUnitsSuccQuotUniformizerCoord
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) (r : 𝒪[K]) :
    PrincipalUnitsSuccQuot K n :=
  principalUnitsSuccQuotMk K n
    (principalUnitOneAddOfMemPowSubgroup K hn
      ((maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r :
        (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K])
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r).2)

/-- The zero coordinate gives the trivial class in `U^n/U^(n+1)`. -/
@[simp]
theorem principalUnitsSuccQuotUniformizerCoord_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) :
    principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn 0 = 1 := by
  change principalUnitsSuccQuotOfIdealPow K n hn
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n 0) = 1
  rw [map_zero]
  exact principalUnitsSuccQuotOfIdealPow_zero K n hn

/-- Uniformizer coordinates add as expected in the successive principal-unit
quotient: `1 + (r+s)ϖ^n` and `(1+rϖ^n)(1+sϖ^n)` have the same class modulo
`U^(n+1)`. -/
theorem principalUnitsSuccQuotUniformizerCoord_add
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) (r s : 𝒪[K]) :
    principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn (r + s) =
      principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn r *
        principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn s := by
  change principalUnitsSuccQuotOfIdealPow K n hn
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n (r + s)) =
    principalUnitsSuccQuotOfIdealPow K n hn
        (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r) *
      principalUnitsSuccQuotOfIdealPow K n hn
        (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n s)
  rw [map_add]
  exact principalUnitsSuccQuotOfIdealPow_add K n hn
    (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r)
    (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n s)

/-- Additive homomorphism form of the uniformizer coordinate
`r ↦ [1 + rϖ^n]` into the successive principal-unit quotient. -/
noncomputable def principalUnitsSuccQuotUniformizerCoordAddHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) :
    𝒪[K] →+ Additive (PrincipalUnitsSuccQuot K n) where
  toFun r := Additive.ofMul (principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn r)
  map_zero' := by
    change Additive.ofMul (principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn 0) = 0
    rw [principalUnitsSuccQuotUniformizerCoord_zero]
    rfl
  map_add' r s := by
    change Additive.ofMul (principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn (r + s)) =
      Additive.ofMul (principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn r) +
        Additive.ofMul (principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn s)
    rw [principalUnitsSuccQuotUniformizerCoord_add]
    rfl

/-- The uniformizer-coordinate homomorphism sends a principal-unit class to its residue-field
coordinate. -/
@[simp]
theorem principalUnitsSuccQuotUniformizerCoordAddHom_apply
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (hn : 1 ≤ n) (r : 𝒪[K]) :
    principalUnitsSuccQuotUniformizerCoordAddHom K ϖ hϖ n hn r =
      Additive.ofMul (principalUnitsSuccQuotUniformizerCoord K ϖ hϖ n hn r) :=
  rfl

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_NormQuotient
attribute [-instance] _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
# Quotients by local norm subgroups

Constructs `Kˣ/N(Lˣ)`, its universal maps and comparison equivalences, and
relates its finite cardinality to the index of the norm subgroup.
-/

namespace LocalFieldTheory

noncomputable section

universe u v

/-- The norm subgroup N_{L/K}(Lˣ) ≤ Kˣ. -/
def localNormSubgroup (K L : Type u) [Field K] [Field L] [Algebra K L] : Subgroup Kˣ :=
  (normUnits K L).range

/-- Units modulo field norms. -/
def NormQuotient (K L : Type u) [Field K] [Field L] [Algebra K L] : Type u :=
  Kˣ ⧸ localNormSubgroup K L

/-- Field units modulo the local norm subgroup form a commutative group. -/
instance normQuotientCommGroup (K L : Type u) [Field K] [Field L] [Algebra K L] :
    CommGroup (NormQuotient K L) := by
  change CommGroup (Kˣ ⧸ localNormSubgroup K L)
  infer_instance

/-- The explicit boundary to the concrete quotient implementation.  Clients
that need quotient-level constructions should use this equivalence instead of
unfolding `NormQuotient`. -/
def normQuotientConcreteEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    NormQuotient K L ≃* Kˣ ⧸ localNormSubgroup K L := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* Kˣ ⧸ localNormSubgroup K L
  exact MulEquiv.refl _

/-- Defines `normClass`. -/
def normClass (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Kˣ →* NormQuotient K L := by
  change Kˣ →* Kˣ ⧸ localNormSubgroup K L
  let N := localNormSubgroup K L
  exact QuotientGroup.mk' N

/-- The concrete quotient equivalence sends a norm class to the quotient class of its
representative. -/
@[simp]
theorem normQuotientConcreteEquiv_normClass
    (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ) :
    normQuotientConcreteEquiv K L (normClass K L x) =
      QuotientGroup.mk x := by
  rfl

/-- Define a homomorphism out of a norm quotient from a homomorphism on
`Kˣ` that kills every local norm. -/
def normQuotientLift {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (h : localNormSubgroup K L ≤ f.ker) :
    NormQuotient K L →* M := by
  change (Kˣ ⧸ localNormSubgroup K L) →* M
  let N := localNormSubgroup K L
  exact QuotientGroup.lift N f h

/-! ### Surjectivity and equality refinements for norm quotients -/

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_Basic
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# algebraic input for Hensel's lemma

This file records the residue-polynomial data used at the start of the
proof of Hensel's lemma.  The analytic convergence step is kept separate; the
lemmas here are the initial lifts and congruences.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- first congruence input: if `f` reduces to the product of
the residual factors and `g0`, `h0` lift those factors, then every coefficient
of `f - g0 h0` lies in the kernel of the coefficient map. -/
theorem henselFactorization_coeff_mem_ker_sub_mul_of_lifts
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    {f g0 h0 : R[X]} {gbar hbar : k[X]}
    (hfbar : f.map φ = gbar * hbar)
    (hg0 : g0.map φ = gbar) (hh0 : h0.map φ = hbar) :
    ∀ n : ℕ, (f - g0 * h0).coeff n ∈ RingHom.ker φ := by
  have hmap : (f - g0 * h0).map φ = 0 := by
    calc
      (f - g0 * h0).map φ = f.map φ - g0.map φ * h0.map φ := by
        exact henselFactorization_map_sub_mul φ f g0 h0
      _ = gbar * hbar - gbar * hbar := by
        rw [hfbar, hg0, hh0]
      _ = 0 := by simp
  exact (henselFactorization_map_eq_zero_iff_coeff_mem_ker φ _).1 hmap

/-- local-ring form of the first congruence input for the
residue map. -/
theorem henselFactorization_coeff_mem_maximalIdeal_sub_mul_of_residue_lifts
    {R : Type*} [CommRing R] [IsLocalRing R]
    {f g0 h0 : R[X]} {gbar hbar : (IsLocalRing.ResidueField R)[X]}
    (hfbar : f.map (IsLocalRing.residue R) = gbar * hbar)
    (hg0 : g0.map (IsLocalRing.residue R) = gbar)
    (hh0 : h0.map (IsLocalRing.residue R) = hbar) :
    ∀ n : ℕ, (f - g0 * h0).coeff n ∈ IsLocalRing.maximalIdeal R := by
  intro n
  have hker :
      (f - g0 * h0).coeff n ∈ RingHom.ker (IsLocalRing.residue R) :=
    henselFactorization_coeff_mem_ker_sub_mul_of_lifts
      (IsLocalRing.residue R) hfbar hg0 hh0 n
  rwa [IsLocalRing.ker_residue] at hker

/-- if a polynomial maps to `1`, then subtracting `1` gives
coefficients in the kernel of the coefficient map. -/
theorem henselFactorization_coeff_mem_ker_sub_one_of_map_eq_one
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    {P : R[X]} (hP : P.map φ = 1) :
    ∀ n : ℕ, (P - 1).coeff n ∈ RingHom.ker φ := by
  have hmap : (P - 1).map φ = 0 := by
    calc
      (P - 1).map φ = P.map φ - 1 := by
        simp [Polynomial.map_sub]
      _ = 0 := by
        rw [hP]
        simp
  exact (henselFactorization_map_eq_zero_iff_coeff_mem_ker φ _).1 hmap

/-- local-ring form of the lifted Bezout congruence:
`a*g0 + b*h0 ≡ 1` modulo the residue map means every coefficient of
`a*g0 + b*h0 - 1` lies in the maximal ideal. -/
theorem henselFactorization_coeff_mem_maximalIdeal_sub_one_of_bezout_lift
    {R : Type*} [CommRing R] [IsLocalRing R]
    {a b g0 h0 : R[X]}
    (hbez : (a * g0 + b * h0).map (IsLocalRing.residue R) = 1) :
    ∀ n : ℕ, (a * g0 + b * h0 - 1).coeff n ∈
      IsLocalRing.maximalIdeal R := by
  intro n
  have hker :
      (a * g0 + b * h0 - 1).coeff n ∈
        RingHom.ker (IsLocalRing.residue R) :=
    henselFactorization_coeff_mem_ker_sub_one_of_map_eq_one
      (IsLocalRing.residue R) hbez n
  rwa [IsLocalRing.ker_residue] at hker

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_AdicLimits
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# coefficientwise limit preparation

This file records the coefficientwise Cauchy form of the infinite Hensel
approximants.  It is the input needed for the adic-completeness step in
the coefficientwise proof of Hensel's lemma.
-/

noncomputable section

open scoped Polynomial
open scoped BigOperators

namespace AlgebraicNumberTheory
namespace Valuations

/-- A coefficientwise Cauchy estimate for a polynomial sequence gives an
adic Cauchy estimate for each fixed coefficient. -/
theorem henselFactorization_coeff_adicCoeffCauchy_of_sub_coeff_mem
    {R : Type*} [CommRing R] (I : Ideal R) {Pseq : ℕ → R[X]}
    (hsub :
      ∀ {M N : ℕ}, M ≤ N → ∀ i : ℕ,
        (Pseq N - Pseq M).coeff i ∈ I ^ (M + 1))
    (i : ℕ) :
    henselFactorization_adicCoeffCauchy I (fun N : ℕ => (Pseq N).coeff i) := by
  intro M N hMN
  simpa [henselFactorization_adicCoeffCauchy, Polynomial.coeff_sub] using hsub hMN i

/-- precompleteness supplies a coefficient limit for every
coefficient sequence satisfying the directed estimate. -/
theorem henselFactorization_exists_adicCoeffLimit
    {R : Type*} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    {x : ℕ → R}
    (hx : henselFactorization_adicCoeffCauchy I x) :
    ∃ L : R, ∀ n : ℕ, x n - L ∈ I ^ n := by
  obtain ⟨L, hL⟩ :=
    IsPrecomplete.prec (show IsPrecomplete I R from inferInstance)
      (henselFactorization_adicCoeffCauchy_isAdicCauchy I hx)
  refine ⟨L, fun n => ?_⟩
  have hmem := SModEq.sub_mem.mp (hL n)
  simpa [smul_eq_mul, Ideal.mul_top] using hmem

/-- bounded polynomial approximants with coefficientwise
adic limits have a bounded polynomial limit. -/
theorem henselFactorization_exists_limitPolynomial_of_bounded_coeffLimits
    {R : Type*} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    {N : ℕ} {Pseq : ℕ → R[X]}
    (hdeg : ∀ n : ℕ, (Pseq n).natDegree ≤ N)
    (hcauchy :
      ∀ i : ℕ, henselFactorization_adicCoeffCauchy I
        (fun n : ℕ => (Pseq n).coeff i)) :
    ∃ P : R[X], P.natDegree ≤ N ∧
      ∀ n i : ℕ, (Pseq n - P).coeff i ∈ I ^ n := by
  classical
  let L : ℕ → R :=
    fun i =>
      Classical.choose
        (henselFactorization_exists_adicCoeffLimit (I := I) (hcauchy i))
  let P : R[X] := henselFactorization_polyOfLimitCoeffs N L
  refine ⟨P, henselFactorization_polyOfLimitCoeffs_natDegree_le N L, ?_⟩
  intro n i
  by_cases hi : i ≤ N
  · have hlim :=
      Classical.choose_spec
        (henselFactorization_exists_adicCoeffLimit (I := I) (hcauchy i)) n
    simpa [P, L, Polynomial.coeff_sub,
      henselFactorization_polyOfLimitCoeffs_coeff_of_le (c := L) hi] using hlim
  · have hlt : N < i := Nat.lt_of_not_ge hi
    have hseq : (Pseq n).coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hdeg n) hlt)
    have hP : P.coeff i = 0 :=
      henselFactorization_polyOfLimitCoeffs_coeff_eq_zero_of_lt (c := L) hlt
    simp [Polynomial.coeff_sub, hseq, hP]

/-- coefficientwise membership in a ring-hom kernel gives
equality after mapping coefficients. -/
theorem henselFactorization_map_eq_of_sub_coeff_mem_ker
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    {P Q : R[X]}
    (hcoeff : ∀ i : ℕ, (P - Q).coeff i ∈ RingHom.ker φ) :
    P.map φ = Q.map φ := by
  have hzero : (P - Q).map φ = 0 :=
    (henselFactorization_map_eq_zero_iff_coeff_mem_ker φ (P - Q)).2 hcoeff
  rw [Polynomial.map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- coefficientwise maximal-ideal congruence is exactly
equality after mapping to the residue field. -/
theorem henselFactorization_residue_map_eq_of_sub_coeff_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] {P Q : R[X]}
    (hcoeff : ∀ i : ℕ, (P - Q).coeff i ∈ IsLocalRing.maximalIdeal R) :
    P.map (IsLocalRing.residue R) = Q.map (IsLocalRing.residue R) := by
  apply henselFactorization_map_eq_of_sub_coeff_mem_ker
  intro i
  have hi := hcoeff i
  rwa [IsLocalRing.ker_residue]

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_CoefficientMinimum
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# the finite minimum coefficient

The coefficientwise proof of Hensel's lemma chooses, among the finitely many
coefficients of `f - g₀h₀` and `ag₀ + bh₀ - 1`, one coefficient of minimum
valuation and calls it `π`.  In a valuation ring this is the same algebraic
input as choosing one coefficient that divides all coefficients in the finite
set.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- A coefficient supported in the left polynomial belongs to the two-polynomial
coefficient set. -/
theorem henselFactorization_mem_twoPolynomialCoeffFinset_left
    {R : Type*} [Semiring R] {P Q : R[X]} {n : ℕ}
    (hn : n ∈ P.support) :
    P.coeff n ∈ henselFactorization_twoPolynomialCoeffFinset P Q := by
  classical
  unfold henselFactorization_twoPolynomialCoeffFinset
  exact Finset.mem_union.mpr
    (Or.inl (Finset.mem_image.mpr ⟨n, hn, rfl⟩))

/-- A coefficient supported in the right polynomial belongs to the
two-polynomial coefficient set. -/
theorem henselFactorization_mem_twoPolynomialCoeffFinset_right
    {R : Type*} [Semiring R] {P Q : R[X]} {n : ℕ}
    (hn : n ∈ Q.support) :
    Q.coeff n ∈ henselFactorization_twoPolynomialCoeffFinset P Q := by
  classical
  unfold henselFactorization_twoPolynomialCoeffFinset
  exact Finset.mem_union.mpr
    (Or.inr (Finset.mem_image.mpr ⟨n, hn, rfl⟩))

/-- every element of the finite coefficient set is a
nonzero coefficient. -/
theorem henselFactorization_ne_zero_of_mem_twoPolynomialCoeffFinset
    {R : Type*} [Semiring R] {P Q : R[X]} {x : R}
    (hx : x ∈ henselFactorization_twoPolynomialCoeffFinset P Q) :
    x ≠ 0 := by
  classical
  unfold henselFactorization_twoPolynomialCoeffFinset at hx
  rw [Finset.mem_union] at hx
  rcases hx with hx | hx
  · rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
    simpa [Polynomial.mem_support_iff] using hn
  · rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
    simpa [Polynomial.mem_support_iff] using hn

/-- if the two-polynomial coefficient set is nonempty, one of
its coefficients divides every coefficient of both polynomials. -/
theorem henselFactorization_exists_coeff_dvd_all_two_polynomials
    {R : Type*} [CommRing R] [PreValuationRing R] {P Q : R[X]}
    (hs : (henselFactorization_twoPolynomialCoeffFinset P Q).Nonempty) :
    ∃ π ∈ henselFactorization_twoPolynomialCoeffFinset P Q,
      (∀ n : ℕ, π ∣ P.coeff n) ∧
        (∀ n : ℕ, π ∣ Q.coeff n) := by
  classical
  rcases henselFactorization_exists_mem_finset_dvd_all
      (R := R) (s := henselFactorization_twoPolynomialCoeffFinset P Q) hs with
    ⟨π, hπ, hπall⟩
  refine ⟨π, hπ, ?_, ?_⟩
  · intro n
    by_cases hn : n ∈ P.support
    · exact hπall (P.coeff n)
        (henselFactorization_mem_twoPolynomialCoeffFinset_left
          (P := P) (Q := Q) hn)
    · rw [Polynomial.notMem_support_iff.mp hn]
      exact dvd_zero π
  · intro n
    by_cases hn : n ∈ Q.support
    · exact hπall (Q.coeff n)
        (henselFactorization_mem_twoPolynomialCoeffFinset_right
          (P := P) (Q := Q) hn)
    · rw [Polynomial.notMem_support_iff.mp hn]
      exact dvd_zero π

/-- if the two polynomials have coefficients in an ideal, the
chosen finite-minimum coefficient lies in the same ideal. -/
theorem henselFactorization_exists_coeff_mem_ideal_dvd_all_two_polynomials
    {R : Type*} [CommRing R] [PreValuationRing R] {I : Ideal R}
    {P Q : R[X]}
    (hP : ∀ n : ℕ, P.coeff n ∈ I)
    (hQ : ∀ n : ℕ, Q.coeff n ∈ I)
    (hs : (henselFactorization_twoPolynomialCoeffFinset P Q).Nonempty) :
    ∃ π ∈ I,
      π ∈ henselFactorization_twoPolynomialCoeffFinset P Q ∧
        (∀ n : ℕ, π ∣ P.coeff n) ∧
          (∀ n : ℕ, π ∣ Q.coeff n) := by
  classical
  rcases henselFactorization_exists_coeff_dvd_all_two_polynomials
      (R := R) (P := P) (Q := Q) hs with
    ⟨π, hπcoeff, hπP, hπQ⟩
  have hπI : π ∈ I := by
    unfold henselFactorization_twoPolynomialCoeffFinset at hπcoeff
    rw [Finset.mem_union] at hπcoeff
    rcases hπcoeff with hπleft | hπright
    · rcases Finset.mem_image.mp hπleft with ⟨n, _hn, hnπ⟩
      rw [← hnπ]
      exact hP n
    · rcases Finset.mem_image.mp hπright with ⟨n, _hn, hnπ⟩
      rw [← hnπ]
      exact hQ n
  exact ⟨π, hπI, hπcoeff, hπP, hπQ⟩

/-- nonempty finite-minimum branch with the ideal
membership retained: if both source polynomials have coefficients in `I`, the
chosen coefficient `π` lies in `I` and simultaneously factors both
polynomials. -/
theorem henselFactorization_exists_coeff_mem_ideal_minimum_factor_two_polynomials
    {R : Type*} [CommRing R] [PreValuationRing R] {I : Ideal R}
    {P Q : R[X]}
    (hP : ∀ n : ℕ, P.coeff n ∈ I)
    (hQ : ∀ n : ℕ, Q.coeff n ∈ I)
    (hs : (henselFactorization_twoPolynomialCoeffFinset P Q).Nonempty) :
    ∃ π ∈ I,
      π ∈ henselFactorization_twoPolynomialCoeffFinset P Q ∧
        (∃ P' : R[X], P = Polynomial.C π * P') ∧
          (∃ Q' : R[X], Q = Polynomial.C π * Q') := by
  classical
  rcases henselFactorization_exists_coeff_mem_ideal_dvd_all_two_polynomials
      (R := R) (I := I) (P := P) (Q := Q) hP hQ hs with
    ⟨π, hπI, hπcoeff, hπP, hπQ⟩
  refine ⟨π, hπI, hπcoeff, ?_, ?_⟩
  · exact henselFactorization_exists_factor_of_coeff_mem_span_singleton
      (a := π) (P := P) (by
        intro n
        rw [Ideal.mem_span_singleton]
        exact hπP n)
  · exact henselFactorization_exists_factor_of_coeff_mem_span_singleton
      (a := π) (P := Q) (by
        intro n
        rw [Ideal.mem_span_singleton]
        exact hπQ n)

/-- the first choice of `π` in the nonempty branch:
from the two initial source polynomials
`f - g0*h0` and `a*g0 + b*h0 - 1`, choose a coefficient `π` lying in the
maximal ideal that factors both source polynomials. -/
theorem henselFactorization_exists_pi_factor_initial_errors_of_nonempty
    {R : Type*} [CommRing R] [IsLocalRing R] [PreValuationRing R]
    {f g0 h0 a b : R[X]}
    (herr : ∀ n : ℕ, (f - g0 * h0).coeff n ∈
      IsLocalRing.maximalIdeal R)
    (hbezerr : ∀ n : ℕ, (a * g0 + b * h0 - 1).coeff n ∈
      IsLocalRing.maximalIdeal R)
    (hs :
      (henselFactorization_twoPolynomialCoeffFinset
        (f - g0 * h0) (a * g0 + b * h0 - 1)).Nonempty) :
    ∃ π ∈ IsLocalRing.maximalIdeal R,
      π ∈ henselFactorization_twoPolynomialCoeffFinset
        (f - g0 * h0) (a * g0 + b * h0 - 1) ∧
        (∃ f1 : R[X], f - g0 * h0 = Polynomial.C π * f1) ∧
          (∃ e1 : R[X],
            a * g0 + b * h0 - 1 = Polynomial.C π * e1) := by
  exact henselFactorization_exists_coeff_mem_ideal_minimum_factor_two_polynomials
    (R := R) (I := IsLocalRing.maximalIdeal R)
    (P := f - g0 * h0) (Q := a * g0 + b * h0 - 1)
    herr hbezerr hs

/-- residue-factorization form of the first `π`
choice in the nonempty branch.  The two coefficient-in-the-maximal-ideal
inputs are produced from the residue factorization and lifted Bezout
congruence. -/
theorem henselFactorization_exists_pi_factor_initial_errors_of_residue_lifts_of_nonempty
    {R : Type*} [CommRing R] [IsLocalRing R] [PreValuationRing R]
    {f g0 h0 a b : R[X]}
    {gbar hbar : (IsLocalRing.ResidueField R)[X]}
    (hfbar : f.map (IsLocalRing.residue R) = gbar * hbar)
    (hg0 : g0.map (IsLocalRing.residue R) = gbar)
    (hh0 : h0.map (IsLocalRing.residue R) = hbar)
    (hbez : (a * g0 + b * h0).map (IsLocalRing.residue R) = 1)
    (hs :
      (henselFactorization_twoPolynomialCoeffFinset
        (f - g0 * h0) (a * g0 + b * h0 - 1)).Nonempty) :
    ∃ π ∈ IsLocalRing.maximalIdeal R,
      π ∈ henselFactorization_twoPolynomialCoeffFinset
        (f - g0 * h0) (a * g0 + b * h0 - 1) ∧
        (∃ f1 : R[X], f - g0 * h0 = Polynomial.C π * f1) ∧
          (∃ e1 : R[X],
            a * g0 + b * h0 - 1 = Polynomial.C π * e1) := by
  exact henselFactorization_exists_pi_factor_initial_errors_of_nonempty
    (R := R) (f := f) (g0 := g0) (h0 := h0) (a := a) (b := b)
    (henselFactorization_coeff_mem_maximalIdeal_sub_mul_of_residue_lifts
      hfbar hg0 hh0)
    (henselFactorization_coeff_mem_maximalIdeal_sub_one_of_bezout_lift hbez)
    hs

/-- if the finite coefficient set is empty, the first
polynomial is zero. -/
theorem henselFactorization_left_eq_zero_of_twoPolynomialCoeffFinset_empty
    {R : Type*} [Semiring R] {P Q : R[X]}
    (h : henselFactorization_twoPolynomialCoeffFinset P Q = ∅) :
    P = 0 := by
  ext n
  by_cases hn : n ∈ P.support
  · have hmem :
        P.coeff n ∈ henselFactorization_twoPolynomialCoeffFinset P Q :=
      henselFactorization_mem_twoPolynomialCoeffFinset_left
        (P := P) (Q := Q) hn
    rw [h] at hmem
    simp at hmem
  · exact Polynomial.notMem_support_iff.mp hn

/-- if the finite coefficient set is empty, the second
polynomial is zero. -/
theorem henselFactorization_right_eq_zero_of_twoPolynomialCoeffFinset_empty
    {R : Type*} [Semiring R] {P Q : R[X]}
    (h : henselFactorization_twoPolynomialCoeffFinset P Q = ∅) :
    Q = 0 := by
  ext n
  by_cases hn : n ∈ Q.support
  · have hmem :
        Q.coeff n ∈ henselFactorization_twoPolynomialCoeffFinset P Q :=
      henselFactorization_mem_twoPolynomialCoeffFinset_right
        (P := P) (Q := Q) hn
    rw [h] at hmem
    simp at hmem
  · exact Polynomial.notMem_support_iff.mp hn

/-- the empty finite coefficient set is exactly the branch
where both source polynomials are zero. -/
theorem henselFactorization_twoPolynomialCoeffFinset_empty_iff
    {R : Type*} [Semiring R] {P Q : R[X]} :
    henselFactorization_twoPolynomialCoeffFinset P Q = ∅ ↔ P = 0 ∧ Q = 0 := by
  classical
  constructor
  · intro h
    exact ⟨
      henselFactorization_left_eq_zero_of_twoPolynomialCoeffFinset_empty
        (P := P) (Q := Q) h,
      henselFactorization_right_eq_zero_of_twoPolynomialCoeffFinset_empty
        (P := P) (Q := Q) h⟩
  · rintro ⟨rfl, rfl⟩
    unfold henselFactorization_twoPolynomialCoeffFinset
    simp

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_Iteration
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# recursive Hensel iterates

This file records the recursive polynomial iterates used in the proof
of Hensel's lemma and the coefficientwise adic estimates needed for the later
completion argument.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- if the initial polynomial and all correction polynomials
have degree at most `M`, then every recursive iterate has degree at most
`M`. -/
theorem henselFactorization_henselIterate_natDegree_le
    {R : Type*} [CommRing R] {π : R} {F0 : R[X]} {corr : ℕ → R[X]} {M : ℕ}
    (hF0 : F0.natDegree ≤ M)
    (hcorr : ∀ n : ℕ, (corr n).natDegree ≤ M) :
    ∀ n : ℕ, (henselFactorization_henselIterate π F0 corr n).natDegree ≤ M := by
  intro n
  induction n with
  | zero =>
      simpa using hF0
  | succ n ih =>
      rw [henselFactorization_henselIterate_succ]
      have hterm :
          (Polynomial.C (π ^ (n + 1)) * corr (n + 1)).natDegree ≤ M :=
        (Polynomial.natDegree_C_mul_le (π ^ (n + 1)) (corr (n + 1))).trans
          (hcorr (n + 1))
      exact Polynomial.natDegree_add_le_of_degree_le ih hterm

/-- an iterate only depends on the correction coefficients up
to its own index. -/
theorem henselFactorization_henselIterate_eq_of_corr_eq_le
    {R : Type*} [CommRing R] {π : R} {F0 : R[X]}
    {corr corr' : ℕ → R[X]} :
    ∀ n : ℕ,
      (∀ k : ℕ, k ≤ n → corr k = corr' k) →
        henselFactorization_henselIterate π F0 corr n =
          henselFactorization_henselIterate π F0 corr' n := by
  intro n hcorr
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [henselFactorization_henselIterate_succ,
        henselFactorization_henselIterate_succ]
      have hprev :
          henselFactorization_henselIterate π F0 corr n =
            henselFactorization_henselIterate π F0 corr' n :=
        ih (by
          intro k hk
          exact hcorr k (Nat.le_trans hk (Nat.le_succ n)))
      rw [hprev, hcorr (n + 1) le_rfl]

/-- changing a correction coefficient at a later index does
not change an earlier Hensel iterate. -/
theorem henselFactorization_henselIterate_update_of_lt
    {R : Type*} [CommRing R] (π : R) (F0 : R[X])
    (corr : ℕ → R[X]) {n k : ℕ} (c : R[X]) (h : n < k) :
    henselFactorization_henselIterate π F0 (Function.update corr k c) n =
      henselFactorization_henselIterate π F0 corr n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [henselFactorization_henselIterate_succ,
        henselFactorization_henselIterate_succ]
      have hnlt : n < k := lt_trans (Nat.lt_succ_self n) h
      rw [ih hnlt]
      have hne : n + 1 ≠ k := ne_of_lt h
      rw [Function.update_of_ne hne]

/-- extending the correction sequence at the next index gives
the expected next Hensel iterate. -/
theorem henselFactorization_henselIterate_update_next
    {R : Type*} [CommRing R] (π : R) (F0 : R[X])
    (corr : ℕ → R[X]) (n : ℕ) (c : R[X]) :
    henselFactorization_henselIterate π F0
        (Function.update corr (n + 1) c) (n + 1) =
      henselFactorization_henselIterate π F0 corr n +
        Polynomial.C (π ^ (n + 1)) * c := by
  rw [henselFactorization_henselIterate_succ]
  rw [henselFactorization_henselIterate_update_of_lt
    (π := π) (F0 := F0) (corr := corr) (c := c) (Nat.lt_succ_self n)]
  rw [Function.update_self]

/-- updating the correction functions at `n+1` preserves all
factorization invariants already established up to stage `n`. -/
theorem henselFactorization_henselIterate_update_preserves_factor_of_le
    {R : Type*} [CommRing R] {π : R}
    {f g0 h0 : R[X]} (pCorr qCorr : ℕ → R[X])
    {n r : ℕ} (hr : r ≤ n) (p q fn : R[X])
    (hfactor :
      f - henselFactorization_henselIterate π g0 pCorr r *
          henselFactorization_henselIterate π h0 qCorr r =
        Polynomial.C (π ^ (r + 1)) * fn) :
    f - henselFactorization_henselIterate π g0
          (Function.update pCorr (n + 1) p) r *
        henselFactorization_henselIterate π h0
          (Function.update qCorr (n + 1) q) r =
      Polynomial.C (π ^ (r + 1)) * fn := by
  have hrlt : r < n + 1 := Nat.lt_succ_of_le hr
  rw [henselFactorization_henselIterate_update_of_lt
      (π := π) (F0 := g0) (corr := pCorr) (c := p) hrlt,
    henselFactorization_henselIterate_update_of_lt
      (π := π) (F0 := h0) (corr := qCorr) (c := q) hrlt]
  exact hfactor

/-- the one-step factorization statement rewritten in terms
of the updated Hensel iterates. -/
theorem henselFactorization_henselIterate_update_next_factor
    {R : Type*} [CommRing R] {π : R}
    {f g0 h0 : R[X]} (pCorr qCorr : ℕ → R[X])
    (n : ℕ) (p q fnNext : R[X])
    (hfactorNext :
      f - (henselFactorization_henselIterate π g0 pCorr n +
            Polynomial.C (π ^ (n + 1)) * p) *
          (henselFactorization_henselIterate π h0 qCorr n +
            Polynomial.C (π ^ (n + 1)) * q) =
        Polynomial.C (π ^ (n + 2)) * fnNext) :
    f - henselFactorization_henselIterate π g0
          (Function.update pCorr (n + 1) p) (n + 1) *
        henselFactorization_henselIterate π h0
          (Function.update qCorr (n + 1) q) (n + 1) =
      Polynomial.C (π ^ (n + 2)) * fnNext := by
  rw [henselFactorization_henselIterate_update_next
      (π := π) (F0 := g0) (corr := pCorr) (c := p),
    henselFactorization_henselIterate_update_next
      (π := π) (F0 := h0) (corr := qCorr) (c := q)]
  exact hfactorNext

/-- a global correction-degree bound is preserved when one
correction coefficient is replaced by another coefficient satisfying the same
bound. -/
theorem henselFactorization_update_corr_natDegree_le
    {R : Type*} [CommRing R] {corr : ℕ → R[X]} {k M : ℕ} {c : R[X]}
    (hcorr : ∀ r : ℕ, (corr r).natDegree ≤ M)
    (hc : c.natDegree ≤ M) :
    ∀ r : ℕ, ((Function.update corr k c) r).natDegree ≤ M := by
  intro r
  by_cases h : r = k
  · subst r
    simpa [Function.update_self] using hc
  · rw [Function.update_of_ne h]
    exact hcorr r

/-- the increment from step `n` to step `n+1` is exactly the
chosen `π^(n+1)`-multiple. -/
theorem henselFactorization_henselIterate_succ_sub_eq
    {R : Type*} [CommRing R] (π : R) (F0 : R[X]) (corr : ℕ → R[X])
    (n : ℕ) :
    henselFactorization_henselIterate π F0 corr (n + 1) -
        henselFactorization_henselIterate π F0 corr n =
      Polynomial.C (π ^ (n + 1)) * corr (n + 1) := by
  rw [henselFactorization_henselIterate_succ]
  ring

/-- coefficient form of the increment estimate in the
principal ideal `(π^(n+1))`. -/
theorem henselFactorization_henselIterate_succ_sub_coeff_mem_span_singleton_pow
    {R : Type*} [CommRing R] {π : R} (F0 : R[X]) (corr : ℕ → R[X])
    (n i : ℕ) :
    (henselFactorization_henselIterate π F0 corr (n + 1) -
        henselFactorization_henselIterate π F0 corr n).coeff i ∈
      Ideal.span ({π ^ (n + 1)} : Set R) := by
  rw [henselFactorization_henselIterate_succ_sub_eq, Polynomial.coeff_C_mul]
  refine Ideal.mem_span_singleton'.mpr ⟨(corr (n + 1)).coeff i, ?_⟩
  ring

/-- coefficient form of the increment estimate in the
`(n+1)`-st power of the principal ideal `(π)`. -/
theorem henselFactorization_henselIterate_succ_sub_coeff_mem_span_pow
    {R : Type*} [CommRing R] {π : R} (F0 : R[X]) (corr : ℕ → R[X])
    (n i : ℕ) :
    (henselFactorization_henselIterate π F0 corr (n + 1) -
        henselFactorization_henselIterate π F0 corr n).coeff i ∈
      Ideal.span ({π} : Set R) ^ (n + 1) := by
  rw [Ideal.span_singleton_pow]
  exact henselFactorization_henselIterate_succ_sub_coeff_mem_span_singleton_pow
    F0 corr n i

/-- Cauchy-control estimate for two iterates in the
principal-ideal filtration generated by `π`. -/
theorem henselFactorization_henselIterate_sub_coeff_mem_span_pow_of_le
    {R : Type*} [CommRing R] {π : R}
    (F0 : R[X]) (corr : ℕ → R[X]) :
    ∀ {m n : ℕ}, m ≤ n → ∀ i : ℕ,
      (henselFactorization_henselIterate π F0 corr n -
          henselFactorization_henselIterate π F0 corr m).coeff i ∈
        Ideal.span ({π} : Set R) ^ (m + 1) := by
  intro m n hmn
  induction n generalizing m with
  | zero =>
      intro i
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hmn
      simp [hm0]
  | succ n ih =>
      intro i
      by_cases hm : m = n + 1
      · simp [hm]
      · have hmle : m ≤ n := Nat.lt_succ_iff.mp (lt_of_le_of_ne hmn hm)
        have hprev := ih hmle i
        have hincr :
            (henselFactorization_henselIterate π F0 corr (n + 1) -
                henselFactorization_henselIterate π F0 corr n).coeff i ∈
              Ideal.span ({π} : Set R) ^ (m + 1) :=
          (Ideal.pow_le_pow_right (Nat.succ_le_succ hmle))
            (henselFactorization_henselIterate_succ_sub_coeff_mem_span_pow
              F0 corr n i)
        have hsplit :
            henselFactorization_henselIterate π F0 corr (n + 1) -
                henselFactorization_henselIterate π F0 corr m =
              (henselFactorization_henselIterate π F0 corr n -
                  henselFactorization_henselIterate π F0 corr m) +
                (henselFactorization_henselIterate π F0 corr (n + 1) -
                  henselFactorization_henselIterate π F0 corr n) := by
          ring
        rw [hsplit, Polynomial.coeff_add]
        exact (Ideal.span ({π} : Set R) ^ (m + 1)).add_mem hprev hincr


end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Henselian_Factorization_InfiniteApproximation
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# compatible Hensel prefixes

This file turns the finite Hensel-prefix construction into a recursive family
of compatible prefixes.  The completion/limit argument is kept for the next
layer.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- the stage `0` prefix state from a displayed
finite-minimum factor of the initial error. -/
def henselFactorization_initialPrefixState_of_factor
    {R : Type*} [CommRing R] [IsLocalRing R]
    {π : R} {f g0 h0 f1 : R[X]} {m d : ℕ}
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hg0nat : g0.natDegree = m)
    (hh0deg : h0.natDegree ≤ d - m) :
    HenselFactorizationFinitePrefixState π f g0 h0 m d 0 := by
  refine
    { pCorr := fun _ => 0
      qCorr := fun _ => 0
      fErr := f1
      prefixFactor := ?_
      pCorrDeg := ?_
      qCorrDeg := ?_
      factor := ?_
      gDeg := ?_
      hDeg := ?_
      gRed := ?_
      hRed := ?_ }
  · intro r hr
    have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
    subst r
    exact ⟨f1, by simpa using hfactor0⟩
  · intro r
    simp
  · intro r
    simp
  · simpa using hfactor0
  · simp [hg0nat]
  · simpa using hh0deg
  · intro i
    simp
  · intro i
    simp


end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_AbsoluteValue_PrincipalAdicCompleteness
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.AlgebraicNumberTheory.Valuations.absoluteValueExponentialValuation_apply_ne_zero _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Principal adic filtrations in complete nonarchimedean valuation rings

For a complete nonarchimedean absolute value, a nonzero element of the open
unit ball generates a separated and precomplete principal filtration on the
closed unit ball.  These facts are shared by the coefficientwise Hensel
construction and the irreducible-polynomial coefficient estimate.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

/-- Principal separatedness for the element `π` chosen in the proof, as
soon as `π` is a nonzero element of the open unit ball. -/
theorem principalHausdorff_of_nonzero_mem_maximalIdeal
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π : absoluteValueValuationSubring v hnonarch}
    (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch)) :
    IsHausdorff (Ideal.span ({π} : Set
      (absoluteValueValuationSubring v hnonarch)))
      (absoluteValueValuationSubring v hnonarch) := by
  let V := absoluteValueValuationSubring v hnonarch
  refine ⟨?_⟩
  intro x hx
  have hπ_abs_lt : v ((π : V) : K) < 1 :=
    (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
      v hnonarch π).1 hπmem
  have hπK_ne : ((π : V) : K) ≠ 0 := by
    intro hzero
    exact hπne (Subtype.ext hzero)
  by_contra hxne
  have hxK_ne : (x : K) ≠ 0 := by
    intro hxzero
    exact hxne (Subtype.ext hxzero)
  have hx_abs_pos : 0 < v (x : K) := v.pos hxK_ne
  rcases exists_pow_lt_of_lt_one hx_abs_pos hπ_abs_lt with ⟨n, hn⟩
  have hxmem : x ∈ (Ideal.span ({π} : Set V)) ^ n := by
    have h := (SModEq.zero.mp (hx n))
    simpa [smul_eq_mul, Ideal.mul_top, V] using h
  have hx_abs_le :=
    (principal_pow_mem_iff_abs_le
      v hnonarch (π := π) (x := x) hπne n).1 hxmem
  exact not_lt_of_ge hx_abs_le hn

/-- Principal precompleteness for the element `π` chosen in the proof,
deduced from completeness of the valued field. -/
theorem principalPrecomplete_of_complete
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π : absoluteValueValuationSubring v hnonarch}
    (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch)) :
    IsPrecomplete (Ideal.span ({π} : Set
      (absoluteValueValuationSubring v hnonarch)))
      (absoluteValueValuationSubring v hnonarch) := by
  let V := absoluteValueValuationSubring v hnonarch
  let I : Ideal V := Ideal.span ({π} : Set V)
  have hπ_abs_lt : v ((π : V) : K) < 1 :=
    (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
      v hnonarch π).1 hπmem
  have hπK_ne : ((π : V) : K) ≠ 0 := by
    intro hzero
    exact hπne (Subtype.ext hzero)
  have hπ_abs_pos : 0 < v ((π : V) : K) := v.pos hπK_ne
  refine ⟨?_⟩
  intro f hf
  let u : ℕ → WithAbs v := fun n => (WithAbs.equiv v).symm ((f n : V) : K)
  have hu : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rcases exists_pow_lt_of_lt_one hε hπ_abs_lt with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    wlog hmn : m ≤ n generalizing m n with H
    · have hnm : n ≤ m := le_of_not_ge hmn
      simpa [dist_comm] using H n hn m hm hnm
    have hsub_le :
        v (((f m : V) : K) - ((f n : V) : K)) ≤
          v ((π : V) : K) ^ m :=
      abs_sub_le_of_principal_smodEq
        v hnonarch (π := π) hπne (hf hmn)
    have hpow_le : v ((π : V) : K) ^ m ≤ v ((π : V) : K) ^ N :=
      pow_le_pow_of_le_one (le_of_lt hπ_abs_pos) hπ_abs_lt.le hm
    have hdist_le :
        dist (u m) (u n) ≤ v ((π : V) : K) ^ N := by
      calc
        dist (u m) (u n) =
            v (((f m : V) : K) - ((f n : V) : K)) := by
          simp [u, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs]
        _ ≤ v ((π : V) : K) ^ m := hsub_le
        _ ≤ v ((π : V) : K) ^ N := hpow_le
    exact hdist_le.trans_lt hN
  rcases (absoluteValueCompleteness_complete_iff_cauchySeq_converges v).1
      hcomplete u hu with
    ⟨a, ha⟩
  let aK : K := WithAbs.equiv v a
  have ha_dist_lt_one : ∃ N : ℕ, dist (u N) a < 1 := by
    rcases Filter.eventually_atTop.1
        ((Metric.tendsto_nhds.mp ha) 1 zero_lt_one) with
      ⟨N, hN⟩
    exact ⟨N, hN N le_rfl⟩
  rcases ha_dist_lt_one with ⟨N₁, hN₁⟩
  have ha_sub_lt_one :
      v (aK - ((f N₁ : V) : K)) < 1 := by
    have hfa : v (((f N₁ : V) : K) - aK) < 1 := by
      simpa [aK, u, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs] using hN₁
    have hneg : aK - ((f N₁ : V) : K) = -(((f N₁ : V) : K) - aK) := by
      ring
    rw [hneg]
    rw [v.map_neg]
    simpa using hfa
  have ha_mem : aK ∈ V := by
    rw [mem_absoluteValueValuationSubring_iff]
    have hfN_mem : v (((f N₁ : V) : K)) ≤ 1 :=
      (mem_absoluteValueValuationSubring_iff
        v hnonarch (((f N₁ : V) : K))).1 (f N₁).property
    calc
      v aK = v (((f N₁ : V) : K) + (aK - ((f N₁ : V) : K))) := by
        ring_nf
      _ ≤ max (v (((f N₁ : V) : K))) (v (aK - ((f N₁ : V) : K))) :=
        LubinTate.Valuations.strong_triangle_of_nonarchimedean
          v hnonarch (((f N₁ : V) : K)) (aK - ((f N₁ : V) : K))
      _ ≤ 1 := max_le hfN_mem ha_sub_lt_one.le
  let L : V := ⟨aK, ha_mem⟩
  refine ⟨L, ?_⟩
  intro n
  have hπpow_pos : 0 < v ((π : V) : K) ^ n :=
    pow_pos hπ_abs_pos n
  rcases Filter.eventually_atTop.1
      ((Metric.tendsto_nhds.mp ha) (v ((π : V) : K) ^ n) hπpow_pos) with
    ⟨N₀, hN₀⟩
  let N : ℕ := max n N₀
  have hnN : n ≤ N := le_max_left n N₀
  have hN₀N : N₀ ≤ N := le_max_right n N₀
  have hsub_le :
      v (((f n : V) : K) - ((f N : V) : K)) ≤
        v ((π : V) : K) ^ n :=
    abs_sub_le_of_principal_smodEq
      v hnonarch (π := π) hπne (hf hnN)
  have hN_lim :
      v (((f N : V) : K) - aK) ≤ v ((π : V) : K) ^ n := by
    have hdist := hN₀ N hN₀N
    exact le_of_lt (by
      simpa [aK, u, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs] using hdist)
  have hdiff_le :
      v (((f n : V) : K) - (L : K)) ≤ v ((π : V) : K) ^ n := by
    calc
      v (((f n : V) : K) - (L : K)) =
          v ((((f n : V) : K) - ((f N : V) : K)) +
              (((f N : V) : K) - (L : K))) := by
        ring_nf
      _ ≤ max
          (v (((f n : V) : K) - ((f N : V) : K)))
          (v (((f N : V) : K) - (L : K))) :=
        LubinTate.Valuations.strong_triangle_of_nonarchimedean
          v hnonarch
          (((f n : V) : K) - ((f N : V) : K))
          (((f N : V) : K) - (L : K))
      _ ≤ v ((π : V) : K) ^ n := max_le hsub_le hN_lim
  exact
    (principal_smodEq_iff_abs_sub_le
      v hnonarch (π := π) (x := f n) (y := L) hπne).2
      (by simpa [L] using hdiff_le)

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_AbsoluteValueConjugacy
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.AlgebraicNumberTheory.Valuations.absoluteValueExtension_localizationTensorHom_tmul _root_.AlgebraicNumberTheory.Valuations.completionExtensionFactor_adjoinRootEquivCompletion_root _root_.AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion_coe _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Valuation conjugacy

For a possibly infinite Galois extension `L/K`, the Galois group acts
transitively on the extensions to `L` of a nontrivial absolute value of `K`.
-/

noncomputable section

universe u v

namespace AlgebraicNumberTheory
namespace Valuations

/-- Normality descent for the embeddings supplied by the valuation-extension theorem: two exact
extensions differ by an actual `K`-automorphism of `L`, not merely by an
automorphism of the ambient algebraic closure. -/
theorem absoluteValueConjugacy_exists_conjugatingAlgEquiv
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w w' : AbsoluteValueExtension vK L) :
    ∃ σ : L ≃ₐ[K] L, w'.1 = absoluteValueConjugate w.1 σ := by
  let A := absoluteValueExtension_algebraicCompletionClosure vK
  let τ : L →ₐ[K] A := absoluteValueExtension_embeddingOfExtension vK w
  let τ' : L →ₐ[K] A := absoluteValueExtension_embeddingOfExtension vK w'
  let : Algebra L A := τ.toRingHom.toAlgebra
  let : IsScalarTower K L A :=
    IsScalarTower.of_algebraMap_eq' τ.comp_algebraMap.symm
  let σ : L ≃ₐ[K] L := Normal.algHomEquivAut K A L τ'
  refine ⟨σ, ?_⟩
  rw [absoluteValueExtension_extension_eq_pullback_embeddingOfExtension vK hvK w',
    absoluteValueExtension_extension_eq_pullback_embeddingOfExtension vK hvK w]
  ext x
  change
    absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK (τ' x) =
      absoluteValueExtension_algebraicClosureAbsoluteValue vK hvK (τ (σ x))
  congr 1
  simpa [σ, τ, AlgHom.restrictNormal', RingHom.algebraMap_toAlgebra] using
    (τ'.restrictNormal_commutes L x).symm

end Valuations
end AlgebraicNumberTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Completion_FiniteLocalization
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite localizations inside metric completions

For a finite extension `L / K`, the localization `L K_v` inside
the metric completion `L_w` is already all of `L_w`.  The proof uses no
separability: the image of `K_v ⊗_K L` is finite-dimensional and closed,
but contains the dense copy of `L`.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

universe u v

open scoped TensorProduct

/-- The algebraic localization of an extension inside the completion selected
by an extended absolute value. -/
abbrev LocalizedCompletion
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) :=
  AbsoluteValue.algebraicLocalization vK w.1 w.2

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The algebraic localization of a finite extension is finite-dimensional
over the completed base field. -/
theorem localizedCompletionModuleFinite
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    Module.Finite vK.Completion
      (AbsoluteValue.algebraicLocalization vK w.1 w.2) := by
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Module.Finite vK.Completion
      (vK.Completion ⊗[K] L) :=
    inferInstance
  let f :=
    absoluteValueExtension_localizationTensorHom vK w
  let : Module.Finite vK.Completion
      w.1.Completion :=
    Module.Finite.of_surjective f.toLinearMap
      (absoluteValueExtension_localizationTensorHom_surjective
        vK hvK w)
  exact FiniteDimensional.of_injective
    (AbsoluteValue.algebraicLocalization vK w.1 w.2).val.toLinearMap
    (AbsoluteValue.algebraicLocalization vK w.1 w.2).val.injective

end Valuations
end AlgebraicNumberTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_ResidueGalois
attribute [-instance] _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
# Galois actions on residue fields

Restricts field automorphisms to residue-field automorphisms and identifies
the resulting kernels and stabilizers with inertia subgroups.
-/

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The residue representation of the Galois group evaluates to the induced residue-field algebra
automorphism. -/
@[simp]
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_apply (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) :
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L σ =
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ :=
  rfl

/-- The mathlib stabilizer action on the residue field, specialized to the
actual integral-closure action of `Gal(L / K)` on `𝒪[L]`. -/
def galoisGroupResidueStabilizerHomOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    @MulAction.stabilizer Gal(L / K) (Ideal 𝒪[L]) _
        (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
        (𝓂[L] : Ideal 𝒪[L]) →*
      (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) := by
  letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  letI := galoisGroupIntegerRingSMulCommClassOfIsIntegralClosure K L
  letI := galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure K L
  exact Ideal.Quotient.stabilizerHom (𝓂[L] : Ideal 𝒪[L])
    (𝓂[K] : Ideal 𝒪[K]) Gal(L / K)

/-- The inertia subgroup for the actual integral-closure action on `𝒪[L]`. -/
def galoisGroupMaximalIdealInertiaOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Subgroup Gal(L / K) := by
  letI := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  exact (𝓂[L] : Ideal 𝒪[L]).toAddSubgroup.inertia Gal(L / K)

/-- The actual residue action obtained through the maximal-ideal stabilizer. -/
def galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L / K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
  (galoisGroupResidueStabilizerHomOfIsIntegralClosure K L).comp
    (galoisGroupMaximalIdealStabilizerHomOfIsIntegralClosure K L)

/-- The stabilizer representation obtained from the Galois group agrees with the canonical residue
stabilizer map. -/
theorem galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure_eq
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure K L =
      galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L := by
  ext σ x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- A Galois automorphism acts trivially on the residue field exactly when its stabilizer image is
trivial. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_stabilizerHom
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) :
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
      galoisGroupMaximalIdealStabilizerHomOfIsIntegralClosure K L σ ∈
        (galoisGroupResidueStabilizerHomOfIsIntegralClosure K L).ker := by
  rw [← galoisGroupResidueStabilizerHomFromGaloisGroupOfIsIntegralClosure_eq K L]
  rfl

/-- The kernel of the residue stabilizer action is the maximal-ideal inertia subgroup. -/
theorem galoisGroupResidueStabilizerHomOfIsIntegralClosure_ker_eq_maximalIdealInertia
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    (galoisGroupResidueStabilizerHomOfIsIntegralClosure K L).ker =
      (galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L).subgroupOf
        (@MulAction.stabilizer Gal(L / K) (Ideal 𝒪[L]) _
          (galoisGroupIntegerRingIdealMulActionOfIsIntegralClosure K L)
          (𝓂[L] : Ideal 𝒪[L])) := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  let := galoisGroupIntegerRingSMulCommClassOfIsIntegralClosure K L
  let := galoisGroupIntegerRingIdealDistribMulActionOfIsIntegralClosure K L
  exact Ideal.Quotient.ker_stabilizerHom (𝓂[L] : Ideal 𝒪[L])
    (𝓂[K] : Ideal 𝒪[K]) Gal(L / K)

/-- A Galois automorphism acts trivially on the residue field exactly when it belongs to
maximal-ideal inertia. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_mem_maximalIdealInertia
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L / K)) :
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
      σ ∈ galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_stabilizerHom]
  rw [galoisGroupResidueStabilizerHomOfIsIntegralClosure_ker_eq_maximalIdealInertia K L]
  rfl

/-- The kernel of the residue-field Galois representation is the maximal-ideal inertia subgroup. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_eq_maximalIdealInertia
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker =
      galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L := by
  ext σ
  exact galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_mem_maximalIdealInertia
    K L σ

/-- The actual integral-closure inertia subgroup has cardinality equal to the
mathlib ramification index over the base maximal ideal. -/
theorem galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdxIn
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Nat.card (galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L) =
      (𝓂[K] : Ideal 𝒪[K]).ramificationIdxIn 𝒪[L] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  let := galoisGroupIntegerRing_isGaloisGroup_of_isIntegralClosure K L
  let : Module.Finite 𝒪[K] 𝒪[L] :=
    integerRing_moduleFinite_of_isIntegralClosure K L
  let : Algebra.IsSeparable (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K]))
      (𝒪[L] ⧸ (𝓂[L] : Ideal 𝒪[L])) :=
    residueFieldAlgebra_isSeparable_of_valuationExtension K L
  let : Finite (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K])) := by
    change Finite 𝓀[K]
    infer_instance
  simpa [galoisGroupMaximalIdealInertiaOfIsIntegralClosure] using
    (Ideal.card_inertia_eq_ramificationIdxIn
      (R := 𝒪[K]) (S := 𝒪[L]) (G := Gal(L / K))
      (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]))

/-- The actual integral-closure inertia cardinality, rewritten with the
concrete ramification index of the valuation-integer-ring extension. -/
theorem galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdx
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Nat.card (galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L) =
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] := by
  let := galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  let := galoisGroupIntegerRing_isGaloisGroup_of_isIntegralClosure K L
  rw [galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdxIn K L]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx
    (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) Gal(L / K)

/-- The kernel cardinality of the actual integral-closure residue action,
rewritten using the concrete ramification index. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_ramificationIdx
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Nat.card (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker =
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_eq_maximalIdealInertia K L]
  exact galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdx K L

/-- If the valuation-integer-ring extension has ramification index one, then
the actual integral-closure residue action has kernel of cardinality one. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_one_of_ramificationIdx_eq_one
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (h :
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1) :
    Nat.card (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker = 1 := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_ramificationIdx K L, h]


end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_FiniteUnramified
attribute [-instance] _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.CyclicCohomology.mem_chosenBaseUniformizerPowSubmodule_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
# Finite unramified valued extensions

Develops the ideal, residue-field, Galois, trace, and norm consequences of a
finite valued extension with ramification index one and full residue degree.
-/

namespace LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel

/-- An unramified valued extension has ramification index one. -/
theorem unramifiedValuation_ramificationIdx_eq_one
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] [IsUnramifiedValuedExtension K L] :
    (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1 :=
  IsUnramifiedValuedExtension.maximalIdeal_ramificationIdx_eq_one
    (K := K) (L := L)

/-- For an unramified valued extension, the residue-field degree equals the field-extension degree.
For an unramified valued extension, the residue-field degree equals the field-extension degree. -/
theorem unramifiedValuation_residue_finrank_eq_finrank
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] [IsUnramifiedValuedExtension K L] :
    Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L := by
  have h :=
    LocalFieldTheory.maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank K L
  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp,
    unramifiedValuation_ramificationIdx_eq_one K L, one_mul] at h
  exact h

end IsNonarchimedeanLocalField

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField
open Filter

/-- In an actual unramified valuation extension, the image of the base maximal
ideal is the maximal ideal upstairs. -/
theorem maximalIdeal_map_eq_maximalIdeal_of_unramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Ideal.map (algebraMap 𝒪[K] 𝒪[L]) (𝓂[K] : Ideal 𝒪[K]) =
      (𝓂[L] : Ideal 𝒪[L]) := by
  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ := by
    exact Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  have hfact := Ideal.map_algebraMap_eq_finsetProd_pow
    (R := 𝒪[L]) (S := 𝒪[K]) (p := (𝓂[K] : Ideal 𝒪[K])) hp
  have hfin : ((𝓂[K] : Ideal 𝒪[K]).primesOver 𝒪[L]).toFinset =
      ({(𝓂[L] : Ideal 𝒪[L])} : Finset (Ideal 𝒪[L])) := by
    ext P
    simp [IsLocalRing.primesOver_eq 𝒪[L] hp]
  rw [hfin] at hfact
  simpa [LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_ramificationIdx_eq_one K L]
    using hfact

/-- A base DVR uniformizer remains a DVR uniformizer after an actual
unramified valuation extension. -/
theorem integerRingMap_uniformizer_irreducible_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Irreducible (integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  calc
    (𝓂[L] : Ideal 𝒪[L]) =
        Ideal.map (algebraMap 𝒪[K] 𝒪[L]) (𝓂[K] : Ideal 𝒪[K]) :=
      (maximalIdeal_map_eq_maximalIdeal_of_unramifiedValuation K L).symm
    _ = Ideal.map (algebraMap 𝒪[K] 𝒪[L])
        (Ideal.span ({chosenIntegerRingUniformizer K} : Set 𝒪[K])) := by
          rw [chosenIntegerRingUniformizer_maximalIdeal_eq K]
    _ = Ideal.span
        ({integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)} :
          Set 𝒪[L]) := by
          rw [Ideal.map_span, Set.image_singleton]
          rfl

/-- In an actual unramified valuation extension, the integer-ring map sends
`𝓂_K^n` into `𝓂_L^n`.  The proof uses the base uniformizer as an upstairs
uniformizer, which is the local source needed before comparing graded
principal-unit quotients with residue fields. -/
theorem integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) {a : 𝒪[K]} (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) :
    integerRingMapOfValuationExtension K L a ∈ (𝓂[L] ^ n : Ideal 𝒪[L]) := by
  let πK : 𝒪[K] := chosenIntegerRingUniformizer K
  have hπL : Irreducible (integerRingMapOfValuationExtension K L πK) := by
    simpa [πK] using integerRingMap_uniformizer_irreducible_of_unramifiedValuation K L
  have ha_span : a ∈ Ideal.span ({πK ^ n} : Set 𝒪[K]) := by
    simpa [πK, maximalIdeal_pow_eq_span_uniformizer_pow K n] using ha
  rcases (Ideal.mem_span_singleton.mp ha_span) with ⟨r, hr⟩
  rw [maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducible L
    (integerRingMapOfValuationExtension K L πK) hπL n]
  rw [Ideal.mem_span_singleton]
  refine ⟨integerRingMapOfValuationExtension K L r, ?_⟩
  simp [integerRingMapOfValuationExtension, hr, map_pow]

/-- The additive map on `𝓂^n` induced by base extension in an actual
unramified valuation extension. -/
def maximalIdealPowMapOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) →+ ((𝓂[L] ^ n : Ideal 𝒪[L]) : Type u) where
  toFun a :=
    ⟨integerRingMapOfValuationExtension K L (a : 𝒪[K]),
      integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation K L n a.2⟩
  map_zero' := by
    ext
    simp [integerRingMapOfValuationExtension]
  map_add' a b := by
    ext
    simp [integerRingMapOfValuationExtension]

/-- The map on maximal-ideal powers induced by an unramified extension is given by the integer-ring
inclusion. -/
@[simp]
theorem maximalIdealPowMapOfUnramifiedValuation_apply (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    (maximalIdealPowMapOfUnramifiedValuation K L n a : 𝒪[L]) =
      integerRingMapOfValuationExtension K L (a : 𝒪[K]) :=
  rfl

/-- In an actual unramified valuation extension, base extension sends
`U_K^n` into `U_L^n`. -/
theorem integerUnitsMapOfValuationExtension_mem_principalUnits_of_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) {u : 𝒪[K]ˣ} (hu : u ∈ principalUnits K n) :
    integerUnitsMapOfValuationExtension K L u ∈ principalUnits L n := by
  rw [mem_principalUnits_iff] at hu ⊢
  have hmap :=
    integerRingMap_mem_maximalIdeal_pow_of_unramifiedValuation K L n hu
  simpa [integerUnitsMapOfValuationExtension_apply, integerRingMapOfValuationExtension,
    sub_eq_add_neg] using hmap

/-- Base extension restricted to the `n`-th principal-unit group in an actual
unramified valuation extension. -/
def principalUnitsMapOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) :
    principalUnits K n →* principalUnits L n where
  toFun u :=
    ⟨integerUnitsMapOfValuationExtension K L u.1,
      integerUnitsMapOfValuationExtension_mem_principalUnits_of_unramifiedValuation
        K L n u.2⟩
  map_one' := by
    ext
    simp
  map_mul' u v := by
    ext
    simp

/-- The map on principal units for an unramified extension is induced by the integer-ring inclusion.
The map on principal units for an unramified extension is induced by the integer-ring inclusion. -/
@[simp]
theorem principalUnitsMapOfUnramifiedValuation_apply (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (u : principalUnits K n) :
    ((principalUnitsMapOfUnramifiedValuation K L n u : principalUnits L n) :
        𝒪[L]ˣ) =
      integerUnitsMapOfValuationExtension K L u.1 :=
  rfl

/-- Base extension on successive principal-unit quotients in an actual
unramified valuation extension. -/
def principalUnitsSuccQuotMapOfUnramifiedValuation (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) :
    PrincipalUnitsSuccQuot K n →* PrincipalUnitsSuccQuot L n :=
  principalUnitsSuccQuotLift n
    ((principalUnitsSuccQuotMk L n).comp
      (principalUnitsMapOfUnramifiedValuation K L n))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        principalUnitsSuccQuotMk_eq_one_iff]
      change ((principalUnitsMapOfUnramifiedValuation K L n u :
        principalUnits L n) : 𝒪[L]ˣ) ∈ principalUnits L (n + 1)
      simpa [principalUnitsMapOfUnramifiedValuation_apply]
        using integerUnitsMapOfValuationExtension_mem_principalUnits_of_unramifiedValuation
          K L (n + 1) (u := u.1) hu)

/-- The induced map on successive principal-unit quotients sends a class to the class of its
included representative. -/
@[simp]
theorem principalUnitsSuccQuotMapOfUnramifiedValuation_mk (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (u : principalUnits K n) :
    principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotMk K n u) =
      principalUnitsSuccQuotMk L n
        (principalUnitsMapOfUnramifiedValuation K L n u) :=
  rfl

/-- For an unramified extension, the residue-field automorphism group has cardinality equal to the
field-extension degree. -/
theorem residueAlgEquiv_card_eq_finrank_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) = Module.finrank K L := by
  rw [residueAlgEquiv_card_eq_finrank K L,
    LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_residue_finrank_eq_finrank K L]

/-- For an unramified Galois extension, the residue automorphism group and field Galois group have
equal cardinality. -/
theorem residueAlgEquiv_card_eq_galoisGroup_card_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) = Nat.card Gal(L / K) := by
  rw [residueAlgEquiv_card_eq_finrank_of_unramifiedValuation K L,
    galoisGroup_card_eq_finrank K L]

/-- In an actual unramified valuation extension, the integral-closure residue
action has kernel of cardinality one. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_one_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Nat.card (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker = 1 :=
  galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_one_of_ramificationIdx_eq_one K L
    (LocalFieldTheory.IsNonarchimedeanLocalField.unramifiedValuation_ramificationIdx_eq_one K L)

/-- In an actual unramified valuation extension, the integral-closure residue
action is injective. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Injective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L) := by
  refine (MonoidHom.ker_eq_bot_iff _).mp ?_
  exact ((galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker).eq_bot_of_card_eq
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_one_of_unramifiedValuation
      K L)

/-- In an actual unramified valuation extension, the integral-closure residue
action is surjective onto the residue-field automorphism group. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_surjective_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Surjective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L) := by
  exact ((Nat.bijective_iff_injective_and_card
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L)).2
      ⟨galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
          K L,
        (residueAlgEquiv_card_eq_galoisGroup_card_of_unramifiedValuation K L).symm⟩).2

/-- In an actual unramified valuation extension, the integral-closure residue
action is bijective. -/
theorem galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Bijective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L) :=
  ⟨galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation K L,
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure_surjective_of_unramifiedValuation K L⟩

/-- The actual integral-closure residue action as an isomorphism in the
unramified valuation case. -/
noncomputable def galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Gal(L / K) ≃* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
  MulEquiv.ofBijective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L)
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation K L)

/-- The unramified Galois-to-residue equivalence sends an automorphism to its induced action on
residue classes. -/
@[simp]
theorem galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure_apply
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (σ : Gal(L / K)) :
    galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L σ =
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ :=
  rfl

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_ClassFormation_LocalBlocks_Tensor
attribute [-instance] _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue
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
theorem localTensorConjugation_one
    (vK : AbsoluteValue K ℝ)
    (z : LocalTensorAlgebra (L := L) vK) :
    localTensorConjugation vK (1 : L ≃ₐ[K] L) z = z := by
  induction z using OAI.tensorInductionOn with
  | tmul b x => simp
  | add x y hx hy => simp [hx, hy]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem localTensorConjugation_mul
    (vK : AbsoluteValue K ℝ) (σ τ : L ≃ₐ[K] L)
    (z : LocalTensorAlgebra (L := L) vK) :
    localTensorConjugation vK (σ * τ) z =
      localTensorConjugation vK σ
        (localTensorConjugation vK τ z) := by
  induction z using OAI.tensorInductionOn with
  | tmul b x => simp
  | add x y hx hy => simp [hx, hy]

/-- The natural Galois action on the unit group of the local tensor
algebra. -/
@[reducible]
noncomputable def localTensorUnitsAction
    (vK : AbsoluteValue K ℝ) :
    MulDistribMulAction
      (L ≃ₐ[K] L) (LocalTensorAlgebra (L := L) vK)ˣ where
  smul σ z :=
    Units.mapEquiv (localTensorConjugation vK σ).toMulEquiv z
  one_smul z := by
    apply Units.ext
    exact localTensorConjugation_one vK
      (z : LocalTensorAlgebra (L := L) vK)
  mul_smul σ τ z := by
    apply Units.ext
    exact localTensorConjugation_mul vK σ τ
      (z : LocalTensorAlgebra (L := L) vK)
  smul_mul σ x y := by
    apply Units.ext
    exact (localTensorConjugation vK σ).map_mul
      (x : LocalTensorAlgebra (L := L) vK)
      (y : LocalTensorAlgebra (L := L) vK)
  smul_one σ := by
    apply Units.ext
    exact (localTensorConjugation vK σ).map_one

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem localTensorUnitsAction_smul_coe
    (vK : AbsoluteValue K ℝ) (σ : L ≃ₐ[K] L)
    (z : (LocalTensorAlgebra (L := L) vK)ˣ) :
    letI := localTensorUnitsAction (K := K) (L := L) vK
    ((σ • z : (LocalTensorAlgebra (L := L) vK)ˣ) :
        LocalTensorAlgebra (L := L) vK) =
      localTensorConjugation vK σ
        (z : LocalTensorAlgebra (L := L) vK) :=
  rfl

/-- The isometric ring equivalence from the normed copy attached to
`w ∘ σ` to the normed copy attached to `w`. -/
noncomputable def conjugateWithAbsRingEquiv
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    WithAbs (absoluteValueConjugate w σ) ≃+* WithAbs w :=
  WithAbs.congr
    (absoluteValueConjugate w σ) w σ.toRingEquiv

omit [FiniteDimensional K L] [IsGalois K L] in
theorem conjugateWithAbsRingEquiv_isometry
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    Isometry (conjugateWithAbsRingEquiv w σ) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
theorem conjugateWithAbsRingEquiv_symm_isometry
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    Isometry (conjugateWithAbsRingEquiv w σ).symm := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
  change w (σ (σ⁻¹ x.ofAbs)) = w x.ofAbs
  exact congrArg w (σ.apply_symm_apply x.ofAbs)

/-- The canonical equivalence between the completions at `w ∘ σ` and
`w`, induced by `σ : L → L`. -/
noncomputable def conjugateCompletionRingEquiv
    (w : AbsoluteValue L ℝ) (σ : L ≃ₐ[K] L) :
    (absoluteValueConjugate w σ).Completion ≃+*
      w.Completion :=
  UniformSpace.Completion.mapRingEquiv
    (conjugateWithAbsRingEquiv w σ)
    (conjugateWithAbsRingEquiv_isometry w σ).continuous
    (conjugateWithAbsRingEquiv_symm_isometry w σ).continuous

section RightCosetCoordinates

universe uG uB

variable {G : Type uG} {B : Type uB}
    [Group G] [CommGroup B]
    (H : Subgroup G) [MulDistribMulAction H B]

@[simp]
theorem rightCosetCoefficient_mul_out (g : G) :
    (rightCosetCoefficient H g : G) *
        Quotient.out (Quotient.mk'' g :
          InducedRightCosets H) = g := by
  simp [rightCosetCoefficient]

theorem rightCoset_mk_mul_left
    (h : H) (g : G) :
    (Quotient.mk'' (h.1 * g) : InducedRightCosets H) =
      Quotient.mk'' g := by
  apply Quotient.sound'
  rw [QuotientGroup.rightRel_apply]
  simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left,
    one_mul] using H.inv_mem h.2

theorem rightCosetCoefficient_mul_left
    (h : H) (g : G) :
    rightCosetCoefficient H (h.1 * g) =
      h * rightCosetCoefficient H g := by
  apply Subtype.ext
  simp only [rightCosetCoefficient, Subgroup.coe_mul]
  rw [rightCoset_mk_mul_left H h g]
  simp only [mul_assoc]

/-- Restriction to one representative of each right coset identifies an
induced module with a product indexed by `H \ G`.  No commutativity or
cyclicity assumption on `G` is used. -/
noncomputable def inducedRightCosetCoordinates :
    InducedModule (B := B) H ≃*
      (InducedRightCosets H → B) where
  toFun f q := f.1 (Quotient.out q)
  invFun b := ⟨fun g =>
      rightCosetCoefficient H g •
        b (Quotient.mk'' g), by
    intro h g
    change
      rightCosetCoefficient H (h.1 * g) •
          b (Quotient.mk'' (h.1 * g)) =
        h •
          (rightCosetCoefficient H g •
            b (Quotient.mk'' g))
    rw [rightCosetCoefficient_mul_left H h g,
      rightCoset_mk_mul_left H h g, mul_smul]⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    change
      rightCosetCoefficient H g •
          f.1 (Quotient.out
            (Quotient.mk'' g : InducedRightCosets H)) =
        f.1 g
    calc
      rightCosetCoefficient H g •
          f.1 (Quotient.out
            (Quotient.mk'' g : InducedRightCosets H)) =
          f.1 ((rightCosetCoefficient H g : G) *
            Quotient.out
              (Quotient.mk'' g : InducedRightCosets H)) :=
        (f.2 (rightCosetCoefficient H g)
          (Quotient.out
            (Quotient.mk'' g : InducedRightCosets H))).symm
      _ = f.1 g := congrArg f.1
        (rightCosetCoefficient_mul_out H g)
  right_inv b := by
    funext q
    change
      rightCosetCoefficient H (Quotient.out q) •
          b (Quotient.mk'' (Quotient.out q)) =
        b q
    have hq :
        (Quotient.mk'' (Quotient.out q) :
          InducedRightCosets H) = q :=
      Quotient.out_eq' q
    rw [hq]
    have hc :
        rightCosetCoefficient H (Quotient.out q) = 1 := by
      apply Subtype.ext
      simp [rightCosetCoefficient, hq]
    rw [hc, one_smul]
  map_mul' f g := by
    funext q
    rfl

@[simp]
theorem inducedRightCosetCoordinates_apply
    (f : InducedModule (B := B) H)
    (q : InducedRightCosets H) :
    inducedRightCosetCoordinates H f q =
      f.1 (Quotient.out q) :=
  rfl

end RightCosetCoordinates

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Relative_Support
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.RelativeIdeleGroup.classInclusion_mk _root_.RelativeIdeleGroup.classNorm_mk _root_.TowerRelativeIdeleGroup.classGroupEquiv_mk _root_.TowerRelativeIdeleGroup.classNorm_mk _root_.TowerRelativeIdeleGroup.norm_principalIdele _root_.TowerRelativeIdeleGroup.towerRelativeIdeleEquiv_principalIdele _root_.bottomAdeleToTower_apply _root_.compositeToBaseNormQuotient_mk _root_.intermediateAdeleInclusion_tmul _root_.intermediateToCompositeNormQuotient_mk _root_.topFieldToOneStep_apply _root_.topFieldToTower_apply _root_.towerRelativeAdeleFlatten_tmul _root_.towerRelativeAdeleUnflatten_tmul
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

/-- Scalar extension of the chosen basis from `K` to `𝔸_K`. -/
noncomputable def relativeAdeleBasis :
    Module.Basis (RelativeAdeleBasisIndex (K := K) (L := L))
      (NumberField.AdeleRing (𝓞 K) K)
      (RelativeAdeleRing K L) :=
  Algebra.TensorProduct.basis
    (NumberField.AdeleRing (𝓞 K) K)
    (relativeExtensionBasis (K := K) (L := L))

/-- The `i`-th base-adele coefficient of a relative adele. -/
noncomputable def relativeAdeleCoefficient
    (z : RelativeAdeleRing K L)
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    NumberField.AdeleRing (𝓞 K) K :=
  (relativeAdeleBasis (K := K) (L := L)).repr z i

/-- Exact union of all exceptional coefficient places of a relative
adele. -/
noncomputable def relativeAdeleCoefficientSupport
    (z : RelativeAdeleRing K L) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact Finset.univ.biUnion fun i =>
    adeleNonIntegralPlaces
      (K := K)
      (relativeAdeleCoefficient
        (K := K) (L := L) z i)

omit [NumberField L] in
@[simp]
theorem mem_relativeAdeleCoefficientSupport_iff
    (z : RelativeAdeleRing K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ relativeAdeleCoefficientSupport
        (K := K) (L := L) z ↔
      ∃ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L) z i).2 w ∉
          w.adicCompletionIntegers K := by
  classical
  simp [relativeAdeleCoefficientSupport]

/-- The exact coefficient support of a relative idele contains the
exceptional places of the idele and its inverse. -/
noncomputable def relativeIdeleCoefficientSupport
    (z : RelativeIdeleGroup K L) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact
    relativeAdeleCoefficientSupport
        (K := K) (L := L)
        (z : RelativeAdeleRing K L) ∪
      relativeAdeleCoefficientSupport
        (K := K) (L := L)
        ((z⁻¹ : RelativeIdeleGroup K L) :
          RelativeAdeleRing K L)

omit [NumberField L] in
@[simp]
theorem mem_relativeIdeleCoefficientSupport_iff
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ relativeIdeleCoefficientSupport
        (K := K) (L := L) z ↔
      (∃ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L)
            (z : RelativeAdeleRing K L) i).2 w ∉
          w.adicCompletionIntegers K) ∨
      (∃ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L)
            ((z⁻¹ : RelativeIdeleGroup K L) :
              RelativeAdeleRing K L) i).2 w ∉
          w.adicCompletionIntegers K) := by
  classical
  simp [relativeIdeleCoefficientSupport]
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_Lattice
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

/-- One common nonzero integer scales every vector of the chosen
`K`-basis into the ring of integers of `L`. -/
theorem exists_integral_relativeBasis_scale :
    ∃ d : ℤ, d ≠ 0 ∧
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        IsIntegral ℤ
          (d • relativeExtensionBasis
            (K := K) (L := L) i) := by
  classical
  let : Algebra.IsAlgebraic ℤ L :=
    (IsFractionRing.isAlgebraic_iff' ℤ (𝓞 L) L).mp
      inferInstance
  let s : Finset L :=
    Finset.univ.image fun i :
      RelativeAdeleBasisIndex (K := K) (L := L) =>
        relativeExtensionBasis (K := K) (L := L) i
  obtain ⟨d, hd, hint⟩ :=
    Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  refine ⟨d, hd, ?_⟩
  intro i
  exact
    hint
      (relativeExtensionBasis (K := K) (L := L) i)
      (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ i, rfl⟩)

/-- The chosen common integral scale. -/
noncomputable def chosenRelativeBasisIntegralScale : ℤ :=
  Classical.choose
    (exists_integral_relativeBasis_scale
      (K := K) (L := L))

/-- The chosen integral scale is nonzero. -/
theorem chosenRelativeBasisIntegralScale_ne_zero :
    chosenRelativeBasisIntegralScale (K := K) (L := L) ≠ 0 :=
  (Classical.choose_spec
    (exists_integral_relativeBasis_scale
      (K := K) (L := L))).1

/-- The chosen integral scale is integral in the base field. -/
theorem chosenRelativeBasisIntegralScale_isIntegral
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    IsIntegral ℤ
      (chosenRelativeBasisIntegralScale (K := K) (L := L) •
        relativeExtensionBasis (K := K) (L := L) i) :=
  (Classical.choose_spec
    (exists_integral_relativeBasis_scale
      (K := K) (L := L))).2 i

/-- The integral scale viewed in the base field. -/
noncomputable def relativeBasisIntegralScaleInK : K :=
  algebraMap ℤ K
    (chosenRelativeBasisIntegralScale (K := K) (L := L))

/-- The base-field coercion of the chosen integral scale is nonzero. -/
theorem relativeBasisIntegralScaleInK_ne_zero :
    relativeBasisIntegralScaleInK (K := K) (L := L) ≠ 0 := by
  intro h
  have hc :
      (chosenRelativeBasisIntegralScale
        (K := K) (L := L) : K) =
        ((0 : ℤ) : K) := by
    simpa [relativeBasisIntegralScaleInK] using h
  exact
    chosenRelativeBasisIntegralScale_ne_zero
      (K := K) (L := L)
      (Int.cast_injective hc)

/-- The integral scale as a unit of `K`. -/
noncomputable def relativeBasisIntegralScaleUnit : Kˣ :=
  Units.mk0
    (relativeBasisIntegralScaleInK (K := K) (L := L))
    (relativeBasisIntegralScaleInK_ne_zero
      (K := K) (L := L))

/-- The chosen basis after multiplying every vector by the common
integral scale. -/
noncomputable def scaledRelativeExtensionBasis :
    Module.Basis
      (RelativeAdeleBasisIndex (K := K) (L := L)) K L :=
  (relativeExtensionBasis (K := K) (L := L)).unitsSMul
    fun _ => relativeBasisIntegralScaleUnit
      (K := K) (L := L)

/-- Evaluation and integrality properties of the scaled relative basis. -/

@[simp]
theorem scaledRelativeExtensionBasis_apply
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    scaledRelativeExtensionBasis (K := K) (L := L) i =
      relativeBasisIntegralScaleInK
          (K := K) (L := L) •
        relativeExtensionBasis (K := K) (L := L) i := by
  rw [scaledRelativeExtensionBasis,
    Module.Basis.unitsSMul_apply]
  rfl

/-- Every vector of the scaled relative basis is integral. -/
theorem scaledRelativeExtensionBasis_isIntegral
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    IsIntegral ℤ
      (scaledRelativeExtensionBasis
        (K := K) (L := L) i) := by
  simpa [scaledRelativeExtensionBasis_apply,
    relativeBasisIntegralScaleInK, Algebra.smul_def] using
      chosenRelativeBasisIntegralScale_isIntegral
        (K := K) (L := L) i

/-- The scaled basis vector as an actual element of `𝓞 L`. -/
noncomputable def scaledRelativeExtensionInteger
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    𝓞 L :=
  ⟨scaledRelativeExtensionBasis (K := K) (L := L) i,
    scaledRelativeExtensionBasis_isIntegral
      (K := K) (L := L) i⟩

/-- The named scaled integer is the corresponding scaled basis vector. -/

@[simp]
theorem scaledRelativeExtensionInteger_coe
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    (scaledRelativeExtensionInteger
        (K := K) (L := L) i : L) =
      scaledRelativeExtensionBasis (K := K) (L := L) i :=
  rfl
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Adele_IntegralTensorSupport_LocalTensorDecomposition
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

/-- The discriminant of the globally integral scaled relative basis,
viewed as an algebraic integer of the base field. -/
noncomputable def scaledRelativeBasisDiscriminantInteger :
    𝓞 K :=
  ⟨Algebra.discr K
      (scaledRelativeExtensionBasis (K := K) (L := L)),
    Algebra.discr_isIntegral K fun i =>
      scaledRelativeExtensionBasis_isIntegral
        (K := K) (L := L) i⟩

/-- Coercion and nonvanishing properties of the discriminant control element. -/

@[simp]
theorem scaledRelativeBasisDiscriminantInteger_coe :
    (scaledRelativeBasisDiscriminantInteger
        (K := K) (L := L) : K) =
      Algebra.discr K
        (scaledRelativeExtensionBasis (K := K) (L := L)) :=
  rfl

end LocalTensorDecompositionIntegralComparison
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Completion_LocalizedValuation
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Valuation rings of algebraic localizations

This file equips nonarchimedean absolute-value completions and their algebraic
localizations with the norm-induced valuation structures. It identifies the
localized valuation ring with the integral closure of the base valuation ring.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section LocalValuation

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)

omit [NumberField K] in
/-- A nonarchimedean absolute value makes its completion an ultrametric
space. -/
theorem completionIsUltrametricDist
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    IsUltrametricDist vK.Completion :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
      vK hvKna)

/-- The norm-induced valued-field structure on a nonarchimedean completion. -/
@[reducible]
noncomputable def finitePlaceCompletionValued
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    Valued vK.Completion ℝ≥0 :=
  letI : IsUltrametricDist vK.Completion :=
    completionIsUltrametricDist vK hvKna
  NormedField.toValued

/-- The valuation relation induced by the norm valuation on a
nonarchimedean completion. -/
@[reducible]
noncomputable def finitePlaceCompletionValuativeRel
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    ValuativeRel vK.Completion := by
  letI : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  exact ValuativeRel.ofValuation
    (Valued.v : Valuation vK.Completion ℝ≥0)

omit [NumberField K] in
/-- Membership in the valuation ring of a nonarchimedean completion is
equivalent to the usual norm bound by one, for the canonical norm-induced
valuation used in this file. -/
theorem finitePlaceCompletion_mem_integers_iff_norm_le_one
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (x : vK.Completion) :
    letI : Valued vK.Completion ℝ≥0 :=
      finitePlaceCompletionValued vK hvKna
    letI : ValuativeRel vK.Completion :=
      finitePlaceCompletionValuativeRel vK hvKna
    x ∈ 𝒪[vK.Completion] ↔ ‖x‖ ≤ 1 := by
  let : Valued vK.Completion ℝ≥0 :=
    finitePlaceCompletionValued vK hvKna
  let ν : Valuation vK.Completion ℝ≥0 := Valued.v
  let : ValuativeRel vK.Completion :=
    finitePlaceCompletionValuativeRel vK hvKna
  rw [Valuation.mem_integer_iff,
    ← map_one (ValuativeRel.valuation vK.Completion),
    ← Valuation.Compatible.vle_iff_le
      (v := ValuativeRel.valuation vK.Completion)]
  change ν x ≤ ν 1 ↔ _
  simp only [map_one]
  change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  exact NNReal.coe_le_coe


end LocalValuation
end
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

noncomputable instance
    chosenFinitePlaceBaseNontriviallyNormedField
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    NontriviallyNormedField
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  absoluteValueExtension_completionNontriviallyNormedField
    (HeightOneSpectrum.adicAbv K w₀)
    (RayClass.adicAbv_isNontrivial w₀)

noncomputable instance chosenFinitePlaceBaseIsUltrametricDist
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    IsUltrametricDist
      (ChosenFinitePlaceBaseCompletion (K := K) w₀) :=
  completionIsUltrametricDist
    (HeightOneSpectrum.adicAbv K w₀)
    (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_Cohomology_SPlaces_OutsideIntegralInduced_LocalInduction_Spine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Shared completion spine for integral local induction

This file names the coherent algebra, valuation, and integral-closure
structures used by every integral local-induction leaf.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

namespace LocalInductionInternal

variable (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L)

/-- The canonical valued structure on the completed base place. -/
@[reducible]
noncomputable def baseValued
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    Valued vK.Completion ℝ≥0 :=
  finitePlaceCompletionValued vK hvKna

/-- The canonical valuative relation on the completed base place. -/
@[reducible]
noncomputable def baseValuativeRel
    (hvKna : IsNonarchimedean (vK : K → ℝ)) :
    letI : Valued vK.Completion ℝ≥0 := baseValued vK hvKna
    ValuativeRel vK.Completion :=
  finitePlaceCompletionValuativeRel vK hvKna

end LocalInductionInternal
end
end


