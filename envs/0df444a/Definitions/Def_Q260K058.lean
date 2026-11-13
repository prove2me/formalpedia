-- Prove2me | Definitions.Def_Q260K058
-- name    : Q260K058
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T05:37:39.893353+00:00
-- url     : https://prove2.me/theorems/2afa83d8-5777-4593-be03-fc4763242184
-- title:
--   Definitions bundle Q260K058 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 8 definitions and 14 theorems. The definitions and types are `OAI.Generator.Tracial.traceFreeInclusion`, `OAI.Generator.Tracial.traceFreeLeftAction`, `OAI.Generator.Tracial.traceFreeLeftOnPreHilbert`, `OAI.Generator.Tracial.traceHilbertActionCStar`, `OAI.Generator.Tracial.traceHilbertBoundCStar`, `OAI.Generator.Tracial.traceHilbertBoundLE`, `OAI.Generator.Tracial.traceHilbertBoundOrder`, `OAI.Generator.Tracial.traceHilbertBoundPreorder`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_TraceHilbert`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/TraceHilbert.lean).
--
--   **Imports.** It imports the bundle `Q260K057` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K021`; the statements `OAI_KadisonKastler_PointedMatrixSites_spatialMatrix_reference_approximation` and `OAI_KadisonKastler_regularCore_spatial_of_matrix_corner`; the proofs of `OAI_KadisonKastler_PointedMatrixSites_block_coisometry`, `OAI_KadisonKastler_PointedMatrixSites_spatialMatrix_reference_approximation`, `OAI_KadisonKastler_projectionCentralSpace_scalar`, `OAI_KadisonKastler_regularCore_spatial_of_matrix_corner` and `OAI_KadisonKastler_vector_bicentralizer_scalar_of_modular_coisometries`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K057

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A separate type with the constructed trace inner product. Its norm is the
trace two-norm; the original concrete algebra retains its operator norm.
Lean's inner product is linear in the second argument. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.traceHilbertStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

theorem traceFreeCopy_norm_sq (x : M.toStarSubalgebra) :
    ‖copy x‖^2 = (τ₀ (star x*x)).re := by
  rw [← traceFreeCopy_inner hfactor hdiff hfinite hunit]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (copy x)).symm

def traceFreeInclusion : E →ₗᵢ[ℂ] TraceFreeHilbert hfactor hdiff hfinite hunit :=
  UniformSpace.Completion.toComplₗᵢ

@[simp] theorem traceFreeInclusion_inner (x y : M.toStarSubalgebra) :
    inner ℂ (traceFreeInclusion hfactor hdiff hfinite hunit (copy x))
      (traceFreeInclusion hfactor hdiff hfinite hunit (copy y)) = τ₀ (star x*y) :=
  UniformSpace.Completion.inner_coe (𝕜 := ℂ) (copy x) (copy y)

theorem traceFreeInclusion_denseRange :
    DenseRange (traceFreeInclusion hfactor hdiff hfinite hunit) :=
  UniformSpace.Completion.denseRange_coe

end

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertBoundCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertBoundOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertBoundPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceHilbertBoundLE : LE M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toLE
local instance traceHilbertBoundStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

theorem traceFreeTrace_mul_square_le (a x : M.toStarSubalgebra) :
    (τ₀ (star (a*x)*(a*x))).re ≤ ‖a‖^2 * (τ₀ (star x*x)).re := by
  have hp : 0 ≤ algebraMap ℝ M.toStarSubalgebra (‖a‖^2)-star a*a :=
    sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq)
  have h := (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.1 _
    (star_left_conjugate_nonneg hp x)
  have he : star x*(algebraMap ℝ M.toStarSubalgebra (‖a‖^2)-star a*a)*x =
      (‖a‖^2) • (star x*x)-star (a*x)*(a*x) := by
    simp only [Algebra.algebraMap_eq_smul_one,mul_sub,sub_mul,mul_smul_comm,
      smul_mul_assoc,mul_one,star_mul,mul_assoc]
  rw [he,map_sub, ContinuousLinearMap.map_smul_of_tower, Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  exact sub_nonneg.mp h

theorem traceFreeCopy_mul_norm_le (a x : M.toStarSubalgebra) :
    ‖copy (a*x)‖ ≤ ‖a‖ * ‖copy x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, traceFreeCopy_norm_sq, traceFreeCopy_norm_sq]
  exact traceFreeTrace_mul_square_le hfactor hdiff hfinite hunit a x

end

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertActionCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertActionOrder_rdbac0b_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertActionStarOrder_rdbac0b_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit

local instance traceHilbertOperatorCStar_rdbac0b_1 : CStarAlgebra (K →L[ℂ] K) := {}
def traceFreeLeftOnPreHilbert (a : M.toStarSubalgebra) : E →L[ℂ] E :=
  LinearMap.mkContinuous (LinearMap.mulLeft ℂ (copy a)) ‖a‖ (by
    intro x
    obtain ⟨x,rfl⟩ := (copy).surjective x
    exact traceFreeCopy_mul_norm_le hfactor hdiff hfinite hunit a x)

@[simp] theorem traceFreeLeftOnPreHilbert_apply (a : M.toStarSubalgebra) (x : E) :
    traceFreeLeftOnPreHilbert hfactor hdiff hfinite hunit a x = copy a*x := rfl

def traceFreeLeftAction (a : M.toStarSubalgebra) : K →L[ℂ] K :=
  ((ι).toContinuousLinearMap.comp (traceFreeLeftOnPreHilbert hfactor hdiff hfinite hunit a)).extend
    (ι).toContinuousLinearMap

local notation "L" => traceFreeLeftAction hfactor hdiff hfinite hunit

@[simp] theorem traceFreeLeftAction_inclusion (a : M.toStarSubalgebra) (x : E) :
    L a (ι x) = ι (copy a*x) := by
  exact ContinuousLinearMap.extend_eq
    ((ι).toContinuousLinearMap.comp (traceFreeLeftOnPreHilbert hfactor hdiff hfinite hunit a))
    (e := (ι).toContinuousLinearMap) (traceFreeInclusion_denseRange hfactor hdiff hfinite hunit)
    ((ι).isometry.isUniformInducing) x

@[simp] theorem traceFreeLeftAction_coe (a : M.toStarSubalgebra) (x : E) :
    L a (x : K) = ((copy a*x : E) : K) :=
  traceFreeLeftAction_inclusion hfactor hdiff hfinite hunit a x

@[simp] theorem traceFreeLeftAction_one : L 1 = 1 := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [traceFreeLeftAction_coe,map_one,one_mul,one_apply_eq_self]

@[simp] theorem traceFreeLeftAction_mul (a b : M.toStarSubalgebra) :
    L (a*b) = L a*L b := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [mul_apply_eq_comp,traceFreeLeftAction_coe,map_mul,mul_assoc]

@[simp] theorem traceFreeLeftAction_add (a b : M.toStarSubalgebra) :
    L (a+b) = L a+L b := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [add_apply,traceFreeLeftAction_coe,map_add,add_mul,UniformSpace.Completion.coe_add]

@[simp] theorem traceFreeLeftAction_smul (c : ℂ) (a : M.toStarSubalgebra) :
    L (c • a) = c • L a := by
  apply ContinuousLinearMap.ext
  intro x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (L (c • a)).continuous ((c • L a : K →L[ℂ] K)).continuous) ?_
  intro b
  change L (c • a) (ι b) = c • L a (ι b)
  rw [traceFreeLeftAction_inclusion,traceFreeLeftAction_inclusion,map_smul,smul_mul_assoc]
  exact (ι).map_smul c _

@[simp] theorem traceFreeLeftAction_zero : L 0 = 0 := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [traceFreeLeftAction_coe,map_zero,zero_mul,zero_apply,UniformSpace.Completion.coe_zero]

end

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators

end Generator.Tracial

end

end OAI
end


