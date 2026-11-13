-- Prove2me | Definitions.Def_Q260K021
-- name    : Q260K021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T05:58:55.523782+00:00
-- url     : https://prove2.me/theorems/671893d6-6389-437f-8419-5561448f8dbf
-- title:
--   Definitions bundle Q260K021 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 6 definitions and 11 theorems. The definitions and types are `OAI.Generator.Tracial.traceFreeHilbertAction`, `OAI.Generator.Tracial.traceFreeHilbertVector`, `OAI.Generator.Tracial.traceFreeRightAction`, `OAI.Generator.Tracial.traceFreeRightOnPreHilbert`, `OAI.Generator.Tracial.traceHilbertOperatorCStar`, `OAI.Generator.Tracial.traceHilbertRightCStar`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_TraceHilbert`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/TraceHilbert.lean), [`KadisonKastler_Basic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/Basic.lean).
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundle `Q260K058` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q260K028`, `Q260K059` and `Q260K061`; the proof of `OAI.KadisonKastler.concrete_ucp_starEquiv_of_published`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
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
import Mathlib.Analysis.Normed.Group.Bounded
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
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K058

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.traceHilbertActionCStar
local instance traceHilbertActionOrder_r23e757_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertActionStarOrder_r23e757_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceHilbertOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "L" => traceFreeLeftAction hfactor hdiff hfinite hunit

@[simp] theorem traceFreeLeftAction_star (a : M.toStarSubalgebra) : L (star a) = star (L a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  refine UniformSpace.Completion.induction_on₂ x y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b c
  obtain ⟨b,rfl⟩ := (copy).surjective b
  obtain ⟨c,rfl⟩ := (copy).surjective c
  rw [traceFreeLeftAction_coe,traceFreeLeftAction_coe]
  rw [UniformSpace.Completion.inner_coe,UniformSpace.Completion.inner_coe]
  change τ₀ (star (star a*b)*c) = τ₀ (star b*(a*c))
  simp only [star_mul,star_star,mul_assoc]

def traceFreeHilbertAction : M.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun := L
  map_one' := traceFreeLeftAction_one hfactor hdiff hfinite hunit
  map_mul' := traceFreeLeftAction_mul hfactor hdiff hfinite hunit
  map_zero' := traceFreeLeftAction_zero hfactor hdiff hfinite hunit
  map_add' := traceFreeLeftAction_add hfactor hdiff hfinite hunit
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,traceFreeLeftAction_smul,traceFreeLeftAction_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' := traceFreeLeftAction_star hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

@[simp] theorem traceFreeHilbertAction_inclusion (a x : M.toStarSubalgebra) :
    π a (ι (copy x)) = ι (copy (a*x)) := by
  exact (traceFreeLeftAction_inclusion hfactor hdiff hfinite hunit a (copy x)).trans
    (congrArg ι ((copy).map_mul a x).symm)

def traceFreeHilbertVector : K := ι (copy 1)

local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

@[simp] theorem traceFreeHilbertAction_vector (a : M.toStarSubalgebra) :
    π a Ω = ι (copy a) := by
  change π a (ι (copy 1)) = _
  rw [traceFreeHilbertAction_inclusion,mul_one]

theorem traceFreeHilbertAction_injective : Function.Injective π := by
  intro a b hab
  have hv := congrArg (fun T : K →L[ℂ] K => T Ω) hab
  simp only [traceFreeHilbertAction_vector] at hv
  exact (copy).injective ((ι).injective hv)

theorem traceFreeHilbertAction_norm (a : M.toStarSubalgebra) : ‖π a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map π (traceFreeHilbertAction_injective hfactor hdiff hfinite hunit) a

end

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertRightCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertRightOrder_r23e757_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertRightStarOrder_r23e757_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
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
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local instance traceHilbertRightOperatorCStar_r23e757_1 : CStarAlgebra (K →L[ℂ] K) := {}
theorem traceFreeCopy_star_norm (x : M.toStarSubalgebra) : ‖copy (star x)‖ = ‖copy x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [traceFreeCopy_norm_sq,traceFreeCopy_norm_sq,star_star,
    (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.2]

theorem traceFreeCopy_mul_norm_le_right (a x : M.toStarSubalgebra) :
    ‖copy (x*a)‖ ≤ ‖a‖ * ‖copy x‖ := by
  rw [← traceFreeCopy_star_norm hfactor hdiff hfinite hunit (x*a),star_mul]
  simpa only [norm_star,traceFreeCopy_star_norm] using
    traceFreeCopy_mul_norm_le hfactor hdiff hfinite hunit (star a) (star x)

def traceFreeRightOnPreHilbert (a : M.toStarSubalgebra) : E →L[ℂ] E :=
  LinearMap.mkContinuous (LinearMap.mulRight ℂ (copy a)) ‖a‖ (by
    intro x
    obtain ⟨x,rfl⟩ := (copy).surjective x
    exact traceFreeCopy_mul_norm_le_right hfactor hdiff hfinite hunit a x)

def traceFreeRightAction (a : M.toStarSubalgebra) : K →L[ℂ] K :=
  ((ι).toContinuousLinearMap.comp (traceFreeRightOnPreHilbert hfactor hdiff hfinite hunit a)).extend
    (ι).toContinuousLinearMap

local notation "R" => traceFreeRightAction hfactor hdiff hfinite hunit

@[simp] theorem traceFreeRightAction_inclusion (a : M.toStarSubalgebra) (x : E) :
    R a (ι x) = ι (x*copy a) := by
  exact ContinuousLinearMap.extend_eq
    ((ι).toContinuousLinearMap.comp (traceFreeRightOnPreHilbert hfactor hdiff hfinite hunit a))
    (e := (ι).toContinuousLinearMap) (traceFreeInclusion_denseRange hfactor hdiff hfinite hunit)
    ((ι).isometry.isUniformInducing) x

@[simp] theorem traceFreeRightAction_coe (a : M.toStarSubalgebra) (x : E) :
    R a (x : K) = ((x*copy a : E) : K) :=
  traceFreeRightAction_inclusion hfactor hdiff hfinite hunit a x

@[simp] theorem traceFreeRightAction_vector (a : M.toStarSubalgebra) : R a Ω = ι (copy a) := by
  change R a (ι (copy 1)) = _
  rw [traceFreeRightAction_inclusion,map_one,one_mul]

end

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The concrete Kadison–Kastler distance

The distance is the operator-norm Hausdorff distance between the closed unit
balls of two concrete, unital von Neumann algebras.  All Hilbert spaces are
allowed, including the zero space. The elementary estimates belong to §2 of
*Universal strong Kadison–Kastler stability* (2026).
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strict distance bound supplies a contractive approximant in the other algebra. -/
theorem exists_unitBall_approx {M N : VonNeumannAlgebra H} {x : H →L[ℂ] H}
    (hx : x ∈ unitBall M) {r : ℝ} (hr : kkDistance M N < r) :
    ∃ y ∈ unitBall N, ‖x - y‖ < r := by
  simpa only [dist_eq_norm] using
    Metric.exists_dist_lt_of_hausdorffDist_lt hx hr (unitBall_hausdorffEDist_ne_top M N)

end

end KadisonKastler

end OAI
end


