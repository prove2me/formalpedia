-- Prove2me | Definitions.Def_OAIQ4Kq011
-- name    : OAIQ4Kq011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T08:47:40.147998+00:00
-- url     : https://prove2.me/theorems/575fca9b-4659-4618-ad8c-9be46a480773
-- title:
--   Definitions bundle OAIQ4Kq011 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kaplansky.kaplansky_quasitrace_counterexample`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 21 definitions, 2 instances and 28 theorems. The definitions and types are `OAI.Kaplansky.actualCuntzDimensionState`, `OAI.Kaplansky.actualDefectA`, `OAI.Kaplansky.actualDefectAlgebraSemiring`, `OAI.Kaplansky.actualDefectAmplificationEquiv`, `OAI.Kaplansky.actualDefectB`, `OAI.Kaplansky.actualDefectMatrixSemiring`, `OAI.Kaplansky.actualGeneratorNat`, `OAI.Kaplansky.twistedGraphBundleChartNormalization`, `OAI.Kaplansky.twistedGraphBundleCoordinates`, `OAI.Kaplansky.twistedGraphBundleNormalization`, `OAI.Kaplansky.twistedGraphBundlePullbackRelativeIso`, `OAI.Kaplansky.twistedGraphBundleRelativeIso`, `OAI.Kaplansky.twistedGraphLineUnit`, `OAI.Kaplansky.twistedLocalSectionHomeomorph`, `OAI.Kaplansky.twistedLocalSectionRelativeIso`, `OAI.Kaplansky.twistedRestrictedSection`, `OAI.Kaplansky.twistedRestrictedSectionRelativeMap`, `OAI.Kaplansky.twistedSlopeEvaluationEquiv`, `OAI.Kaplansky.twistedStandardChartHomeomorph`, `OAI.Kaplansky.twistedStandardLineUnit`, `OAI.Kaplansky.twistedStandardSectionCoordinates`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: [`BundleTests_Normalization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/BundleTests/Normalization.lean), [`BundleTests_Obstruction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/BundleTests/Obstruction.lean), [`BundleTests_Smooth`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/BundleTests/Smooth.lean), [`BundleTests_Twisted`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/BundleTests/Twisted.lean), [`Kaplansky_ActualAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/ActualAlgebra.lean).
--
--   **Imports.** It imports the bundles `OAIQ4Kq009` and `OAIQ4Kq010` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.Kaplansky.mainTarget_of_actualDefectQuasitrace`; the proofs of `OAI.Kaplansky.kaplansky_quasitrace_counterexample` and `OAI.Kaplansky.mainTarget_of_actualDefectQuasitrace`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ4Kq009
import Definitions.Def_OAIQ4Kq010

section
-- module Solutions.OAIQ4_Kq.BundleTests_Twisted
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Twisted hyperplane bundles, zeros, graph coordinates, and frame sections. -/

section
open Bundle Topology Set
namespace Kaplansky
open ComplexGrassmann
variable {ι A : Type} [Fintype ι] [TopologicalSpace A] (K : ι → ℕ)
  (U : Set (ProjectiveProduct K)) (e : U ≃ₜ A)
  (F : ∀ i, GraphFrame 1 (K i))
  (hF : U ⊆ (projectiveProductGraphChart K F).source)

theorem continuous_productGraphLineUnit (i : Option ι) :
    Continuous (fun a => TotalSpace.mk' ℂ a (productGraphLineUnit K U e F hF i a)) := by
  cases i with
  | none =>
    apply continuous_iff_continuousAt.mpr
    intro a
    rw [FiberBundle.continuousAt_section]
    exact continuousAt_const
  | some i =>
    exact (hyperplaneEvaluationHomeomorph (productGraphLineProjection K U e i)
      (productGraphLineVector K U e F i) (productGraphLineVector_mem K U e F hF i)
      (productGraphLineVector_ne_zero K U e F i) (continuous_productGraphLineVector K U e F hF i)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)

end Kaplansky

end

section
open Bundle Topology Set CategoryTheory
namespace Kaplansky
open ComplexGrassmann
variable {ι A : Type} [Fintype ι] [TopologicalSpace A] (K : ι → ℕ) (h : ℕ)
  (U : Set (ProjectiveProduct (twistedProjectiveDimensions K h))) (e : U ≃ₜ A)
  (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
  (hF : U ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source)

def twistedGraphLineUnit (s : TwistedHyperplaneSlot K h) (a : A) :
    (pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U e)).Fiber a :=
  tensorLinePair
    (pullbackLineCore (productLineCore (twistedProjectiveDimensions K h) (twistedOldLabel K h s)) (chartBaseMap U e))
    (pullbackLineCore (productLineCore (twistedProjectiveDimensions K h) (some none)) (chartBaseMap U e)) a
    (productGraphLineUnit (twistedProjectiveDimensions K h) U e F hF (twistedOldLabel K h s) a)
    (productGraphLineUnit (twistedProjectiveDimensions K h) U e F hF (some none) a)

theorem twistedGraphLineUnit_ne_zero (s : TwistedHyperplaneSlot K h) (a : A) :
    twistedGraphLineUnit K h U e F hF s a ≠ 0 :=
  tensorLinePair_ne_zero _ _ _ _ _
    (productGraphLineUnit_ne_zero _ _ _ _ _ _ _) (productGraphLineUnit_ne_zero _ _ _ _ _ _ _)

theorem continuous_twistedGraphLineUnit (s : TwistedHyperplaneSlot K h) :
    Continuous (fun a => TotalSpace.mk' ℂ a (twistedGraphLineUnit K h U e F hF s a)) := by
  exact continuous_tensorLinePair_section _ _ _ _
    (continuous_productGraphLineUnit _ _ _ _ _ _) (continuous_productGraphLineUnit _ _ _ _ _ _)

/-- Genuine linear coordinates for the original twisted bundle, over
any subset of any product graph chart. -/
def twistedGraphBundleCoordinates : twistedGraphBundleDomain K h U ≃ₜ
    A × (TwistedHyperplaneSlot K h → ℂ) :=
  (lineSumChartPullbackHomeomorph (twistedHyperplaneLineCore K h) U e).symm.trans
    (finiteLineFrameHomeomorph
      (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U e))
      (twistedGraphLineUnit K h U e F hF) (twistedGraphLineUnit_ne_zero K h U e F hF)
      (continuous_twistedGraphLineUnit K h U e F hF))

theorem twistedGraphBundleCoordinates_zero_iff (z : twistedGraphBundleDomain K h U) :
    (twistedGraphBundleCoordinates K h U e F hF z).2 = 0 ↔ z.1.2 = 0 :=
  (finiteLineFrameEquiv _ (twistedGraphLineUnit K h U e F hF)
    (twistedGraphLineUnit_ne_zero K h U e F hF) _).map_eq_zero_iff

def twistedGraphBundleRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso (twistedGraphBundleCoordinates K h U e F hF)
    (Subtype.val ⁻¹' nonzeroBundle) {z : A × (TwistedHyperplaneSlot K h → ℂ) | z.2 ≠ 0}
    (fun z => (mem_nonzeroBundle z.1).trans
      (not_congr (twistedGraphBundleCoordinates_zero_iff K h U e F hF z)).symm) n

def twistedGraphBundleNormalization (n : ℕ) :=
  (twistedGraphBundleRelativeIso K h U e F hF n).hom ≫
    productPairProjection (B := A) ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)) n

end Kaplansky

end

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedSlopeEvaluationEquiv : ProjectiveProductModel (twistedProjectiveDimensions K h) ≃L[ℂ]
    (TwistedHyperplaneSlot K h → ℂ) :=
  (productSlopeEvaluationEquiv (twistedProjectiveDimensions K h)).trans
    (LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) (twistedSlotEquiv K h).symm).toContinuousLinearEquiv

abbrev twistedStandardChartHomeomorph := canonicalProductChartHomeomorph (twistedProjectiveDimensions K h)

def twistedStandardLineUnit (s : TwistedHyperplaneSlot K h)
    (A : ProjectiveProductModel (twistedProjectiveDimensions K h)) :=
  twistedGraphLineUnit K h (twistedStandardChart K h).source
    (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl s A

/-- Actual section coordinates in the proved tensor graph trivialization. -/
def twistedStandardSectionCoordinates
    (A : ProjectiveProductModel (twistedProjectiveDimensions K h)) : TwistedHyperplaneSlot K h → ℂ :=
  fun s => (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
    twistedHyperplaneSection K h (canonicalProductGraphPoint (twistedProjectiveDimensions K h) A)) s /
    (show ℂ from twistedStandardLineUnit K h s A)

theorem twistedStandard_coordinate_evaluation
    (i : Option ι) (j : Fin (1+twistedProjectiveDimensions K h i))
    (A : ProjectiveProductModel (twistedProjectiveDimensions K h)) :
    (show ℂ from twistedCoordinateSection K h i j
        (canonicalProductGraphPoint (twistedProjectiveDimensions K h) A)) /
      (show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h)
        (twistedStandardChart K h).source (twistedStandardChartHomeomorph K h)
        (twistedStandardFrames K h) subset_rfl (some i) A) =
      coordinateFunctional j (graphLineVector (twistedStandardFrames K h i) (A i)) := by
  rw [show (show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h)
        (twistedStandardChart K h).source (twistedStandardChartHomeomorph K h)
        (twistedStandardFrames K h) subset_rfl (some i) A) =
      (show ℂ ≃ₗ[ℂ] ℂ from productGraphLineEvaluation (twistedProjectiveDimensions K h)
        (twistedStandardChart K h).source (twistedStandardChartHomeomorph K h)
        (twistedStandardFrames K h) subset_rfl i A).symm 1 from rfl,
    div_linearEquiv_inverse_one]
  change projectionDualLineFiberEquiv _ (hyperplaneFunctionalSection (coordinateFunctional j) _)
    ⟨productGraphLineVector (twistedProjectiveDimensions K h) (twistedStandardChart K h).source
      (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) i A,_⟩ = _
  rw [hyperplaneFunctionalSection_realization]
  change coordinateFunctional j (graphLineVector (twistedStandardFrames K h i)
    (slopeCoordinate (twistedStandardFrames K h i) (slopePoint (twistedStandardFrames K h i) (A i)))) = _
  rw [slopeCoordinate_point]

theorem twistedStandardSectionCoordinates_eq
    (A : ProjectiveProductModel (twistedProjectiveDimensions K h)) :
    twistedStandardSectionCoordinates K h A = twistedSlopeEvaluationEquiv K h A := by
  funext s
  cases s with
  | inl j =>
    change ((1 : ℂ) * (show ℂ from twistedCoordinateSection K h none (positiveCoordinate h j) _)) /
      (1 * (show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h) (twistedStandardChart K h).source
        (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl (some none) A)) = A none (fun _ => 1) j
    rw [one_mul, one_mul]
    refine (twistedStandard_coordinate_evaluation K h none (positiveCoordinate h j) A).trans ?_
    exact (congrArg (fun f : EuclideanSpace ℂ (Fin (1+h)) →ₗ[ℂ] ℂ =>
      f (graphLineVector (standardLineGraphFrame h) (A none)))
      (standard_verticalFunctional h j).symm).trans
        (graphVerticalFunctional_vector (standardLineGraphFrame h) (A none) j)
  | inr s =>
    change ((show ℂ from twistedCoordinateSection K h (some s.1) (positiveCoordinate (K s.1) s.2) _) *
      (show ℂ from twistedCoordinateSection K h none 0 _)) /
      ((show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h) (twistedStandardChart K h).source
        (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl (some (some s.1)) A) *
       (show ℂ from productGraphLineUnit (twistedProjectiveDimensions K h) (twistedStandardChart K h).source
        (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl (some none) A)) = A (some s.1) (fun _ => 1) s.2
    rw [mul_div_mul_comm]
    refine (congrArg₂ (fun x y : ℂ => x * y)
      (twistedStandard_coordinate_evaluation K h (some s.1) (positiveCoordinate (K s.1) s.2) A)
      (twistedStandard_coordinate_evaluation K h none 0 A)).trans ?_
    have hzero : coordinateFunctional (0 : Fin (1+h))
        (graphLineVector (standardLineGraphFrame h) (A none)) = 1 := by
      change (graphLineVector (standardLineGraphFrame h) (A none)) 0 = 1
      have he := graphLineVector_coordinates (standardLineGraphFrame h) (show GraphSlope 1 h from A none)
      have hh := congrArg (fun v => (standardLineGraphFrame h v).1 (0 : Fin 1)) he
      simp only [standardLineGraphFrame_horizontal,LinearEquiv.apply_symm_apply] at hh
      exact hh
    change coordinateFunctional (positiveCoordinate (K s.1) s.2)
      (graphLineVector (standardLineGraphFrame (K s.1)) (A (some s.1))) *
      coordinateFunctional (0 : Fin (1+h)) (graphLineVector (standardLineGraphFrame h) (A none)) = _
    rw [hzero,mul_one,← standard_verticalFunctional]
    exact graphVerticalFunctional_vector (standardLineGraphFrame (K s.1)) (A (some s.1)) s.2

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Normalization
attribute [-instance] _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Twisted bundle graph normalization and its naturality. -/

section
open Bundle Topology CategoryTheory Limits Set
namespace Kaplansky
open ComplexGrassmann
variable {ι A : Type} [Fintype ι] [TopologicalSpace A] (K : ι → ℕ) (h : ℕ)
  (U : Set (ProjectiveProduct (twistedProjectiveDimensions K h))) (e : U ≃ₜ A)

def twistedGraphBundlePullbackRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso
    (lineSumChartPullbackHomeomorph (twistedHyperplaneLineCore K h) U e).symm
    (Subtype.val ⁻¹' nonzeroBundle)
    {z : TotalSpace (EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
      (finiteLineSumCore (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s)
        (chartBaseMap U e))).Fiber | z.2 ≠ 0}
    (fun z => mem_nonzeroBundle z.1) n

theorem twistedGraphBundleNormalization_pullback
    (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
    (hF : U ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source) (n : ℕ) :
    twistedGraphBundleNormalization K h U e F hF n =
      (twistedGraphBundlePullbackRelativeIso K h U e n).hom ≫
        finiteLineFrameNormalization
          (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U e))
          (twistedGraphLineUnit K h U e F hF) (twistedGraphLineUnit_ne_zero K h U e F hF)
          (continuous_twistedGraphLineUnit K h U e F hF) n := by
  have he := relativeHomologyHomeomorphIso_trans_hom
    (lineSumChartPullbackHomeomorph (twistedHyperplaneLineCore K h) U e).symm
    (finiteLineFrameHomeomorph
      (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U e))
      (twistedGraphLineUnit K h U e F hF) (twistedGraphLineUnit_ne_zero K h U e F hF)
      (continuous_twistedGraphLineUnit K h U e F hF))
    (Subtype.val ⁻¹' nonzeroBundle) {z | z.2 ≠ 0} {z | z.2 ≠ 0}
    (fun z => mem_nonzeroBundle z.1)
    (fun z => (not_congr (finiteLineFrameHomeomorph_zero_iff _ _ _ _ z)).symm) n
  exact (congrArg (fun g => g ≫
    productPairProjection (B := A) ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)) n)
    he).trans (Category.assoc _ _ _)

variable {E V J : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Fintype J]

theorem twistedGraphBundleNormalization_affine_eq
    (l : J → E →L[ℝ] V) (c : J → V) (a : U ≃ₜ affineAvoidanceSet l c)
    (F₁ F₂ : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
    (h₁ : U ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F₁).source)
    (h₂ : U ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F₂).source)
    (hp : 0 < h+∑ i, K i) :
    twistedGraphBundleNormalization K h U a F₁ h₁ (2*(h+∑ i, K i)) =
      twistedGraphBundleNormalization K h U a F₂ h₂ (2*(h+∑ i, K i)) := by
  rw [twistedGraphBundleNormalization_pullback,twistedGraphBundleNormalization_pullback]
  apply congrArg (fun f => (twistedGraphBundlePullbackRelativeIso K h U a (2*(h+∑ i, K i))).hom ≫ f)
  have hv : 2 ≤ Module.finrank ℝ (TwistedHyperplaneSlot K h → ℂ) := by
    rw [twistedCoordinateSpace_real_finrank]; omega
  have he := affineAvoidance_finiteLineFrameNormalization_eq (S := TwistedHyperplaneSlot K h) l c
    (fun s => pullbackLineCore (twistedHyperplaneLineCore K h s) (chartBaseMap U a))
    (twistedGraphLineUnit K h U a F₁ h₁) (twistedGraphLineUnit_ne_zero K h U a F₁ h₁)
    (continuous_twistedGraphLineUnit K h U a F₁ h₁)
    (twistedGraphLineUnit K h U a F₂ h₂) (twistedGraphLineUnit_ne_zero K h U a F₂ h₂)
    (continuous_twistedGraphLineUnit K h U a F₂ h₂) hv
  rwa [twistedCoordinateSpace_real_finrank] at he

variable {L : Type} [Fintype L]

theorem twistedGraphBundleIntersection_below_isZero
    (F₀ : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
    (G : L → ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))
    (hp : 0 < h+∑ i, K i) (q : ℕ) (hq : q < 2*(h+∑ i, K i)) :
    IsZero (relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle : Set (twistedGraphBundleDomain K h
        (projectiveProductGraphIntersection (twistedProjectiveDimensions K h) F₀ G)))) q) := by
  apply (affineAvoidance_product_below_isZero
    (productGraphDenominatorLinear (twistedProjectiveDimensions K h) F₀ G)
    (productGraphDenominatorConstant (twistedProjectiveDimensions K h) F₀ G)
    (V := TwistedHyperplaneSlot K h → ℂ) ?_ q ?_).of_iso
    (twistedGraphBundleRelativeIso K h
      (projectiveProductGraphIntersection (twistedProjectiveDimensions K h) F₀ G)
      (projectiveProductGraphIntersectionHomeomorph (twistedProjectiveDimensions K h) F₀ G)
      F₀ inter_subset_left q)
  · rw [twistedCoordinateSpace_real_finrank]; omega
  · rwa [twistedCoordinateSpace_real_finrank]

end Kaplansky

end

section
open Bundle Topology CategoryTheory Set
namespace Kaplansky
open ComplexGrassmann
variable {ι A B : Type} [Fintype ι] [TopologicalSpace A] [TopologicalSpace B]
  (K : ι → ℕ) (r : ℕ) {U V : Set (ProjectiveProduct (twistedProjectiveDimensions K r))} (h : U ⊆ V)
  (e : U ≃ₜ A) (f : V ≃ₜ B) (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K r i))
  (hF : V ⊆ (projectiveProductGraphChart (twistedProjectiveDimensions K r) F).source)

/-- The fiber coordinate depends only on the original base point,
fiber vector and graph frame, and not on the chosen base coordinates. -/
theorem twistedGraphBundleCoordinates_restrict_fiber (z : twistedGraphBundleDomain K r U) :
    (twistedGraphBundleCoordinates K r V f F hF ⟨z.1,h z.2⟩).2 =
      (twistedGraphBundleCoordinates K r U e F (h.trans hF) z).2 := by
  funext s
  change (show EuclideanSpace ℂ (TwistedHyperplaneSlot K r) from z.1.2) s / (show ℂ from twistedGraphLineUnit K r V f F hF s (f ⟨z.1.proj,h z.2⟩)) =
    (show EuclideanSpace ℂ (TwistedHyperplaneSlot K r) from z.1.2) s / (show ℂ from twistedGraphLineUnit K r U e F (h.trans hF) s (e ⟨z.1.proj,z.2⟩))
  congr 1
  cases s with
  | inl j =>
    simp only [twistedGraphLineUnit,tensorLinePair,twistedOldLabel,productGraphLineUnit]
    congr 1
    simp only [productGraphLineEvaluation,pullbackEvaluationEquiv,
      productGraphLineProjection,productGraphLineVector,chartBaseMap,
      ContinuousMap.comp_apply,ContinuousMap.coe_mk,Homeomorph.symm_apply_apply]
    dsimp [hyperplaneEvaluationEquiv,projectionLineFiberEquiv]
    simp only [Homeomorph.symm_apply_apply]
    rfl
  | inr s =>
    simp only [twistedGraphLineUnit,tensorLinePair,twistedOldLabel,productGraphLineUnit]
    congr 1 <;>
      simp only [productGraphLineEvaluation,pullbackEvaluationEquiv,
        productGraphLineProjection,productGraphLineVector,chartBaseMap,
        ContinuousMap.comp_apply,ContinuousMap.coe_mk,Homeomorph.symm_apply_apply] <;>
      dsimp [hyperplaneEvaluationEquiv,projectionLineFiberEquiv] <;>
      simp only [Homeomorph.symm_apply_apply] <;> rfl

/-- Restriction of the normalization on a larger chart is exactly the
normalization of the smaller actual bundle pair, in any base coordinates. -/
theorem twistedGraphBundleNormalization_restrict (n : ℕ) :
    restrictedPairHomologyMap (fun _ hz => h hz : twistedGraphBundleDomain K r U ⊆ twistedGraphBundleDomain K r V)
        nonzeroBundle n ≫ twistedGraphBundleNormalization K r V f F hF n =
      twistedGraphBundleNormalization K r U e F (h.trans hF) n := by
  exact productPairNormalization_restrict
    (Subtype.val ⁻¹' nonzeroBundle) (Subtype.val ⁻¹' nonzeroBundle)
    (subspaceInclusionOfLE (fun _ hz => h hz :
      twistedGraphBundleDomain K r U ⊆ twistedGraphBundleDomain K r V)).hom
    (fun _ hz => hz)
    (twistedGraphBundleCoordinates K r U e F (h.trans hF))
    (twistedGraphBundleCoordinates K r V f F hF)
    (fun z => (mem_nonzeroBundle z.1).trans
      (not_congr (twistedGraphBundleCoordinates_zero_iff K r U e F (h.trans hF) z)).symm)
    (fun z => (mem_nonzeroBundle z.1).trans
      (not_congr (twistedGraphBundleCoordinates_zero_iff K r V f F hF z)).symm)
    (twistedGraphBundleCoordinates_restrict_fiber K r h e f F hF) n

end Kaplansky

end

open Bundle Topology CategoryTheory Limits Set
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedGraphBundleChartNormalization (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (n : ℕ) :=
  twistedGraphBundleNormalization K h (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source
    (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) F) F subset_rfl n

/-- The local integral fiber normalizations agree after the actual
inclusions from a pairwise intersection of total-space charts. -/
theorem twistedGraphBundleChartNormalization_compatible
    (F G : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (hp : 0 < h+∑ i, K i) :
    restrictedPairHomologyMap (inter_subset_left :
      twistedGraphBundleChartDomain K h F ∩ twistedGraphBundleChartDomain K h G ⊆ twistedGraphBundleChartDomain K h F)
      nonzeroBundle (2*(h+∑ i, K i)) ≫ twistedGraphBundleChartNormalization K h F (2*(h+∑ i, K i)) =
    restrictedPairHomologyMap (inter_subset_right :
      twistedGraphBundleChartDomain K h F ∩ twistedGraphBundleChartDomain K h G ⊆ twistedGraphBundleChartDomain K h G)
      nonzeroBundle (2*(h+∑ i, K i)) ≫ twistedGraphBundleChartNormalization K h G (2*(h+∑ i, K i)) := by
  let U := (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source ∩ (projectiveProductGraphChart (twistedProjectiveDimensions K h) G).source
  let H : Unit → ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i) := fun _ => G
  have he : U = projectiveProductGraphIntersection (twistedProjectiveDimensions K h) F H := by
    ext P; simp [U, H, projectiveProductGraphIntersection]
  let e := (Homeomorph.setCongr he).trans (projectiveProductGraphIntersectionHomeomorph (twistedProjectiveDimensions K h) F H)
  change restrictedPairHomologyMap (fun z hz => hz.1 :
      twistedGraphBundleDomain K h U ⊆ twistedGraphBundleChartDomain K h F) nonzeroBundle _ ≫
        twistedGraphBundleNormalization K h _ (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) F) F subset_rfl _ =
    restrictedPairHomologyMap (fun z hz => hz.2 :
      twistedGraphBundleDomain K h U ⊆ twistedGraphBundleChartDomain K h G) nonzeroBundle _ ≫
        twistedGraphBundleNormalization K h _ (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) G) G subset_rfl _
  rw [twistedGraphBundleNormalization_restrict K h inter_subset_left e
      (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) F) F subset_rfl,
    twistedGraphBundleNormalization_restrict K h inter_subset_right e
      (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) G) G subset_rfl]
  exact twistedGraphBundleNormalization_affine_eq K h U (productGraphDenominatorLinear (twistedProjectiveDimensions K h) F H)
    (productGraphDenominatorConstant (twistedProjectiveDimensions K h) F H) e F G inter_subset_left inter_subset_right hp

/-- All finite nonempty intersections of the total-space graph charts
have the required lower relative vanishing. -/
theorem twistedGraphBundleChartIntersection_below_isZero
    (T : Finset (∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i))) (ht : T.Nonempty)
    (hp : 0 < h+∑ i, K i) (q : ℕ) (hq : q < 2*(h+∑ i, K i)) :
    IsZero (relativeSingularHomology (subspaceInclusion
      (Subtype.val ⁻¹' nonzeroBundle : Set ↥(⋂ F ∈ T, twistedGraphBundleChartDomain K h F))) q) := by
  classical
  obtain ⟨F,hF⟩ := ht
  let G : T → ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i) := fun t => t.val
  have he : (⋂ H ∈ T, twistedGraphBundleChartDomain K h H) =
      twistedGraphBundleDomain K h (projectiveProductGraphIntersection (twistedProjectiveDimensions K h) F G) := by
    ext z
    simp only [mem_iInter]
    change (∀ H, H ∈ T → z.proj ∈ (projectiveProductGraphChart (twistedProjectiveDimensions K h) H).source) ↔
      z.proj ∈ (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source ∧
        z.proj ∈ ⋂ t : T, (projectiveProductGraphChart (twistedProjectiveDimensions K h) (G t)).source
    rw [mem_iInter]
    exact ⟨fun h => ⟨h F hF,fun t => h t.val t.property⟩,
      fun h H hH => h.2 ⟨H,hH⟩⟩
  rw [he]
  exact twistedGraphBundleIntersection_below_isZero K h F G hp q hq

/-- A genuine normalization on the WHOLE actual twisted bundle pair,
agreeing with the normalization on any preselected graph chart. -/
theorem twistedHyperplaneBundle_exists_global_normalization
    (F₀ : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (hp : 0 < h+∑ i, K i) :
    ∃ f : relativeSingularHomology
        (subspaceInclusion (nonzeroBundle : Set (TotalSpace (EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
          (twistedHyperplaneSumCore K h).Fiber))) (2*(h+∑ i, K i)) ⟶
        relativeSingularHomology (subspaceInclusion ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)))
          (2*(h+∑ i, K i)),
      restrictedPairToAmbientHomologyMap (twistedGraphBundleChartDomain K h F₀) nonzeroBundle
          (2*(h+∑ i, K i)) ≫ f = twistedGraphBundleChartNormalization K h F₀ (2*(h+∑ i, K i)) := by
  classical
  obtain ⟨S,hF₀,hS⟩ := projectiveProduct_finiteGraphCover (twistedProjectiveDimensions K h) F₀
  have hopen : ∀ F ∈ S, IsOpen (twistedGraphBundleChartDomain K h F) :=
    fun F _ => (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).open_source.preimage (FiberBundle.continuous_proj _ _)
  have hcover : (⋃ F ∈ S, twistedGraphBundleChartDomain K h F) = univ := by
    ext z
    have hz : z.proj ∈ ⋃ F ∈ S, (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source := by
      rw [hS]; trivial
    simpa only [mem_iUnion, twistedGraphBundleChartDomain, twistedGraphBundleDomain,
      mem_ofPred_eq, mem_univ, iff_true] using hz
  let n := 2*(h+∑ i, K i)-1
  have hn : n+1 = 2*(h+∑ i, K i) := by dsimp [n]; omega
  have hex := finiteRelativeOpenCover_exists_glue S (twistedGraphBundleChartDomain K h)
    nonzeroBundle hopen hcover n
    (fun T ht _ q hq => twistedGraphBundleChartIntersection_below_isZero K h T ht hp q (by omega))
    (fun F => twistedGraphBundleChartNormalization K h F (n+1))
    (fun F _ G _ => by rw [hn]; exact twistedGraphBundleChartNormalization_compatible K h F G hp)
  rw [hn] at hex
  obtain ⟨f,hf⟩ := hex
  exact ⟨f,hf F₀ hF₀⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Smooth
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.lineStage_complete _root_.OAI.Kaplansky.lineStage_finite _root_.OAI.Kaplansky.projectiveSpaceZero_nonempty _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Smooth bases and test bundles with replacement maps. -/

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
open ComplexGrassmann

instance smoothTestBundle_smooth (m R b n : ℕ) (hb : b≤R) (hn : n≤b) :
    ContMDiffVectorBundle ∞ (EuclideanSpace ℂ (TestBundleSlot m R n))
      (SmoothTestBundle m R b n hb hn)
      𝓘(ℝ,ProjectiveProductModel (stageProjectiveDimensions m R b hb)) :=
  smoothLineSum_contMDiffVectorBundle _ _

end Kaplansky

end

open Bundle Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.BundleTests_Obstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Nonvanishing twisted section classes and the stable retained-bundle obstruction. -/

section
open Bundle Topology CategoryTheory Set
namespace Kaplansky
open ComplexGrassmann

variable {ι : Type} [Fintype ι] (K : ι → ℕ) (h : ℕ)

def twistedRestrictedSection : C((twistedStandardChart K h).source,
    twistedGraphBundleDomain K h (twistedStandardChart K h).source) :=
  ⟨fun P => ⟨⟨P.1,twistedHyperplaneSection K h P.1⟩,P.2⟩,
    ((continuous_twistedHyperplaneSection K h).comp continuous_subtype_val).subtype_mk _⟩

theorem twistedStandardBundleCoordinates_section (P : (twistedStandardChart K h).source) :
    twistedGraphBundleCoordinates K h (twistedStandardChart K h).source
      (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl
      (twistedRestrictedSection K h P) =
    (twistedStandardChartHomeomorph K h P,
      twistedSlopeEvaluationEquiv K h (twistedStandardChartHomeomorph K h P)) := by
  apply Prod.ext
  · rfl
  let A := twistedStandardChartHomeomorph K h P
  have hP : P.1 = canonicalProductGraphPoint (twistedProjectiveDimensions K h) A := by
    change P.1 = ((twistedStandardChartHomeomorph K h).symm
      (twistedStandardChartHomeomorph K h P)).val
    rw [Homeomorph.symm_apply_apply]
  change (fun s => (show EuclideanSpace ℂ (TwistedHyperplaneSlot K h) from
    twistedHyperplaneSection K h P.1) s / (show ℂ from twistedStandardLineUnit K h s A)) = _
  rw [hP]
  exact twistedStandardSectionCoordinates_eq K h A

def twistedLocalSectionHomeomorph : (twistedStandardChart K h).source ≃ₜ
    (TwistedHyperplaneSlot K h → ℂ) :=
  (twistedStandardChartHomeomorph K h).trans (twistedSlopeEvaluationEquiv K h).toHomeomorph

theorem twistedLocalSectionHomeomorph_zero :
    twistedLocalSectionHomeomorph K h
      ⟨firstCoordinateProduct (twistedProjectiveDimensions K h),
        canonicalProduct_zero_in_chart (twistedProjectiveDimensions K h)⟩ = 0 := by
  change twistedSlopeEvaluationEquiv K h (canonicalProductChartHomeomorph _ _) = 0
  rw [canonicalProductChartHomeomorph_zero,map_zero]

def twistedLocalSectionRelativeIso (n : ℕ) :=
  relativeHomologyHomeomorphIso (twistedLocalSectionHomeomorph K h)
    ({⟨firstCoordinateProduct (twistedProjectiveDimensions K h),
      canonicalProduct_zero_in_chart (twistedProjectiveDimensions K h)⟩}ᶜ :
      Set (twistedStandardChart K h).source)
    ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)) (fun P => by
      change P ≠ _ ↔ twistedLocalSectionHomeomorph K h P ≠ 0
      rw [← twistedLocalSectionHomeomorph_zero K h]
      exact (not_congr (twistedLocalSectionHomeomorph K h).injective.eq_iff).symm) n

def twistedRestrictedSectionRelativeMap (n : ℕ) :=
  relativeHomologyMap
    (subspaceInclusion ({⟨firstCoordinateProduct (twistedProjectiveDimensions K h),
      canonicalProduct_zero_in_chart (twistedProjectiveDimensions K h)⟩}ᶜ :
      Set (twistedStandardChart K h).source))
    (subspaceInclusion (Subtype.val ⁻¹' nonzeroBundle :
      Set (twistedGraphBundleDomain K h (twistedStandardChart K h).source)))
    (subspaceMap _ _ (twistedRestrictedSection K h) (by
      intro P hP
      exact (mem_nonzeroBundle _).mpr (fun hz => hP
        (Subtype.ext ((twistedHyperplaneSection_eq_zero_iff K h P.1).mp hz)))))
    (TopCat.ofHom (twistedRestrictedSection K h)) (by rfl) n

theorem twistedRestrictedSection_normalization (n : ℕ) :
    twistedRestrictedSectionRelativeMap K h n ≫
      twistedGraphBundleNormalization K h (twistedStandardChart K h).source
        (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl n =
      (twistedLocalSectionRelativeIso K h n).hom := by
  apply sectionProductNormalization
    ({⟨firstCoordinateProduct (twistedProjectiveDimensions K h),
      canonicalProduct_zero_in_chart (twistedProjectiveDimensions K h)⟩}ᶜ)
    (Subtype.val ⁻¹' nonzeroBundle) (twistedRestrictedSection K h) _
    (twistedGraphBundleCoordinates K h (twistedStandardChart K h).source
      (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl)
    (twistedLocalSectionHomeomorph K h)
  intro P
  exact congrArg Prod.snd (twistedStandardBundleCoordinates_section K h P)

theorem twistedGraphBundleChartNormalization_isIso
    (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (n : ℕ) :
    IsIso (twistedGraphBundleChartNormalization K h F n) := by
  let e := twistedGraphBundleRelativeIso K h
    (projectiveProductGraphChart (twistedProjectiveDimensions K h) F).source
    (projectiveProductGraphHomeomorph (twistedProjectiveDimensions K h) F) F subset_rfl n
  let f := productPairProjection (B := ProjectiveProductModel (twistedProjectiveDimensions K h))
    ({0}ᶜ : Set (TwistedHyperplaneSlot K h → ℂ)) n
  change IsIso (e.hom ≫ f)
  exact IsIso.comp_isIso' e.isIso_hom (productPairProjection_isIso _ _)

theorem twistedGraphBundleChartToAmbient_mono
    (F : ∀ i, GraphFrame 1 (twistedProjectiveDimensions K h i)) (hp : 0 < h+∑ i, K i) :
    Mono (restrictedPairToAmbientHomologyMap (twistedGraphBundleChartDomain K h F)
      nonzeroBundle (2*(h+∑ i, K i))) := by
  obtain ⟨f,hf⟩ := twistedHyperplaneBundle_exists_global_normalization K h F hp
  have : IsIso (restrictedPairToAmbientHomologyMap (twistedGraphBundleChartDomain K h F)
      nonzeroBundle (2*(h+∑ i, K i)) ≫ f) := by
    rw [hf]
    exact twistedGraphBundleChartNormalization_isIso K h F _
  exact mono_of_mono (restrictedPairToAmbientHomologyMap (twistedGraphBundleChartDomain K h F)
    nonzeroBundle (2*(h+∑ i, K i))) f

theorem twistedOrdinaryRelativeMap_chart (n : ℕ) :
    canonicalChartRelativeInclusion (twistedProjectiveDimensions K h) n ≫
      twistedOrdinaryRelativeMap K h n =
    twistedRestrictedSectionRelativeMap K h n ≫
      restrictedPairToAmbientHomologyMap
        (twistedGraphBundleDomain K h (twistedStandardChart K h).source) nonzeroBundle n := by
  unfold canonicalChartRelativeInclusion twistedOrdinaryRelativeMap twistedRestrictedSectionRelativeMap
  change relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n =
    relativeHomologyMap _ _ _ _ _ n ≫ relativeHomologyMap _ _ _ _ _ n
  erw [relativeHomologyMap_comp,relativeHomologyMap_comp]
  apply relativeHomologyMap_congr_ambient
  rfl

theorem twistedOrdinaryRelativeMap_mono (hp : 0 < h+∑ i, K i) :
    Mono (twistedOrdinaryRelativeMap K h (2*(h+∑ i, K i))) := by
  let n := 2*(h+∑ i, K i)
  let e := canonicalChartExcisionIso (twistedProjectiveDimensions K h) n
  let r := twistedRestrictedSectionRelativeMap K h n
  let f := twistedGraphBundleNormalization K h (twistedStandardChart K h).source
    (twistedStandardChartHomeomorph K h) (twistedStandardFrames K h) subset_rfl n
  have : IsIso (r ≫ f) := by
    change IsIso (twistedRestrictedSectionRelativeMap K h n ≫ _)
    rw [twistedRestrictedSection_normalization]
    infer_instance
  have : Mono r := mono_of_mono r f
  have : Mono (restrictedPairToAmbientHomologyMap
      (twistedGraphBundleDomain K h (twistedStandardChart K h).source) nonzeroBundle n) :=
    twistedGraphBundleChartToAmbient_mono K h (twistedStandardFrames K h) hp
  have he : twistedOrdinaryRelativeMap K h n = e.inv ≫ r ≫
      restrictedPairToAmbientHomologyMap
        (twistedGraphBundleDomain K h (twistedStandardChart K h).source) nonzeroBundle n := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc,← Category.assoc,e.hom_inv_id,Category.id_comp]
    exact twistedOrdinaryRelativeMap_chart K h n
  change Mono (twistedOrdinaryRelativeMap K h n)
  rw [he]
  infer_instance

/-- The actual twisted section carries the existing augmented-base
fundamental class to a nonzero ordinary relative class. -/
theorem twistedOrdinarySection_fundamental_ne_zero
    (hp : 0 < ∑ i, twistedProjectiveDimensions K h i) :
    ordinarySectionClassMap (twistedHyperplaneSection K h)
      (continuous_twistedHyperplaneSection K h) (2*∑ i, twistedProjectiveDimensions K h i)
      (projectiveProductFundamentalClass (twistedProjectiveDimensions K h) hp) ≠ 0 := by
  have hp' : 0 < h+∑ i, K i := by rwa [twistedProjectiveDimensions_sum] at hp
  have : Mono (twistedOrdinaryRelativeMap K h (2*∑ i, twistedProjectiveDimensions K h i)) := by
    rw [twistedProjectiveDimensions_sum]
    exact twistedOrdinaryRelativeMap_mono K h hp'
  rw [← twistedOrdinaryRelativeMap_comparison]
  change twistedOrdinaryRelativeMap K h _
    (absoluteToRelative _ _ (projectiveProductFundamentalClass _ hp)) ≠ 0
  rw [projectiveProductFundamentalClass_localizes]
  intro hz
  exact canonicalProductLocalGenerator_ne_zero (twistedProjectiveDimensions K h) hp
    ((ModuleCat.mono_iff_injective (twistedOrdinaryRelativeMap K h _)).mp
      inferInstance (hz.trans (map_zero _).symm))

theorem twistedHyperplane_every_section_has_zero (hp : 0 < h+∑ i, K i)
    (s : ∀ P, (twistedHyperplaneSumCore K h).Fiber P)
    (hs : Continuous (fun P => TotalSpace.mk' (EuclideanSpace ℂ (TwistedHyperplaneSlot K h)) P (s P))) :
    ∃ P, s P = 0 := by
  have hp' : 0 < ∑ i, twistedProjectiveDimensions K h i := by
    rw [twistedProjectiveDimensions_sum]; exact hp
  by_contra hn
  push Not at hn
  have hz := ordinarySectionClassMap_eq_zero s hs hn (2*∑ i, twistedProjectiveDimensions K h i)
  have he := @ordinarySectionClassMap_eq _ (EuclideanSpace ℂ (TwistedHyperplaneSlot K h))
    _ _ _ (twistedHyperplaneSumCore K h).Fiber _ _ _
    (twistedHyperplaneSumCore K h).fiberBundle (twistedHyperplaneSumCore K h).vectorBundle
    (twistedHyperplaneSection K h) s (continuous_twistedHyperplaneSection K h) hs
    (2*∑ i, twistedProjectiveDimensions K h i)
  have hz := he.trans hz
  apply twistedOrdinarySection_fundamental_ne_zero K h hp'
  rw [hz]
  rfl

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- The tensor construction contradicts any frame with more vectors than
the displayed trivial rank. The frame need not respect the line summands. -/
theorem twistedSourceStage_no_large_frame {ι : Type} [Fintype ι]
    (K : ι → ℕ) (h d : ℕ) (hp : 0 < h+∑ i, K i) (hd : h < d) :
    IsEmpty (ContinuousOrthonormalStageFrame (twistedSourceStage K h) d) := by
  refine ⟨fun f => ?_⟩
  have hd' : 1+h ≤ d := by omega
  obtain ⟨P,hP⟩ := twistedHyperplane_every_section_has_zero K h hp
    (twistedFrameSection K h f hd') (continuous_twistedFrameSection K h f hd')
  exact twistedFrameSection_ne_zero K h f hd' P hP

theorem retainedGrouped_no_test_frame {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    IsEmpty (ContinuousOrthonormalStageFrame (retainedGroupedStage m R) (2*m*testRank m R 0)) := by
  have hp := retainedTest_hyperplaneDegree_pos hm hR
  have := twistedSourceStage_no_large_frame (testProjectiveDimension m R)
    (retainedTrivialMultiplicity m R) (2*m*testRank m R 0) (by omega)
    (retainedTrivialMultiplicity_bound hm)
  exact ⟨fun f => isEmptyElim (f.congr (retainedTwistedSourceUnitary m R).symm)⟩

theorem actualAlgebra_matrix_not_properlyInfinite {m : ℕ} (hm : 0 < m) :
    ¬ ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra) := by
  intro hpi
  obtain ⟨R,hR,⟨f⟩⟩ := properlyInfinite_regrouped_frame hm hpi
  have := retainedGrouped_no_test_frame hm hR
  exact isEmptyElim f

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_ActualAlgebra
attribute [-instance] _root_.OAI.Kaplansky.CuntzDimensionState.spectralMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The actual M48 algebra, its fixed defect pair, and its Cuntz dimension state. -/

namespace Kaplansky

section
open scoped BigOperators
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

attribute [local instance] OAI.Kaplansky.actualAlgebraSpectralOrder
attribute [local instance] OAI.Kaplansky.actualAlgebraSpectralOrderedRing
instance (priority := 2400) actualDefectAlgebra_cstar : CStarAlgebra ActualDefectAlgebra :=
  CStarMatrix.instCStarAlgebra

local instance (priority := 3100) actualDefectAlgebraSemiring : Semiring ActualDefectAlgebra :=
  actualDefectAlgebra_cstar.toSemiring
local instance (priority := 3100) actualDefectMatrixSemiring (m : ℕ) :
    Semiring (CStarMatrix (Fin m) (Fin m) ActualDefectAlgebra) := CStarMatrix.instSemiring

def actualGeneratorNat (i : ℕ) : ActualAlgebra :=
  if hi : i < 24 then generatedGenerator actualBoundedGenerator ⟨i,hi⟩ else 0

def actualDefectA : ActualDefectAlgebra := defectA actualGeneratorNat 24
def actualDefectB : ActualDefectAlgebra := defectB actualGeneratorNat 24

attribute [local instance] OAI.Kaplansky.actualAlgebraSemiring
/-- Explicit matrix correspondence for every further amplification. -/
def actualDefectAmplificationEquiv (m : ℕ) :
    CStarMatrix (Fin m) (Fin m) ActualDefectAlgebra ≃⋆ₐ[ℂ]
      CStarMatrix (Fin (48*m)) (Fin (48*m)) ActualAlgebra :=
  (cstarMatrixFlatten ActualAlgebra (Fin m) ActualDefectIndex).trans
    (CStarMatrix.reindexₐ ℂ ActualAlgebra
      ((Fintype.equivFin (Fin m × ActualDefectIndex)).trans
        (finCongr (by simp [ActualDefectIndex,Nat.mul_comm]))))

set_option synthInstance.maxHeartbeats 200000 in
theorem actualDefectAlgebra_matrix_not_properlyInfinite {m : ℕ} (hm : 0 < m) :
    ¬ ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualDefectAlgebra) := by
  intro hp
  exact actualAlgebra_matrix_not_properlyInfinite (m := 48*m) (by omega)
    (properlyInfinite_map (actualDefectAmplificationEquiv m).toStarAlgHom hp)

end

/-- An actual normalized dimension state exists for the constructed algebra.
No quasitrace-existence premise, simplicity, or exactness assumption is used. -/
theorem actualCuntzDimensionState_nonempty : Nonempty (CuntzDimensionState ActualDefectAlgebra) :=
  cuntzDimensionState_nonempty fun _ hk => actualDefectAlgebra_matrix_not_properlyInfinite hk

/-- A chosen state on actual Cuntz classes. No analytic correspondence is claimed. -/
def actualCuntzDimensionState : CuntzDimensionState ActualDefectAlgebra :=
  Classical.choice actualCuntzDimensionState_nonempty

end Kaplansky

end

end OAI
end


