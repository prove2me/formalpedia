-- Prove2me | Definitions.Def_OAIQWUCS000
-- name    : OAIQWUCS000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T00:47:38.708041+00:00
-- url     : https://prove2.me/theorems/e43c8305-2ff8-4a99-a8c0-5bc8ef501dae
-- title:
--   Picard paths for holomorphic flows (OpenAI universal-cover splitting)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniversalCoverSplitting.main`. Its definitions set up the Picard integral equation whose solutions are the local holomorphic flows of the standalone statement `OAI.UniversalCoverSplitting.exists_holomorphic_local_flow`.
--
--   The bundle holds OpenAI's Lean definitions from the modules `PathDerivatives`, `Picard` and `FlowVariation` of `lean/OAI/Geometry/KahlerSplitting` (OpenAI, *Universal-cover splitting for compact Kähler manifolds*, OpenAI Math Release, September 23, 2026, result family 052, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas their bodies use. Among them:
--   - the time interval $[0,1]$ (`FlowTime`), the Banach space of continuous paths in $E$ (`FlowPath`), and initial data $(x, z) \in E \times \mathbb C$ (`FlowParameter`);
--   - pointwise application of a path of linear maps to a path (`pathLinearApply`, `pathLinearApplyL`), and the derivative of composition with a map along a path (`pathDerivative`);
--   - the primitive $\gamma \mapsto \int_0^t \gamma$ as a continuous linear map (`pathPrimitive`, `pathPrimitiveL`);
--   - the Picard operator $\gamma \mapsto \int_0^t V(\gamma)$ (`picardIntegral`) and the equation $\gamma = x + z \int_0^t V(\gamma)$ (`picardEquation`, `picardBase`, `picardLinearTerm`). A solution $\gamma$ is the flow line $t \mapsto \varphi_{zt}(x)$ at complex time $zt$;
--   - the real-time extension of a solution and its time variation (`picardRealExtension`, `picardTimeVariation`);
--   - OpenAI's structure `HolomorphicFlowData`, the local flow with its properties as fields.
--
--   The theorems the definitions do not need are proved in the solutions of this split.
-- source:
--   OpenAI, Universal-cover splitting for compact Kähler manifolds, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 052; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/KahlerSplitting at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_UniversalCover.PathDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped Interval
open Set MeasureTheory
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set
open scoped Manifold

open Set Metric Filter Topology Asymptotics

open Set Metric Filter Topology Asymptotics

namespace UniversalCoverSplitting
variable {𝕜 E F T : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace T] [CompactSpace T]

def pathLinearApply (A : C(T,E →L[𝕜] F)) : C(T,E) →L[𝕜] C(T,F) :=
  LinearMap.mkContinuous
    { toFun := fun η ↦ ⟨fun t ↦ A t (η t), by fun_prop⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    ‖A‖ (fun η ↦ by
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg η))).mpr
      intro t
      exact ((A t).le_opNorm (η t)).trans
        (mul_le_mul (A.norm_coe_le_norm t) (η.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem pathLinearApply_apply (A : C(T,E →L[𝕜] F)) (η : C(T,E)) (t : T) :
    pathLinearApply A η t = A t (η t) := rfl

def pathDerivative (D : E → E →L[𝕜] F) (γ : C(T,E))
    (hD : ∀ t, ContinuousAt D (γ t)) : C(T,E →L[𝕜] F) :=
  ⟨fun t ↦ D (γ t), continuous_iff_continuousAt.mpr
    (fun t ↦ (hD t).comp γ.continuous.continuousAt)⟩

end UniversalCoverSplitting
open Set Metric Filter Topology

namespace UniversalCoverSplitting
variable {𝕜 E F T : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace T] [CompactSpace T]

 theorem pathLinearApply_norm_le (A : C(T,E →L[𝕜] F)) :
    ‖pathLinearApply A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (pathLinearApply A) (norm_nonneg A)
  intro η
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg η))).mpr
  intro t
  exact ((A t).le_opNorm (η t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (η.norm_coe_le_norm t)
      (norm_nonneg _) (norm_nonneg _))

def pathLinearApplyL : C(T,E →L[𝕜] F) →L[𝕜] C(T,E) →L[𝕜] C(T,F) :=
  LinearMap.mkContinuous
    { toFun := fun A : C(T,E →L[𝕜] F) ↦ pathLinearApply A
      map_add' := by intros; ext η t; simp
      map_smul' := by intros; ext η t; simp }
    1 (fun A ↦ by simpa using pathLinearApply_norm_le A)

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.Picard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set Metric Filter Topology
open Set MeasureTheory
open scoped Interval

namespace UniversalCoverSplitting
abbrev FlowTime := Icc (0 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pathExtend (γ : C(FlowTime,E)) : C(ℝ,E) :=
  γ.comp ⟨projIcc 0 1 zero_le_one, continuous_projIcc⟩

omit [NormedSpace ℝ E] in
@[simp] theorem pathExtend_apply (γ : C(FlowTime,E)) (t : FlowTime) :
    pathExtend γ t = γ t := by simp [pathExtend,projIcc_of_mem _ t.property]

def pathPrimitive (γ : C(FlowTime,E)) : C(FlowTime,E) :=
  ⟨fun t ↦ ∫ u in (0 : ℝ)..t.val, pathExtend γ u,
    (intervalIntegral.continuous_primitive
      (fun a b ↦ (pathExtend γ).continuous.intervalIntegrable a b) 0).comp continuous_subtype_val⟩

@[simp] theorem pathPrimitive_apply (γ : C(FlowTime,E)) (t : FlowTime) :
    pathPrimitive γ t = ∫ u in (0 : ℝ)..t.val, pathExtend γ u := rfl

 theorem pathPrimitive_norm_le (γ : C(FlowTime,E)) : ‖pathPrimitive γ‖ ≤ ‖γ‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg γ)).mpr
  intro t
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t.val) (C := ‖γ‖) (f := pathExtend γ)
    (fun u _ ↦ γ.norm_coe_le_norm (projIcc 0 1 zero_le_one u))
  calc
    ‖pathPrimitive γ t‖ ≤ ‖γ‖ * |t.val - 0| := hb
    _ ≤ ‖γ‖ := by rw [sub_zero,abs_of_nonneg t.property.1]; nlinarith [t.property.2,norm_nonneg γ]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def pathPrimitiveL : C(FlowTime,E) →L[ℂ] C(FlowTime,E) :=
  LinearMap.mkContinuous
    { toFun := fun γ : C(FlowTime,E) ↦ pathPrimitive γ
      map_add' := by
        intro γ η; ext t
        exact intervalIntegral.integral_add
          ((pathExtend γ).continuous.intervalIntegrable _ _)
          ((pathExtend η).continuous.intervalIntegrable _ _)
      map_smul' := by
        intro z γ; ext t
        exact intervalIntegral.integral_smul z (pathExtend γ) }
    1 (fun γ ↦ by simpa using pathPrimitive_norm_le γ)

@[simp] theorem pathPrimitiveL_apply (γ : C(FlowTime,E)) :
    pathPrimitiveL γ = pathPrimitive γ := rfl

end UniversalCoverSplitting
open Set Metric Filter Topology

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

abbrev FlowPath (E : Type*) [TopologicalSpace E] := C(FlowTime,E)
abbrev FlowParameter (E : Type*) := E × ℂ

def picardIntegral (V : C(E,E)) (γ : FlowPath E) : FlowPath E :=
  pathPrimitiveL (V.comp γ)

def picardEquation (V : C(E,E)) (q : FlowParameter E × FlowPath E) :
    FlowParameter E × FlowPath E :=
  (q.1,q.2 - (ContinuousMap.const FlowTime q.1.1) - q.1.2 • picardIntegral V q.2)

def picardBase (p : E) : FlowParameter E × FlowPath E :=
  ((p,0),ContinuousMap.const FlowTime p)

@[simp] theorem picardEquation_base (V : C(E,E)) (p : E) :
    picardEquation V (picardBase p) = ((p,0),0) := by simp [picardEquation,picardBase]

def pathShear (L : FlowParameter E →L[ℂ] FlowPath E) :
    (FlowParameter E × FlowPath E) ≃L[ℂ] (FlowParameter E × FlowPath E) where
  toFun q := (q.1,q.2-L q.1)
  invFun q := (q.1,q.2+L q.1)
  left_inv := by intro q; ext <;> simp
  right_inv := by intro q; ext <;> simp
  map_add' := by intro q r; ext <;> simp; abel
  map_smul' := by intro z q; ext <;> simp [smul_sub]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def picardLinearTerm (V : C(E,E)) (p : E) : FlowParameter E →L[ℂ] FlowPath E :=
  (ContinuousLinearMap.const ℂ FlowTime).comp (ContinuousLinearMap.fst ℂ E ℂ) +
    (ContinuousLinearMap.snd ℂ E ℂ).smulRight
      (picardIntegral V (ContinuousMap.const FlowTime p))

end UniversalCoverSplitting
open Set Metric Filter Topology
open scoped ContDiff

open Set Metric Filter Topology MeasureTheory
open scoped Interval

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

def picardRealExtension (V : C(E,E)) (p : E) (z : ℂ) (γ : FlowPath E) : ℝ → E :=
  fun t ↦ p + z • ∫ u in (0 : ℝ)..t, V (pathExtend γ u)

def picardTimeVariation (V : C(E,E)) (γ : FlowPath E) : FlowPath E :=
  ⟨fun t ↦ t.val • V (γ t), by fun_prop⟩

end UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Interval

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.FlowVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology
open scoped ContDiff
open Set Metric Filter Topology MeasureTheory
open scoped Interval

open Set Metric Filter Topology
open scoped ContDiff

open Set Metric Filter Topology
open scoped ContDiff

open Set Metric Filter Topology
open scoped ContDiff

open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

structure HolomorphicFlowData (V : C(E,E)) (D : C(E,E →L[ℂ] E)) (U : Set E) (p : E) where
  domain : Set (E × ℂ)
  isOpen_domain : IsOpen domain
  base_mem : (p,0) ∈ domain
  map : E × ℂ → E
  contDiff : ContDiffOn ℂ 1 map domain
  mapsTo : MapsTo map domain U
  zero : ∀ x, (x,0) ∈ domain → map (x,0) = x
  time : ∀ q ∈ domain, fderiv ℂ map q (0,1) = V (map q)
  preserves : ∀ (A : C(E,E)) (DA : E → E →L[ℂ] E),
    (∀ x ∈ U, HasFDerivAt A (DA x) x) →
    (∀ x ∈ U, DA x (V x) = D x (A x)) →
    ∀ q ∈ domain, fderiv ℂ map q (A q.1,0) = A (map q)

end UniversalCoverSplitting

end

end OAI
end


