-- Prove2me | Definitions.Def_OAI_Geometry_PlaneColoring_MeasurableProper
-- name    : OAI_Geometry_PlaneColoring_MeasurableProper
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T17:39:03.896817+00:00
-- url     : https://prove2.me/theorems/a03cdb61-b3c5-45f6-904f-919366f4383d
-- title:
--   Continuity and unit length of the circle parametrization; the angle and circle measures are probability measures
-- statement:
--   Let $u(t)=(\cos t,\sin t)$ be the direction map $\mathbb{R}\to\mathbb{R}^2$, let $\mu=\frac{1}{2\pi}\,\lambda|_{[0,2\pi)}$ be the normalized angle measure on $\mathbb{R}$ (with $\lambda$ Lebesgue measure), and let $\sigma=u_*\mu$ be the circle measure on the Euclidean plane $\mathbb{R}^2$, as defined in the companion definition file. This file records their basic properties.
--
--   1. **Continuity.** The map $u:\mathbb{R}\to\mathbb{R}^2$ is continuous, and consequently Borel measurable.
--   2. **Normalized angle measure.** $\mu$ is a probability measure: $\mu(\mathbb{R})=1$.
--   3. **Circle measure.** $\sigma$ is a probability measure on $\mathbb{R}^2$: $\sigma(\mathbb{R}^2)=1$.
--   4. **Unit length.** For every $t\in\mathbb{R}$,
--   $$\|u(t)\|=1,$$
--   where $\|\cdot\|$ is the Euclidean norm.
--
--   Together these make $\sigma$ a probability measure carried by unit vectors, so that integrals against $\sigma$ are averages over directions; they are the basic inputs for averaging arguments over unit-distance pairs $(x,x+v)$ in the plane.
--
--   **Formalization Note** The two probability statements are type-class instances of `IsProbabilityMeasure`, so they are found automatically; `continuous_circleDir` and `measurable_circleDir` are registered with the `continuity` and `fun_prop` automation, and `norm_circleDir` is a simp lemma. The norm is that of `EuclideanSpace ℝ (Fin 2)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/PlaneColoring/MeasurableProper.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/PlaneColoring/MeasurableProper.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PlaneColoring mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PlaneColoring
import Definitions.Def_OAI_Geometry_PlaneColoring_Lattice
import Definitions.Def_OAI_Geometry_PlaneColoring_Basic
import Definitions.Def_OAI_Geometry_PlaneColoring_Metric

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem160

@[continuity, fun_prop]
theorem continuous_circleDir : Continuous circleDir := by
  unfold circleDir
  fun_prop

@[fun_prop]
theorem measurable_circleDir : Measurable circleDir :=
  continuous_circleDir.measurable

instance normalizedAngleMeasure_isProbabilityMeasure :
    IsProbabilityMeasure normalizedAngleMeasure where
  measure_univ := by
    have hpos : 0 < (2 : ℝ) * Real.pi := by positivity
    simp only [normalizedAngleMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
      Real.volume_Ico, sub_zero, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hpos))
      ENNReal.ofReal_ne_top

instance circleMeasure_isProbabilityMeasure : IsProbabilityMeasure circleMeasure := by
  unfold circleMeasure
  exact Measure.isProbabilityMeasure_map measurable_circleDir.aemeasurable

@[simp]
theorem norm_circleDir (t : ℝ) : ‖circleDir t‖ = 1 := by
  have h : ‖circleDir t‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [circleDir, Fin.sum_univ_two]
  nlinarith [norm_nonneg (circleDir t)]

end Problem160

end

end OAI


