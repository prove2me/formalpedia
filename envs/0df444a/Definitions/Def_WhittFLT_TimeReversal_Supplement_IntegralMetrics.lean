-- Prove2me | Definitions.Def_WhittFLT_TimeReversal_Supplement_IntegralMetrics
-- name    : WhittFLT_TimeReversal_Supplement_IntegralMetrics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:39:33.521678+00:00
-- url     : https://prove2.me/theorems/6418f1ca-6ef3-432a-a8c8-0ded06bbe7df
-- title:
--   Integral distances (2.2), (2.3) and the original net convergence criterion
-- statement:
--   For càdlàg paths $x,y$ with values in a metric space, let $d_{st}$ be the published compact $J_1$ distance (2.1). Define
--
--   $$d_a(x,y)=\int_a^\infty e^{-(t-a)}\min\{1,d_{at}(x,y)\}\,dt,$$
--   $$d_{\mathbb R}(x,y)=\int_{-\infty}^0\int_0^\infty e^{s-t}\min\{1,d_{st}(x,y)\}\,dt\,ds.$$
--
--   A finite path metric is symmetric, satisfies the triangle inequality, and vanishes precisely on paths agreeing on the time domain. The net version of extended $J_1$ convergence uses the same compact restriction criterion as the published sequential predicate, along an arbitrary filter. These objects express both clauses of Theorem 2.5.
--
--   **Formalization Note** Integrals and distances take values in $[0,\infty]$; finiteness is a theorem conclusion. The nonnegative lower integral has no Bochner default on a nonintegrable input. The truncation $\wedge 1$ is applied to $d_{at}$ (resp. $d_{st}$) and multiplied by the exponential weight, exactly as in (2.2)–(2.3) on p. 72. Net convergence includes càdlàg membership for every indexed path and the limit. Compact singleton intervals are included, consistently with the published definition.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, §2, (2.2)–(2.3), p. 72

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition
open scoped ENNReal
variable {S : Type*} [MetricSpace S]

/-- (2.2), the exponentially weighted truncated compact J₁ distance. -/
noncomputable def metric22 (a : ℝ) (x y : ℝ → S) : ℝ≥0∞ :=
  ∫⁻ t in Ici a, ENNReal.ofReal (Real.exp (-(t-a))) * min 1 (j1Dist a t x y)

/-- (2.3), the two-sided metric. -/
noncomputable def metric23 (x y : ℝ → S) : ℝ≥0∞ :=
  ∫⁻ s in Iic (0 : ℝ), ∫⁻ t in Ici (0 : ℝ),
    ENNReal.ofReal (Real.exp (s-t)) * min 1 (j1Dist s t x y)

/-- A finite metric on càdlàg paths identified on T, not on total representatives. -/
def IsPathMetric (T : Set ℝ) (d : (ℝ → S) → (ℝ → S) → ℝ≥0∞) : Prop :=
  (∀ x y, IsCadlagOn T x → IsCadlagOn T y → d x y < ⊤) ∧
  (∀ x y, IsCadlagOn T x → IsCadlagOn T y → d x y = d y x) ∧
  (∀ x y, IsCadlagOn T x → IsCadlagOn T y → (d x y = 0 ↔ EqOn x y T)) ∧
  (∀ x y z, IsCadlagOn T x → IsCadlagOn T y → IsCadlagOn T z →
    d x z ≤ d x y + d y z)

/-- The original net/filter restriction criterion of §2, including membership in D. -/
def J1Net {ι : Type*} (T : Set ℝ) (L : Filter ι) (xs : ι → ℝ → S) (x : ℝ → S) : Prop :=
  (∀ i, IsCadlagOn T (xs i)) ∧ IsCadlagOn T x ∧
    ∀ a b : ℝ, a ≤ b → Icc a b ⊆ T →
      (ContinuousWithinAt x T a ∨ IsEndpoint T a) →
      (ContinuousWithinAt x T b ∨ IsEndpoint T b) →
      Tendsto (fun i => j1Dist a b (xs i) x) L (𝓝 0)

end WhittFLT.TimeReversal.Supplement


