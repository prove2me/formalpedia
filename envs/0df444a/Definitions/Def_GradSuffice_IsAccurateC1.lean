-- Prove2me | Definitions.Def_GradSuffice_IsAccurateC1
-- name    : GradSuffice_IsAccurateC1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:21:26.279454+00:00
-- url     : https://prove2.me/theorems/6bfdaff8-92e3-44a5-8a65-a79cd230752f
-- title:
--   $\varepsilon$-accuracy on continuously differentiable objectives
-- statement:
--   A randomized first-order algorithm $A=(A_\omega)$ on $W$ with internal randomness $(\Omega,\mu)$ is **$\varepsilon$-accurate on $C^1$ objectives** if for every $f:X\to\mathbb R$ that is convex, continuously differentiable and 1-Lipschitz on all of $X$, answered by the oracle $w\mapsto(f(w),\nabla f(w))$, the success set $\{\omega: f(w_T(\omega))-\inf_W f\le\varepsilon\}$ is measurable and has probability at least $1/2$.
--
--   Every $\varepsilon$-accurate algorithm is $\varepsilon$-accurate on $C^1$ objectives, since such an $f$ with $U=X$ is an objective and its gradient is its only subgradient. Lower bounds stated for this weaker requirement are the paper's remark that they "hold even when the objectives are required to be continuously differentiable".
--
--   **Formalization Note** The gradient is the Fréchet derivative `fderiv ℝ f`.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 4, p.10; §2, p.4

import Mathlib
import Definitions.Def_GradSuffice_DetAlg_lastQuery

namespace GradSuffice

/-- **ε-accuracy on the continuously differentiable objectives.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Theorem 4, p.10: "The
lower bound holds even when the objectives are required to be continuously differentiable", and
§2, p.4 ("Our lower-bound construction produces continuously differentiable functions on the
ambient space"). The accuracy requirement of p.4 (success probability at least `1/2`) is imposed
only for objectives `f : X → ℝ` that are convex, `C¹` and 1-Lipschitz on all of `X`, answered by
their gradient.

**Formalization Note.** For such `f` the subdifferential at every point is `{fderiv ℝ f w}`, so the
oracle is `fderiv ℝ f`. The success set must be measurable, as in `IsAccurate`. -/
def IsAccurateC1 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (W : Set X) (ε : ℝ) {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (A : Ω → DetAlg X W T) : Prop :=
  ∀ f : X → ℝ, ConvexOn ℝ Set.univ f → ContDiff ℝ 1 f → LipschitzWith 1 f →
    MeasurableSet {ω | f ((A ω).lastQuery f (fderiv ℝ f)) - sInf (f '' W) ≤ ε} ∧
      (2⁻¹ : ENNReal) ≤ μ {ω | f ((A ω).lastQuery f (fderiv ℝ f)) - sInf (f '' W) ≤ ε}

end GradSuffice


