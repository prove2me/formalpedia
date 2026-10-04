-- Prove2me | Definitions.Def_StochApproxDyn_WeakAPT_OccupationMeasure
-- name    : StochApproxDyn_WeakAPT_OccupationMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:05:03.128267+00:00
-- url     : https://prove2.me/theorems/80f24073-23e5-4606-a03d-f52fe663358d
-- title:
--   Occupation measures $\mu_t(\omega)$ of a path and their weak limit points $\mathcal M(X,\omega)$ (§10)
-- statement:
--   Let $(M,d)$ be a metric space with its Borel $\sigma$-algebra and let $x:\mathbb R_+\to M$ be a Borel measurable path. For $t>0$ the **occupation measure** of $x$ on $[0,t]$ is the Borel probability measure
--   $$\mu_t=\frac1t\int_0^t\delta_{x(s)}\,ds,\qquad\text{i.e.}\qquad \mu_t(A)=\frac1t\,\mathrm{Leb}\{s\in[0,t]: x(s)\in A\}$$
--   for Borel $A\subset M$; it is the image of the uniform distribution on $[0,t]$ under $s\mapsto x(s)$, and $\int f\,d\mu_t=\frac1t\int_0^t f(x(s))\,ds$ for bounded measurable $f$.
--
--   For a process $X:\mathbb R_+\times\Omega\to M$ and $\omega\in\Omega$, write $\mu_t(\omega)$ for the occupation measure of the path $s\mapsto X(s,\omega)$, and let
--   $$\mathcal M(X,\omega)=\{\mu\in\mathcal P(M):\ \mu \text{ is a weak limit point of } \{\mu_t(\omega)\} \text{ as } t\to\infty\}.$$
--   The set $\mathcal M(X,\omega)$ is a (possibly empty) subset of $\mathcal P(M)$.
--
--   These objects carry the long-run statistics of a path. Theorem 10.1 shows that for a weak asymptotic pseudotrajectory of a semiflow they are almost surely invariant measures of the semiflow.
--
--   **Formalization Note** Limit points are cluster points of $t\mapsto\mu_t(\omega)$ along $t\to\infty$ in Mathlib's `ProbabilityMeasure M` (topology of weak convergence against bounded continuous functions). Lean needs a total definition: at $t=0$, and for a path that is not measurable, the value is set to the Dirac mass $\delta_{x(0)}$, never the zero measure. The value at $t=0$ does not affect limit points as $t\to\infty$, and the paths of a progressively measurable process are always measurable (proved in the definition of weak asymptotic pseudotrajectories), so the convention is never used in the theorems of this mission. A helper lemma records that for a measurable path and $t>0$ the measure is the push-forward of normalised Lebesgue measure on $[0,t]$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 10, p. 61 (PDF p. 62), definition of μ_t(ω) and M(X, ω)

import Mathlib

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω M : Type*} [MeasurableSpace M]

/-- The occupation measure `μ_t = (1/t) ∫_0^t δ_{x(s)} ds` of a path `x : ℝ≥0 → M` at time
`t > 0` (Benaïm 1999, §10, p. 61): the image of the uniform probability measure on `[0, t]` under
`s ↦ x(s)`, so that `μ_t(A) = (1/t) · Leb{s ∈ [0, t] : x(s) ∈ A}` for every Borel set `A`.
It is a Borel probability measure as soon as `x` is measurable and `t > 0`.

Totalisation: for `t = 0` (where `(1/t)∫_0^t` is undefined) and for a non-measurable path the
value is the Dirac mass `δ_{x(0)}`; the first case does not affect limit points as `t → ∞`, and
the second never arises for the paths of a progressively measurable process
(`IsProgressivelyMeasurable.measurable_path`). In particular the value is never the zero
measure. -/
noncomputable def occupationMeasure (x : ℝ≥0 → M) (t : ℝ≥0) : ProbabilityMeasure M :=
  open Classical in
  ⟨if Measurable x ∧ 0 < t then (volume[|Set.Icc (0 : ℝ) t]).map (fun s : ℝ => x s.toNNReal)
    else Measure.dirac (x 0), by
    split_ifs with h
    · have : IsProbabilityMeasure (volume[|Set.Icc (0 : ℝ) t]) :=
        cond_isProbabilityMeasure_of_finite
          (by simpa [Real.volume_Icc] using h.2.ne') (by simp [Real.volume_Icc])
      exact Measure.isProbabilityMeasure_map (h.1.comp measurable_real_toNNReal).aemeasurable
    · infer_instance⟩

/-- For a measurable path and `t > 0`, the occupation measure is the push-forward of the
normalised Lebesgue measure on `[0, t]`. -/
theorem coe_occupationMeasure {x : ℝ≥0 → M} (hx : Measurable x) {t : ℝ≥0} (ht : 0 < t) :
    (occupationMeasure x t : Measure M) =
      (volume[|Set.Icc (0 : ℝ) t]).map (fun s : ℝ => x s.toNNReal) := by
  have h : Measurable x ∧ 0 < t := ⟨hx, ht⟩
  simp only [occupationMeasure, ProbabilityMeasure.coe_mk]
  rw [if_pos h]

variable [TopologicalSpace M] [OpensMeasurableSpace M]

/-- The (possibly empty) set `𝓜(X, ω) ⊂ 𝓟(M)` of weak limit points of the occupation measures
`{μ_t(ω)}` of the path `t ↦ X(t, ω)` as `t → ∞` (Benaïm 1999, §10, p. 61): the cluster points of
`t ↦ μ_t(ω)` along `t → ∞` in the topology of weak convergence on `ProbabilityMeasure M`. -/
def occupationLimitPoints (X : ℝ≥0 → Ω → M) (ω : Ω) : Set (ProbabilityMeasure M) :=
  {μ | MapClusterPt μ atTop (fun t : ℝ≥0 => occupationMeasure (fun s => X s ω) t)}

end StochApproxDyn.WeakAPT


