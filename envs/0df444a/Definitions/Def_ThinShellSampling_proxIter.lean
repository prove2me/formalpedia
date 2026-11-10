-- Prove2me | Definitions.Def_ThinShellSampling_proxIter
-- name    : ThinShellSampling_proxIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:12.974562+00:00
-- url     : https://prove2.me/theorems/3e16b53f-e288-4828-a4fc-df414939d45a
-- title:
--   Law of the $N$-th iterate of the Proximal sampler
-- statement:
--   For a target $\pi^X$ on $\mathbb R^n$ and a step size $h>0$, the **Proximal sampler** alternates
--
--   1. $y_{k+1}\sim\pi^{Y|X=x_k}=N(x_k,hI_n)$,
--   2. $x_{k+1}\sim\pi^{X|Y=y_{k+1}}$, where $\pi^{X|Y=y}(dx)\propto\pi^X(dx)\,e^{-\|x-y\|^2/(2h)}$.
--
--   Starting from $x_0\sim\pi^X_0$, the law of $x_N$ is denoted $\pi^X_N$. The module also provides the generic step $\mu\mapsto$ law of $x'$, for any target, forward kernel and squared distance, reused for the lifted sampler of §6.3.1.
--
--   The mixing of this chain under (LSI) is Corollary 1.3.
--
--   **Formalization Note** The laws are computed with `Measure.bind`; the backward kernel is the exact conditional law (the ideal sampler), which by Lemma 2.6 is also the law of an accepted rejection-sampling proposal.
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), §1.2, p.5 (PDF p.7); §2, p.14 (PDF p.16); Corollary 1.3, p.3

import Mathlib
import Definitions.Def_ThinShellSampling_expTilt
import Definitions.Def_ThinShellSampling_heatAdjoint

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **One step of a proximal sampler, as a map on laws.** Given a target `π`, a forward kernel
`fwd` (`y ∼ fwd x`) and a squared distance `w`, the step sends the law `μ` of the current point to
the law of `x' ∼ π^{X|Y=y}(dx') ∝ π(dx') e^{−w(x', y)/(2h)}` where `y ∼ fwd x`, `x ∼ μ`.

Kook, Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity*, STOC 2027 submission
(manuscript sha256 25a041a9…), §1.2, p.5 (PDF p.7) and §2, p.14 (PDF p.16): "`P_h(x, dy) = π^{Y|X=x}
= N(x, hIₙ)`, `Q_h(y, dx) = π^{X|Y=y} ∝ π^X(·) γ_h(· − y)`".

**Formalization Note.** The step is `(μ.bind fwd).bind (y ↦ expTilt π (x ↦ w x y/(2h)))`. Both
kernels used in this mission are measurable maps into the space of measures, so `Measure.bind`
computes the law of the two-step transition; the backward kernel is the exact conditional law (the
law of an accepted rejection-sampling proposal, Lemma 2.6). -/
noncomputable def proxStepGen {X : Type*} [MeasurableSpace X] (π : Measure X)
    (fwd : X → Measure X) (w : X → X → ℝ) (h : ℝ) (μ : Measure X) : Measure X :=
  (μ.bind fwd).bind (fun y => expTilt π (fun x => w x y / (2 * h)))

/-- **Law `π^X_N` of the `N`-th iterate of the Proximal sampler** on `ℝⁿ` with target `π`, step
size `h > 0` and initial law `π^X_0 = μ₀`.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §1.2, p.5 (PDF p.7):
"(i) `y_{k+1} ∼ π^{Y|X=x_k} = N(x_k, hIₙ)` and (ii) `x_{k+1} ∼ π^{X|Y=y_{k+1}}`", where the augmented
target is `π(x, y) ∝ π^X(x) γ_h(y − x)`; Corollary 1.3, p.3 (PDF p.5).

**Formalization Note.** The forward kernel is `x ↦ law of x + G`, `G ∼ γ_h`; the backward kernel
is `π` tilted by `e^{−‖x − y‖²/(2h)}` and normalized. This is the ideal (exact) sampler. -/
noncomputable def proxIter (n : ℕ) (π : Measure (EuclideanSpace ℝ (Fin n))) (h : ℝ) (N : ℕ)
    (μ₀ : Measure (EuclideanSpace ℝ (Fin n))) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (proxStepGen π (fun x => (gaussianT n h).map (fun z => x + z)) (fun x y => ‖x - y‖ ^ 2) h)^[N]
    μ₀

end ThinShellSampling


