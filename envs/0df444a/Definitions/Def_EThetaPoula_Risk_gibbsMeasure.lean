-- Prove2me | Definitions.Def_EThetaPoula_Risk_gibbsMeasure
-- name    : EThetaPoula_Risk_gibbsMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:57.560513+00:00
-- url     : https://prove2.me/theorems/a008fab0-5d71-4e19-b872-3dc7e2364774
-- title:
--   The Gibbs measure $\pi_\beta$, (3)
-- statement:
--   For $u:\mathbb R^d\to\mathbb R$ and $\beta>0$, the Gibbs measure is
--   $$
--   \pi_\beta(A):=\frac{\int_A e^{-\beta u(\theta)}\,d\theta}{\int_{\mathbb R^d}e^{-\beta u(\theta)}\,d\theta},\qquad A\in\mathcal B(\mathbb R^d).
--   $$
--   It is the target distribution of Langevin algorithms; for large $\beta$ it concentrates near the minimizers of $u$.
--
--   **Formalization Note** The measure is Lebesgue measure with the normalized density. It is a probability measure under the paper's hypothesis $\int e^{-\beta u}<\infty$, which statements carry as an `Integrable` hypothesis.
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §2.1, (3), p.3

import Mathlib

open MeasureTheory

namespace EThetaPoula.Risk

/-- **The Gibbs measure** `π_β(A) := ∫_A e^{−βu(θ)} dθ / ∫ e^{−βu(θ)} dθ` of (3), Lim, Neufeld,
Sabanis, Zhang, arXiv:2210.13193v3, §2.1, p.3.

**Formalization Note.** The measure is Lebesgue measure `volume` with the normalized density. It
is a probability measure exactly under the paper's hypothesis `∫ e^{−βu} < ∞` (with `u` measurable
on a space of positive volume); statements state that hypothesis as `Integrable`. -/
noncomputable def gibbsMeasure {E : Type*} [MeasureSpace E] (u : E → ℝ) (β : ℝ) : Measure E :=
  volume.withDensity fun θ =>
    ENNReal.ofReal (Real.exp (-β * u θ) / ∫ θ', Real.exp (-β * u θ'))

end EThetaPoula.Risk


