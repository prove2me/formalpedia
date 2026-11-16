-- Prove2me | Definitions.Def_ZCDPtoGDP_Sharp_Supplement_Angular
-- name    : ZCDPtoGDP_Sharp_Supplement_Angular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:09:52.710741+00:00
-- url     : https://prove2.me/theorems/c69c6b08-60d5-4022-919d-7862787a6bf6
-- title:
--   The uniform angular law and reciprocal cosine square of Lemma 21
-- statement:
--   Let $\nu$ be the uniform probability law on $[0,\pi/4]$, expressed directly by its Lebesgue density, and define
--   $$\nu=\frac4\pi\,\lambda\!\restriction_{[0,\pi/4]},\qquad A(\theta)=\frac{1}{8\cos^2\theta}.$$
--   The interval has length $\pi/4>0$, so $\nu$ has total mass one. On this interval $\cos\theta>0$ and $1/8\le A(\theta)\le1/4$.
--
--   These objects specify the Laplace expectation in Lemma 21. The boundedness makes the exponential integrands integrable for every nonnegative $s$; no separate integrability assumption is needed. The totalized reciprocal away from the interval has no effect on a random variable with this law.
-- source:
--   Yu-Wei Chen, Aaradhya Pandey, Jordan Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), Lemma 21, p. 23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf

import Mathlib

open MeasureTheory

namespace ZCDPtoGDP.Sharp.Supplement

/-! Source: Chen–Pandey–Awan, STOC 2027 submission #235 (October 2026),
Lemma 21 and its density calculation, p. 23. -/

/-- The uniform law on `[0,π/4]`, explicitly with Lebesgue density `4/π`.
It has mass one because the interval has length `π/4 > 0`. -/
noncomputable def angularLaw : Measure ℝ :=
  ENNReal.ofReal (4 / Real.pi) • volume.restrict (Set.Icc 0 (Real.pi / 4))

/-- Lemma 21's `A(θ)`. On the support of `angularLaw`, `cos θ > 0` and
`1/8 ≤ A(θ) ≤ 1/4`. The totalized values away from that interval are unused. -/
noncomputable def angularA (θ : ℝ) : ℝ := 1 / (8 * Real.cos θ ^ 2)

end ZCDPtoGDP.Sharp.Supplement


