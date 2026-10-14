-- Prove2me | Definitions.Def_DROReview_PhiDiv_phiDiv
-- name    : DROReview_PhiDiv_phiDiv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T21:16:18.017529+00:00
-- url     : https://prove2.me/theorems/927178e0-5ded-46df-b09c-20991b84f13d
-- title:
--   §5.1.2 — φ-divergence of probability measures, including singular mass
-- statement:
--   Let $P_1$ and $P_2$ be probability measures on a measurable space $(\Xi,\mathcal F)$, and let $\phi:[0,\infty)\to[0,\infty]$ be a divergence generator with $\phi(1)=0$. Set $\nu=P_1+P_2$, $p=dP_1/d\nu$, and $q=dP_2/d\nu$. The **$\phi$-divergence** is
--
--   $$
--   \mathfrak D^\phi(P_1,P_2)=\int_\Xi \begin{cases}q\phi(p/q),&q>0,\\p\phi'(\infty),&q=0\end{cases}\,d\nu,
--   \qquad \phi'(\infty)=\lim_{t\to\infty}\frac{\phi(t)}{t}.
--   $$
--
--   At $p=q=0$ the integrand is zero, including when $\phi'(\infty)=+\infty$. This common-measure form implements the conventions stated in §5.1.2 and includes the part of $P_1$ singular to $P_2$. It is the shared divergence used for all four Table 1 generators in this mission.
--
--   **Formalization Note** The recession slope is represented by a limsup, which equals the stated limit for the four convex generators used here. The Radon–Nikodym densities are finite $\nu$-almost everywhere. The generic operation does not require a convexity proof as an argument; the mission applies it only to the named Table 1 generators.
-- source:
--   Rahimian, Mehrotra, Distributionally Robust Optimization: A Review, arXiv:1908.05659v1 (2019), p. 31, §5.1.2, definition preceding (5.9)

import Mathlib

namespace DROReview.PhiDiv

open MeasureTheory Filter

/-- The recession slope `lim_{t → ∞} φ(t)/t` in §5.1.2, p. 31. For the four
generators used below the limsup is the limit specified in the paper. -/
noncomputable def phiSlope (φ : NNReal → ENNReal) : ENNReal :=
  limsup (fun t : NNReal => φ t / (t : ENNReal)) atTop

/-- The general-measure φ-divergence of §5.1.2, p. 31. The common dominating
measure is `ν = P₁ + P₂`, with densities `p` and `q`. This perspective form
includes the paper's conventions at `q = 0`: zero when `p = 0`, and
`p * lim φ(t)/t` when `p > 0`. The Radon–Nikodym derivatives are finite ν-a.e. -/
noncomputable def phiDiv {Ξ : Type*} [MeasurableSpace Ξ]
    (φ : NNReal → ENNReal) (P₁ P₂ : ProbabilityMeasure Ξ) : ENNReal :=
  let ν := P₁.toMeasure + P₂.toMeasure
  ∫⁻ x, (let p := P₁.toMeasure.rnDeriv ν x
          let q := P₂.toMeasure.rnDeriv ν x
          if q = 0 then p * phiSlope φ else q * φ (p / q).toNNReal) ∂ν

end DROReview.PhiDiv


