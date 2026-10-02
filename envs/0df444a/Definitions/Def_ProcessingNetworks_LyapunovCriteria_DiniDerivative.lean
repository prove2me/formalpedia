-- Prove2me | Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
-- name    : ProcessingNetworks_LyapunovCriteria_DiniDerivative
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:55:41.126902+00:00
-- url     : https://prove2.me/theorems/f6db3339-c05c-4f56-87cd-82beaab64f25
-- title:
--   The upper-right Dini derivative (Appendix A.4, Eq. A.9)
-- statement:
--   The **upper-right Dini derivative** of $f$ at $t$ (Appendix A.4, Eq. A.9) is
--   $$
--   D^+f(t) := \limsup_{h \downarrow 0} \frac{f(t+h) - f(t)}{h}.
--   $$
--   Unlike the ordinary derivative, $D^+f(t)$ is defined at *every* point $t$ (it may be
--   $+\infty$ or $-\infty$), which is exactly why Lemma 8.11 can state its hypotheses for every
--   $t$ rather than only regular points.
--
--   **Formalization note.** Restated directly via `Filter.limsup` along the right-neighborhood
--   filter of $0$, rather than imported from an appendix (out of series scope, per
--   `missions/README.md`). The value is taken in the extended reals $\overline{\mathbb{R}}$: the
--   upper Dini derivative of a merely continuous function can be $+\infty$ (at a point of a
--   Cantor-type increase) or $-\infty$, and a real-valued `limsup` would replace such values by a
--   junk real, silently turning Lemma 8.11's bound (b) into a vacuous condition exactly at the
--   points it is meant to exclude.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 139, Appendix A.4, Eq. (A.9) (restated)

import Mathlib

namespace ProcessingNetworks.LyapunovCriteria

/-- The upper-right Dini derivative `D⁺f(t)`, Appendix A.4, Eq. (A.9) — restated inline since the
appendices are out of series scope: `D⁺f(t) := limsup_{h ↓ 0} (f(t+h) - f(t))/h`, taken in the
extended reals `EReal` so that the values `+∞` and `-∞` (which the Dini derivative of a merely
continuous function can take) are represented as such rather than by a junk real value. -/
noncomputable def diniUpperRight (f : ℝ → ℝ) (t : ℝ) : EReal :=
  Filter.limsup (fun h : ℝ => (((f (t + h) - f t) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

end ProcessingNetworks.LyapunovCriteria


