-- Prove2me | Definitions.Def_MeanOnlyProphet_Supplement_twoStepTheta
-- name    : MeanOnlyProphet_Supplement_twoStepTheta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:27:28.346208+00:00
-- url     : https://prove2.me/theorems/d28348d6-9de6-4a34-afb5-d659df91fb82
-- title:
--   The two-step drop rate and two-segment threshold of §4.2
-- statement:
--   The **two-step drop rate** and its threshold are
--   $$
--   b(t)=\begin{cases}1/2,&0\le t<2/3,\\ 1,&2/3\le t\le 1,\end{cases}\qquad
--   \theta(t)=\int_t^1 b(s)\,ds=\begin{cases}2/3-t/2,&0\le t\le 2/3,\\ 1-t,&2/3\le t\le 1.\end{cases}
--   $$
--   The threshold is continuous, concave and piecewise linear, with $\theta(0)=2/3$, $\theta(2/3)=1/3$ and $\theta(1)=0$. It is the threshold of Theorem 4.2, the paper's one-page warm-up that beats the ratio $1-1/e$ in prophet secretary.
--
--   **Formalization Note** $\theta$ is defined by the explicit piecewise formula printed in the paper; both pieces agree at $t=2/3$. Values outside $[0,1]$ are never used.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), §4.2, p.13 (PDF p.14)

import Mathlib

namespace MeanOnlyProphet.Supplement

/-- **The two-step drop rate of §4.2.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*,
arXiv:2610.24711 (held version, sha256 c68bfec4…), §4.2, p.13 (PDF p.14): "b(t) = 1/2, 0 ≤ t < 2/3;
1, 2/3 ≤ t ≤ 1". -/
noncomputable def twoStepRate (t : ℝ) : ℝ :=
  if t < 2 / 3 then 1 / 2 else 1

/-- **The two-segment threshold of §4.2.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*,
arXiv:2610.24711 (held version, sha256 c68bfec4…), §4.2, p.13 (PDF p.14): "θ(t) = ∫_t^1 b(s) ds =
2/3 − t/2, 0 ≤ t ≤ 2/3; 1 − t, 2/3 ≤ t ≤ 1."

**Formalization Note.** The explicit piecewise formula printed on the page; both pieces give
`θ(2/3) = 1/3`, and `θ(0) = 2/3`, `θ(1) = 0`. Values outside `[0,1]` are never used (arrival times lie
in `[0,1]`). -/
noncomputable def twoStepTheta (t : ℝ) : ℝ :=
  if t ≤ 2 / 3 then 2 / 3 - t / 2 else 1 - t

end MeanOnlyProphet.Supplement


