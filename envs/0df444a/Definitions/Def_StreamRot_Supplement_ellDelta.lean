-- Prove2me | Definitions.Def_StreamRot_Supplement_ellDelta
-- name    : StreamRot_Supplement_ellDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:23:24.695194+00:00
-- url     : https://prove2.me/theorems/2a4c3783-ebf1-4756-9b91-4e4638e73489
-- title:
--   Confidence length $\ell_\delta(N)$
-- statement:
--   For a horizon $N$ and a failure probability $\delta$, the **confidence length** is
--   $$
--   \ell_\delta(N)=\begin{cases}\min\{N,\log(2/\delta)\}, & 0<\delta\le 1/3,\\ N, & \delta=0,\end{cases}
--   $$
--   with the natural logarithm. It is the factor by which the upper width bound (B.2) of the confidence-uniform width law depends on the confidence level: at $\delta=0$ it is the horizon, and for positive $\delta$ it is capped by $\log(2/\delta)$.
--
--   **Formalization Note** The value is defined by cases on $\delta>0$, so $\delta=0$ gives $N$ and never $\log(2/0)$. A negative $\delta$ also gives $N$; Theorem B.1 uses only $0\le\delta\le 1/3$.
-- source:
--   Qi, Constant-Failure Width Bounds for Streaming Rotations, STOC 2027 submission (manuscript sha256 3ffd9cd7…), Section B.1, p.20 (PDF 22); Section 7, p.9 (PDF 11)

import Mathlib

namespace StreamRot

namespace Supplement

/-- The confidence length `ℓ_δ(N) = min{N, log(2/δ)}` for `0 < δ ≤ 1/3`, and `ℓ_0(N) = N`, with the natural
logarithm. Qi, Constant-Failure Width Bounds for Streaming Rotations, STOC 2027 submission (manuscript sha256 3ffd9cd7…), Section B.1, p.20 (also Section 7, p.9).

**Formalization Note** The value is defined by cases on `0 < δ`, so `δ = 0` gives `N` and never `log(2/0)`.
Negative `δ` also gives `N`; Theorem B.1 only uses `0 ≤ δ ≤ 1/3`. -/
noncomputable def ellDelta (N : ℕ) (δ : ℝ) : ℝ :=
  if 0 < δ then min (N : ℝ) (Real.log (2 / δ)) else (N : ℝ)

end Supplement

end StreamRot


