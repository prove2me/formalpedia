-- Prove2me | Definitions.Def_ConstDepthUnitary_Lg
-- name    : ConstDepthUnitary_Lg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:42.01769+00:00
-- url     : https://prove2.me/theorems/7c60b941-f15f-4f7c-b97e-a70630d99975
-- title:
--   The logarithm $\mathrm{Lg}(N,\varepsilon)$
-- statement:
--   $\mathrm{Lg}(N,\varepsilon)=\log_2(2+N/\varepsilon)$. It stands for the source's $\log(N/\varepsilon)$ in resource bounds: Theorem 6.1 quantifies all $\varepsilon>0$, while $\log\log(N/\varepsilon)$ is undefined or negative when $\varepsilon$ is near or above $N$. For $N\ge2$ and $\varepsilon\le1$ it is within a constant factor of $\log_2(N/\varepsilon)$, and it is always at least $1$.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 6.1, p.35

import Mathlib

namespace ConstDepthUnitary

/-- The logarithm `Lg(N, ε) = log₂(2 + N/ε)` standing for the paper's `log(N/ε)` in resource bounds: it stays
at least `1` for all `N, ε > 0`, and for `N ≥ 2`, `ε ≤ 1` it is within a constant of `log₂(N/ε)`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 6.1, p.35. -/
noncomputable def Lg (N ε : ℝ) : ℝ := Real.logb 2 (2 + N / ε)

end ConstDepthUnitary


