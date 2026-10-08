-- Prove2me | Definitions.Def_TaoAnDCA_Restart_Setting
-- name    : TaoAnDCA_Restart_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:34.971567+00:00
-- url     : https://prove2.me/theorems/5e662962-7447-4797-ab05-bd15d9fe64f4
-- title:
--   §1 and §4.2, pp. 476, 491–492 — the quadratic f of (Q1), Kuhn–Tucker points, and the restart step γ of (23)
-- statement:
--   Throughout, $A$ is a real symmetric $n\times n$ matrix, $b\in\mathbb R^n$ and $r>0$. The **trust-region subproblem** (Q1) is to minimize
--   $$f(x)=\tfrac12\langle x,Ax\rangle+\langle b,x\rangle\qquad\text{subject to } \|x\|\le r .$$
--
--   1. The **objective** $f$ is the quadratic above (no constraint built in).
--   2. A point $x^*$ is a **Kuhn–Tucker point** of (Q1) with multiplier $\lambda^*$ when
--   $$\lambda^*\ge 0,\qquad (A+\lambda^*I)x^*=-b,\qquad \lambda^*(\|x^*\|-r)=0,\qquad \|x^*\|\le r .$$
--   3. For a direction $u\ne 0$ and a point $x^*$ with $\|x^*\|\le r$, the **restart step** of (23) is the nonzero root $\gamma$ of $\|u\|^2\gamma^2+2u^Tx^*\gamma+\|x^*\|^2-r^2=0$, namely
--   $$\gamma=\begin{cases}-2(u^Tx^*)/\|u\|^2 & \text{if } \|x^*\|=r,\\ \bigl(-(u^Tx^*)+s\sqrt{\Delta}\bigr)/\|u\|^2 & \text{if } \|x^*\|<r,\end{cases}\qquad \Delta=(u^Tx^*)^2-\|u\|^2(\|x^*\|^2-r^2),$$
--   where the sign $s\in\{1,-1\}$ selects the root "$\pm$".
--
--   These are the objects of the restart procedure of §4.2: a Kuhn–Tucker point produced by the DCA is tested for global optimality, and when the test fails, the point $x^*+\gamma u$ is the new starting point.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $A$ is a continuous linear operator on it; symmetry is the hypothesis `IsSelfAdjoint A` in each theorem, not part of the definitions. The restart step takes the sign $s$ as a real parameter; the theorems restrict it to $s=\pm1$. Its value is meaningful only for $u\ne 0$ and $\|x^*\|\le r$, which the theorems assume (for $\|x^*\|<r$ the radicand $\Delta$ is then positive).
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 476 (Q1); p. 491, Theorem 4.1(iii); p. 492, (23)

import Mathlib
import Definitions.Def_TaoAnDCA_TRS_Setting

namespace TaoAnDCA.Restart

/-- The step length `γ` of (23) (p. 492) along a direction `u` from `x*`:
`γ = −2(uᵀx*)/‖u‖²` if `‖x*‖ = r`, and `γ = (−(uᵀx*) + s√Δ)/‖u‖²` otherwise, where
`Δ = (uᵀx*)² − ‖u‖²(‖x*‖² − r²)` and the sign `s ∈ {1, −1}` selects the root `±`. -/
noncomputable def restartGamma {n : ℕ} (u xs : EuclideanSpace ℝ (Fin n)) (r s : ℝ) : ℝ :=
  if ‖xs‖ = r then -2 * inner ℝ u xs / ‖u‖ ^ 2
  else (-(inner ℝ u xs) + s * Real.sqrt ((inner ℝ u xs) ^ 2 - ‖u‖ ^ 2 * (‖xs‖ ^ 2 - r ^ 2))) / ‖u‖ ^ 2

end TaoAnDCA.Restart


