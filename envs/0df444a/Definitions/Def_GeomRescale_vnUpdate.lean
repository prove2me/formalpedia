-- Prove2me | Definitions.Def_GeomRescale_vnUpdate
-- name    : GeomRescale_vnUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:37.039759+00:00
-- url     : https://prove2.me/theorems/fd51486e-9db5-4615-9416-3ca6e4d0770d
-- title:
--   Lines 11–15 of Algorithm 1
-- statement:
--   For the vector $g = g_k$ the algorithm sets
--
--   $$\lambda := \frac{\langle y - g/\|g\|_Q,\ y \rangle_Q}{\|y - g/\|g\|_Q\|_Q^2}, \qquad y := (1 - \lambda) y + \lambda \frac{g}{\|g\|_Q},$$
--
--   $x_k := \lambda$, $x_i := (1 - \lambda) x_i$ for $i < k$, and $k := k + 1$. The new $y$ is the point of minimum $Q$-norm on the segment $[y, g/\|g\|_Q]$.
--
--   **Formalization Note** The step is charged $n^2$ operations for lines 11–12 and $k$ for lines 13–15. Lean's $x/0 = 0$ gives $\lambda = 0$ on a vanishing denominator, a case that a run does not reach.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, lines 11–15, p.8

import Mathlib
import Definitions.Def_GeomRescale_unitQ
import Definitions.Def_GeomRescale_VN

namespace GeomRescale

/-- Lines 11–15 of Algorithm 1 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, p.8), for the vector `g = g_k`:
`λ := ⟨y − g/‖g‖_Q, y⟩_Q / ‖y − g/‖g‖_Q‖²_Q`, `y := (1 − λ)y + λ g/‖g‖_Q`, `x_k := λ`,
`x_i := (1 − λ)x_i` for `i < k`, `k := k + 1`.

**Formalization Note.** Lean's `x / 0 = 0` makes `λ = 0` when the denominator vanishes. That case
needs `y = g/‖g‖_Q ≠ 0`, which cannot occur along a run, since `⟨y, g⟩_Q ≤ 0` at line 11. The charge
is `n²` for lines 11–12 and `k` for lines 13–15 ("time `O(k)`", p.12). -/
noncomputable def vnUpdate {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) (v : VN n) :
    VN n :=
  let u := unitQ Q g
  let lam := qdot Q (v.y - u) v.y / qnorm Q (v.y - u) ^ 2
  { v with
    y := (1 - lam) • v.y + lam • u
    data := v.data.map (fun p => (p.1, (1 - lam) * p.2)) ++ [(g, lam)]
    ops := v.ops + n ^ 2 + (v.data.length + 1) }

end GeomRescale


