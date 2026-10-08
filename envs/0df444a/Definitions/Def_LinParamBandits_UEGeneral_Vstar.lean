-- Prove2me | Definitions.Def_LinParamBandits_UEGeneral_Vstar
-- name    : LinParamBandits_UEGeneral_Vstar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:15.106963+00:00
-- url     : https://prove2.me/theorems/44605c84-eafa-427e-9947-65b92aeb2685
-- title:
--   p. 38 — the optimization problem V*(c, t)
-- statement:
--   For $c \ge 0$, an integer $t \ge 1$ and the dimension $r$, Rusmevichientong and Tsitsiklis define
--   $$V^*(c, t) = \max \sum_{s=1}^t y_s \quad \text{s.t.}\quad 0 \le y_s \le c \ \text{ and }\ y_s \le \frac{\{c\cdot(r+s)\}^r}{\prod_{q=1}^{s-1}(1+y_q)}, \qquad s = 1, \dots, t,$$
--   with the empty product $\prod_{q=1}^0(1+y_q) = 1$.
--
--   The problem bounds the sum $\sum_{t=r}^{T-1}\|U_{t+1}\|^2_{C_t}$ of the UE policy's weighted arm norms (Lemma B.10), and Lemma B.11 bounds it explicitly.
--
--   **Formalization Note** `VstarFeasible r c t` is the feasible set in $\mathbb R^t$, entry `s : Fin t` being $y_{s+1}$; `Vstar r c t` is the real supremum of $\sum_s y_s$ over it. For $c \ge 0$ the set contains $y = 0$, is bounded ($0 \le y_s \le c$) and closed, so the supremum is the maximum. The dimension $r$ is an explicit argument.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, App. B.2, p. 38 (definition of V*(c, t))

import Mathlib

namespace LinParamBandits.UEGeneral

/-- The feasible set of the optimization problem defining `V*(c, t)` (p. 38), in dimension `r`:
vectors `y = (y_1, …, y_t)` with `0 ≤ y_s ≤ c` and
`y_s ≤ {c · (r + s)}^r / ∏_{q=1}^{s-1} (1 + y_q)` for `s = 1, …, t` (empty product `= 1`).
Entry `s : Fin t` is the paper's `y_{s+1}`. -/
def VstarFeasible (r : ℕ) (c : ℝ) (t : ℕ) : Set (Fin t → ℝ) :=
  {y | ∀ s : Fin t, 0 ≤ y s ∧ y s ≤ c ∧
    y s ≤ (c * ((r : ℝ) + ((s : ℕ) + 1))) ^ r / ∏ q ∈ Finset.Iio s, (1 + y q)}

/-- `V*(c, t) = max ∑_{s=1}^t y_s` over the feasible set (p. 38). For `c ≥ 0` the feasible set
contains `y = 0` and is bounded (`y_s ≤ c`) and closed, so the supremum is the maximum. -/
noncomputable def Vstar (r : ℕ) (c : ℝ) (t : ℕ) : ℝ :=
  sSup ((fun y : Fin t → ℝ => ∑ s, y s) '' VstarFeasible r c t)

end LinParamBandits.UEGeneral


