-- Prove2me | Definitions.Def_ProactiveUpgrade_vhat
-- name    : ProactiveUpgrade_vhat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:45.403279+00:00
-- url     : https://prove2.me/theorems/721db382-2998-428f-88e0-d3da130bd77f
-- title:
--   The optimal profit function $\hat v_t(x)$
-- statement:
--   The optimal profit function $\hat v_t(x)$ is the optimal revenue collected from period $t$ to the end of a season of $T$ periods, starting with inventory $x$. It is defined by backward recursion from $\hat v_{T+1}(x)=0$ for all $x\ge0$ (footnote 15) through the optimality equation (10):
--
--   $$
--   \hat v_t(x)=\sum_{i\in\mathcal M}\lambda\beta_i\hat T_i[\hat v_t(x)]+[\lambda\beta_0+(1-\lambda)]\hat v_{t+1}(x),\qquad t=1,\dots,T.
--   $$
--
--   **Formalization Note** The recursion counts periods to go: `valueToGo M 0 = 0` and `valueToGo M (n+1) = step M (valueToGo M n)`, and `vhat M T t = valueToGo M (T + 1 - t)`. This is the paper's $\hat v_t$ for $1\le t\le T+1$; every statement binds $1\le t\le T$.
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, §3.2.3, eq. (10) and footnote 15, p.12

import Mathlib
import Definitions.Def_ProactiveUpgrade_Model

namespace ProactiveUpgrade

/-- The optimal revenue with `n` periods to go: `valueToGo M 0 = 0` and
`valueToGo M (n + 1) = step M (valueToGo M n)` (backward recursion of (10), p.12). -/
def valueToGo {m : ℕ} (M : Model m) : ℕ → (Fin m → ℕ) → ℝ
  | 0 => fun _ => 0
  | n + 1 => step M (valueToGo M n)

/-- **The optimal profit function `v̂ₜ(x)`** (Chen et al., SSRN 3777846, §3.2.3, eq. (10)–(12),
pp.12–13): the optimal revenue collected from period `t` to the end of a season of `T` periods,
starting from inventory `x`, with `v̂_{T+1}(x) = 0` for all `x ≥ 0` (footnote 15, p.12).

**Formalization Note** Periods are counted to go: `vhat M T t = valueToGo M (T + 1 - t)`, which is
the paper's `v̂ₜ` for `1 ≤ t ≤ T + 1` (every statement binds `1 ≤ t ≤ T`). -/
def vhat {m : ℕ} (M : Model m) (T t : ℕ) (x : Fin m → ℕ) : ℝ :=
  valueToGo M (T + 1 - t) x

end ProactiveUpgrade


