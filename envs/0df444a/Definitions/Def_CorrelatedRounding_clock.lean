-- Prove2me | Definitions.Def_CorrelatedRounding_clock
-- name    : CorrelatedRounding_clock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:23.677198+00:00
-- url     : https://prove2.me/theorems/ec6d77ce-5994-44a7-9d4a-dc6224e4c679
-- title:
--   The dilated clock $(y_k/u_{ki})E_k$
-- statement:
--   Given a real vector $E=(E_k)_k$, the clock of FC $k$ for item $i$ is the extended real number
--   $$\frac{y_k}{u_{ki}}E_k\quad\text{if } u_{ki}\neq 0,\qquad \infty\quad\text{if } u_{ki}=0.$$
--   It is the delayed time at which item $i$ sees FC $k$ open, since $y_k/u_{ki}\ge 1$.
--
--   **Formalization Note.** The value lies in `EReal`. The real quotient $y_k/0$ is $0$ in Lean, and without the $\infty$ branch an FC of probability zero would win every minimum.
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, §2.1, p.9, and Algorithm 1, p.10

import Mathlib
import Definitions.Def_CorrelatedRounding_y

namespace CorrelatedRounding

/-- **The dilated clock `(y_k / u_ki) E_k`.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4,
§2.1, p.9: "(y_k/u_ki) E_k is the delayed time … at which item i sees it open, with (y_k/u_ki) E_k = ∞
if u_ki = 0", and Algorithm 1, p.10.

**Formalization Note.** The value lies in `EReal`, because the page's value at `u_ki = 0` is `∞`. In
Lean the real quotient `y_k / 0` is `0`, so without the `⊤` branch an FC of probability zero would win
every arg min. Only `≤` is ever applied to clocks, so no `EReal` arithmetic occurs. -/
noncomputable def clock {q K : ℕ} (u : Fin K → Fin q → ℝ) (E : Fin K → ℝ)
    (k : Fin K) (i : Fin q) : EReal :=
  if u k i = 0 then ⊤ else ((y u k / u k i * E k : ℝ) : EReal)

end CorrelatedRounding


