-- Prove2me | Definitions.Def_DirectTradeCoffee_lambertW
-- name    : DirectTradeCoffee_lambertW
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:50:04.047468+00:00
-- url     : https://prove2.me/theorems/0bb0ab8d-b1d6-4ca3-bd1a-99848e4cd9f1
-- title:
--   Principal Lambert W function $W$ on $[0,\infty)$
-- statement:
--   The **Lambert W function** is the inverse of $w \mapsto w e^{w}$. On $[0,\infty)$ this map is a strictly increasing bijection, so for $x \ge 0$ there is exactly one $w \ge 0$ with
--
--   $$
--   W(x)\, e^{W(x)} = x .
--   $$
--
--   The function $W$ appears in every closed form of the mission: the unconstrained second-stage quantity and the acreage benchmarks.
--
--   **Formalization Note** Only nonnegative arguments occur. For $x<0$ the definition returns the placeholder value $0$.
-- source:
--   Webster–Kazaz–Gheibi, Direct Trade Sourcing Strategies for Specialty Coffee, MSOM (2024), doi:10.1287/msom.2021.0586, §3.2, p.10 ("W(·) is the Lambert W function, which is the inverse of x = We^W")

import Mathlib

namespace DirectTradeCoffee

/-- **Principal Lambert W function on `[0, ∞)`.**
Webster–Kazaz–Gheibi, *Direct Trade Sourcing Strategies for Specialty Coffee*, MSOM (2024),
doi:10.1287/msom.2021.0586, §3.2, p.10: "`W(·)` is the Lambert W function, which is the inverse of
`x = We^W`".

For `x ≥ 0`, `lambertW x` is the unique `w ≥ 0` with `w * exp w = x`.

**Formalization Note.** Every argument used in the paper is positive, and only the branch on
`[0, ∞)` occurs. For `x < 0` no such `w` exists and the definition returns the junk value `0`. -/
noncomputable def lambertW (x : ℝ) : ℝ :=
  open Classical in
  if h : ∃ w : ℝ, 0 ≤ w ∧ w * Real.exp w = x then Classical.choose h else 0

end DirectTradeCoffee


