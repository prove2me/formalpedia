-- Prove2me | Definitions.Def_AndOrSched_tau
-- name    : AndOrSched_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:17.109343+00:00
-- url     : https://prove2.me/theorems/4ccce20e-f2c4-47d0-888a-b5d94fa9bd36
-- title:
--   Interval end points $\tau_l$
-- statement:
--   $$\tau_0:=1,\qquad \tau_l=(1+\varepsilon')^{l-1}\quad(l\ge1).$$
--   The $l$-th interval is $(\tau_{l-1},\tau_l]$; the first is the singleton $\{1\}$.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.9, "Set τ0 := 1, and let τl = (1 + ε′)^(l−1)"

import Mathlib
open scoped Classical NNReal

namespace AndOrSched

/-- The interval end points `τ₀ := 1` and `τ_l = (1 + ε′)^(l−1)` for `l ≥ 1` (Happach, Schulz, arXiv:2001.07011v1, §2, p.9). The
`l`-th interval is `(τ_{l−1}, τ_l]`; the first one is the singleton `{1}`. -/
noncomputable def tau (ε' : ℝ) (l : ℕ) : ℝ :=
  if l = 0 then 1 else (1 + ε') ^ (l - 1)

end AndOrSched


