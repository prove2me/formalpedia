-- Prove2me | Definitions.Def_GeomDL_RNN_Recurrence
-- name    : GeomDL_RNN_Recurrence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:51.983849+00:00
-- url     : https://prove2.me/theorems/e4003c63-c417-461d-95b4-daf56cb20a0c
-- title:
--   §5.7, pp. 90, 93 — RNN recurrence and zero left padding
-- statement:
--   Let an input vector have $k$ real coordinates and a hidden state have $m$ real coordinates. An update map $R:\mathbb R^k\times\mathbb R^m\to\mathbb R^m$ and seed $h_0$ define the RNN run by
--
--   $$
--   h(0)=h_0,\qquad h(t+1)=R(z(t+1),h(t)).
--   $$
--
--   For a padding length $d$, define the left-padded input by $\bar z(t)=0$ for $t\le d$ and $\bar z(t)=z(t-d)$ for $t>d$.
--
--   These definitions fix the sequence boundary used by the shift-equivariance claims. The input $z(0)$ is unused, as the book indexes its first input by $1$.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §5.7, equation (38), p. 90; left-padding display, p. 93

import Mathlib

namespace GeomDL.RNN

/-- Equation (38), p. 90: `z 0` is unused; `h 0` is the seed. -/
def run {k m : ℕ}
    (R : (Fin k → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (h0 : Fin m → ℝ) (z : ℕ → Fin k → ℝ) : ℕ → Fin m → ℝ
  | 0 => h0
  | t + 1 => R (z (t + 1)) (run R h0 z t)

/-- The left-padded sequence on p. 93. -/
def pad {k : ℕ} (delay : ℕ) (z : ℕ → Fin k → ℝ)
    (t : ℕ) : Fin k → ℝ :=
  if t ≤ delay then 0 else z (t - delay)

end GeomDL.RNN


