-- Prove2me | Definitions.Def_SmoothedNash_rho
-- name    : SmoothedNash_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:43.314424+00:00
-- url     : https://prove2.me/theorems/a8d7fd36-5d61-4f41-853f-76e7de9f451a
-- title:
--   Search radius $\rho_t = 2m\,2^{-t}$
-- statement:
--   The **search radius** at level $t \ge 0$ is
--   $$
--   \rho_t = 2m \, 2^{-t}.
--   $$
--   Since $K_A$ has $\ell_1$-diameter at most $2m$, $\rho_0$ covers $K_A$; each level halves the radius. The level-$t$ test uses the tolerance $2\rho_t$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §2.1.1, p.14

import Mathlib

namespace SmoothedNash

/-- The search radius `ρ_t = 2m · 2^{−t}` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §2.1.1, p.14). -/
noncomputable def rho (m t : ℕ) : ℝ :=
  2 * m / 2 ^ t

end SmoothedNash


