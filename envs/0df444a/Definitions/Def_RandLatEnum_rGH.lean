-- Prove2me | Definitions.Def_RandLatEnum_rGH
-- name    : RandLatEnum_rGH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:20.727666+00:00
-- url     : https://prove2.me/theorems/fa8c28d8-aa3b-49d1-a6c3-d9e35f9dddfc
-- title:
--   Radius of the ball of volume one, $r_d=V_d^{-1/d}$
-- statement:
--   For $d\ge 1$,
--   $$
--   r_d=V_d^{-1/d}
--   $$
--   is the radius of a ball of volume one in $\mathbb R^d$ (the Gaussian-heuristic prediction for $\lambda_1$ of a unimodular rank-$d$ lattice).
--
--   **Formalization Note** A real power of $V_d>0$. Statements use only $d\ge1$.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.2, (2.5), p.15

import Mathlib
import Definitions.Def_RandLatEnum_unitBallVol

namespace RandLatEnum

/-- The radius of the ball of volume one, `r_d = V_d^{−1/d}` (`d ≥ 1`) (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.2, (2.5), p.15).

**Formalization Note.** A real power of the positive number `V_d`. At `d = 0` (outside the page's
range) the exponent is `−1/0 = 0` in Lean and the value is `1`; no statement uses `d = 0`. -/
noncomputable def rGH (d : ℕ) : ℝ :=
  unitBallVol d ^ (-(1 : ℝ) / d)

end RandLatEnum


