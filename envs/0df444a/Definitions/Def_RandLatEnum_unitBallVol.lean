-- Prove2me | Definitions.Def_RandLatEnum_unitBallVol
-- name    : RandLatEnum_unitBallVol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:51.30773+00:00
-- url     : https://prove2.me/theorems/22bce043-8322-467f-93b9-75d8eb060528
-- title:
--   Volume of the unit ball $V_d=\pi^{d/2}/\Gamma(1+d/2)$
-- statement:
--   The volume of the Euclidean unit ball in $\mathbb R^d$ is
--   $$
--   V_d=\frac{\pi^{d/2}}{\Gamma(1+d/2)} .
--   $$
--   It enters the Gaussian-heuristic radius $r_d$ and the primitive-vector density $\kappa_d$.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.2, (2.5), p.15

import Mathlib

namespace RandLatEnum

/-- The volume of the unit ball in `d` dimensions, `V_d = π^{d/2}/Γ(1 + d/2)` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.2, (2.5),
p.15). -/
noncomputable def unitBallVol (d : ℕ) : ℝ :=
  Real.pi ^ ((d : ℝ) / 2) / Real.Gamma (1 + (d : ℝ) / 2)

end RandLatEnum


