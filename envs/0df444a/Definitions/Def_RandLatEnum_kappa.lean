-- Prove2me | Definitions.Def_RandLatEnum_kappa
-- name    : RandLatEnum_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:08.978449+00:00
-- url     : https://prove2.me/theorems/21c1a130-f643-4aa4-839f-0445c6f0c31d
-- title:
--   Primitive-pair density $\kappa_d=V_d/(2\zeta(d))$
-- statement:
--   For $d\ge2$,
--   $$
--   \kappa_d=\frac{V_d}{2\zeta(d)} .
--   $$
--   By Siegel's primitive-vector mean, $\kappa_d R^d$ is the expected number of primitive pairs $\{\pm v\}$ of length at most $R$ in a Haar-random unimodular rank-$d$ lattice.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.2, (2.5), p.15

import Mathlib
import Definitions.Def_RandLatEnum_unitBallVol
import Definitions.Def_RandLatEnum_zetaReal

namespace RandLatEnum

/-- The constant `κ_d = V_d/(2ζ(d))` (`d ≥ 2`) (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.2, (2.5), p.15): the density of
primitive pairs `{±v}` of a Haar-random unimodular rank-`d` lattice. -/
noncomputable def kappa (d : ℕ) : ℝ :=
  unitBallVol d / (2 * zetaReal d)

end RandLatEnum


