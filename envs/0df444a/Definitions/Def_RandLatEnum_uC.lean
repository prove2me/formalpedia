-- Prove2me | Definitions.Def_RandLatEnum_uC
-- name    : RandLatEnum_uC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:19.450193+00:00
-- url     : https://prove2.me/theorems/586c9067-4036-4372-98f3-9dbd5d48596a
-- title:
--   $u_c(x)=\min\{x,1-x,2c\}$
-- statement:
--   For a parameter $c$,
--   $$
--   u_c(x)=\min\{x,\,1-x,\,2c\}.
--   $$
--   It is the distance to the nearer endpoint of $[0,1]$, capped at $2c$, and is the argument of the ceiling $g_c$ of (7.5).
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), proof of Theorem 1.5, (7.5), p.29

import Mathlib

namespace RandLatEnum

/-- `u_c(x) = min{x, 1 − x, 2c}` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), proof of Theorem 1.5, (7.5), p.29). -/
noncomputable def uC (c x : ℝ) : ℝ :=
  min (min x (1 - x)) (2 * c)

end RandLatEnum


