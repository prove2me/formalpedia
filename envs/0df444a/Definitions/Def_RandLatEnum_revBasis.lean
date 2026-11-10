-- Prove2me | Definitions.Def_RandLatEnum_revBasis
-- name    : RandLatEnum_revBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:24.077595+00:00
-- url     : https://prove2.me/theorems/6d79b05a-fa5d-4055-bd5b-e43d825c4e11
-- title:
--   Reversed basis $(b_m,\dots,b_1)$
-- statement:
--   The **reversal** of an ordered basis $(b_1,\dots,b_m)$ is $(b_m,\dots,b_1)$. Reversing and dualizing an HKZ basis of the dual lattice gives a basis of the original lattice whose prefix profile is the reflected HKZ profile (Eq. (4.5)).
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §4.1, p.19

import Mathlib

namespace RandLatEnum

/-- The reversed basis `(b_m, …, b_1)` of `(b_1, …, b_m)` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §4.1, p.19, "Reversing and
dualizing an HKZ basis of the dual lattice"). -/
def revBasis {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) : Fin m → EuclideanSpace ℝ (Fin k) :=
  fun i => b (Fin.rev i)

end RandLatEnum


