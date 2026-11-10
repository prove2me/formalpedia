-- Prove2me | Definitions.Def_RandLatEnum_maxPrefixLogDet
-- name    : RandLatEnum_maxPrefixLogDet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:07.623866+00:00
-- url     : https://prove2.me/theorems/c7faa3af-8568-4340-a963-d253e3a3dd32
-- title:
--   Largest prefix log-determinant $\max_{0\le k\le m}P_k(B)$
-- statement:
--   For an ordered basis $B=(b_1,\dots,b_m)$, the **largest prefix log-determinant** is
--   $$
--   \max_{0\le k\le m}P_k(B).
--   $$
--   It is at least $P_0(B)=0$. By Proposition 3.1 it determines $\ln T(B)$ up to $O(n)$ for a Haar-random lattice, and the goal of the mission is a lower bound on it uniform over all bases.
--
--   **Formalization Note** A maximum over the finite nonempty range $0,\dots,m$ (`Finset.sup'`).
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Proposition 3.1, (3.3), p.17; (7.6), p.29

import Mathlib
import Definitions.Def_RandLatEnum_prefixLogDet

namespace RandLatEnum

/-- The largest prefix log-determinant `max_{0 ≤ k ≤ m} P_k(B)` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Proposition 3.1, (3.3),
p.17, and (7.6), p.29).

**Formalization Note.** A maximum over the finite nonempty range `0, …, m` (`Finset.sup'`), so it
is attained; it is `≥ P_0 = 0`. -/
noncomputable def maxPrefixLogDet {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) : ℝ :=
  (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one (prefixLogDet b)

end RandLatEnum


