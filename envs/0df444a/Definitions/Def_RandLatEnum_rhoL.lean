-- Prove2me | Definitions.Def_RandLatEnum_rhoL
-- name    : RandLatEnum_rhoL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:19.86181+00:00
-- url     : https://prove2.me/theorems/b8e80298-2357-433a-bb74-e50ecc3d2682
-- title:
--   Gaussian mass $\rho(L)=\sum_{v\in L}e^{-\pi\|v\|^2}$
-- statement:
--   For a set $S$ of vectors (a lattice, its dual, a projected lattice), the **Gaussian mass** is
--   $$
--   \rho(S)=\sum_{v\in S}e^{-\pi\|v\|^2},
--   $$
--   the zero vector included. For a lattice $L$ it satisfies Poisson summation $\rho(L)=\rho(L^*)/\det L$ and Siegel's mean value $\mathbb E_{\mu_n}[\rho(L)]=2$ (Eq. (2.10)), which give the upper bound on the level counts in Proposition 3.1.
--
--   **Formalization Note** An unconditional sum of nonnegative terms in $[0,\infty]$, so it never takes a junk value; it is finite for a lattice.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.3, (2.10), p.16

import Mathlib

namespace RandLatEnum

open scoped ENNReal

/-- The Gaussian mass `ρ(L) = Σ_{v ∈ L} e^{−π‖v‖²}` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.3, (2.10), p.16), for a set of
vectors (a lattice, its dual, a projected lattice).

**Formalization Note.** An unconditional sum of nonnegative terms in `ℝ≥0∞`, so it never takes a
junk value; for a lattice it is finite. The zero vector is included. -/
noncomputable def rhoL {k : ℕ} (S : Set (EuclideanSpace ℝ (Fin k))) : ℝ≥0∞ :=
  ∑' v : S, ENNReal.ofReal (Real.exp (-Real.pi * ‖(v : EuclideanSpace ℝ (Fin k))‖ ^ 2))

end RandLatEnum


