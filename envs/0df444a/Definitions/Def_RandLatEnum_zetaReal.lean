-- Prove2me | Definitions.Def_RandLatEnum_zetaReal
-- name    : RandLatEnum_zetaReal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:51.832504+00:00
-- url     : https://prove2.me/theorems/a1d7d43c-4bdd-4ca5-bef1-730ed37348fd
-- title:
--   Riemann zeta value $\zeta(d)$ as a real number
-- statement:
--   For an integer $d\ge2$,
--   $$
--   \zeta(d)=\sum_{k\ge1}k^{-d},
--   $$
--   the value of the Riemann zeta function, a real number greater than $1$. It appears in the densities of primitive vectors and sublattices of a Haar-random lattice.
--
--   **Formalization Note** The real part of Mathlib's `riemannZeta` at $d$; it is used only for $d\ge2$, where the value is real.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.2, p.15

import Mathlib

namespace RandLatEnum

/-- The Riemann zeta function at an integer `d`, `ζ(d)`, as a real number (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.2, p.15:
"let Γ and ζ denote the gamma and Riemann zeta functions").

**Formalization Note.** The real part of Mathlib's `riemannZeta` at `d`. It is used only for
`d ≥ 2`, where `ζ(d) = Σ_{k≥1} k^{−d}` is real and `> 1`. -/
noncomputable def zetaReal (d : ℕ) : ℝ :=
  (riemannZeta (d : ℂ)).re

end RandLatEnum


