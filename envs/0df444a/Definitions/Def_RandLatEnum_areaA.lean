-- Prove2me | Definitions.Def_RandLatEnum_areaA
-- name    : RandLatEnum_areaA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:11.730916+00:00
-- url     : https://prove2.me/theorems/5edc6490-5ee3-4def-ac67-8f71a45ebb65
-- title:
--   Area under a ceiling, $A(h)=\int_0^1 h(x)\,dx$
-- statement:
--   For a ceiling $h$ continuous on $[0,1]$,
--   $$
--   A(h)=\int_0^1 h(x)\,dx .
--   $$
--   By the area rule (Proposition 7.1), complete chains below the ceiling $n^{n h(k/n)}$ exist with vanishing probability when $A(h)<1/8$.
--
--   **Formalization Note** The interval integral over $[0,1]$.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §7.1, p.28

import Mathlib

namespace RandLatEnum

/-- The area under a ceiling, `A(h) = ∫_0^1 h(x) dx` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §7.1, p.28).

**Formalization Note.** The interval integral over `[0, 1]`; every use has `h` continuous on
`[0, 1]`, hence integrable there. -/
noncomputable def areaA (h : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, h x

end RandLatEnum


