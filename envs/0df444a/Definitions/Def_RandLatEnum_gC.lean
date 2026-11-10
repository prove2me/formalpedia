-- Prove2me | Definitions.Def_RandLatEnum_gC
-- name    : RandLatEnum_gC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:21.481499+00:00
-- url     : https://prove2.me/theorems/e90422fa-6b21-463d-af7a-7e155555462e
-- title:
--   The ceiling $g_c(x)=\frac{u_c(x)}2\bigl(1-\ln\frac{u_c(x)}{2c}\bigr)$
-- statement:
--   For $c>0$,
--   $$
--   g_c(x)=\frac{u_c(x)}{2}\left(1-\ln\frac{u_c(x)}{2c}\right),\qquad u_c(x)=\min\{x,1-x,2c\}.
--   $$
--   On the plateau $[2c,1-2c]$ it equals $c$; on the flanks it is the curve produced by reducing the outer blocks of a basis by reversed dual-HKZ (left) and HKZ (right). It is the ceiling to which the area rule is applied in the proof of Theorem 1.5.
--
--   **Formalization Note** At $x=0$ and $x=1$, $u_c=0$ and $\ln0=0$ give $g_c=0$, the continuous value.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), proof of Theorem 1.5, (7.5), p.29

import Mathlib
import Definitions.Def_RandLatEnum_uC

namespace RandLatEnum

/-- The ceiling `g_c(x) = (u_c(x)/2)(1 − ln(u_c(x)/(2c)))` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), proof of Theorem 1.5, (7.5),
p.29): height `c` on the plateau `[2c, 1 − 2c]` and the curved HKZ / reversed dual-HKZ flanks
outside it.

**Formalization Note.** At `x = 0` and `x = 1`, `u_c = 0` and `Real.log 0 = 0` give `g_c = 0`, the
continuous value. -/
noncomputable def gC (c x : ℝ) : ℝ :=
  uC c x / 2 * (1 - Real.log (uC c x / (2 * c)))

end RandLatEnum


