-- Prove2me | Definitions.Def_RandLatEnum_pD
-- name    : RandLatEnum_pD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:07.15048+00:00
-- url     : https://prove2.me/theorems/925682be-9e02-45bd-bc62-e8bd525511fa
-- title:
--   Reversed dual-HKZ profile $p_D(t)=p_H(1-t)=-\frac t2\ln t$
-- statement:
--   $$
--   p_D(t)=p_H(1-t)=-\frac t2\ln t\qquad(0\le t\le1),
--   $$
--   the reflection of the HKZ profile. It bounds the prefix profile of a basis obtained by reversing and dualizing an HKZ basis of the dual lattice (Eq. (4.5)).
--
--   **Formalization Note** Defined as $p_H(1-t)$. At $t=0$, $\ln0=0$ gives $p_D(0)=0$, the limit value.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §4.1, (4.5), p.19

import Mathlib
import Definitions.Def_RandLatEnum_pH

namespace RandLatEnum

/-- The reversed dual-HKZ prefix profile `p_D(t) = p_H(1 − t) = −(t/2) ln t` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §4.1, (4.5),
p.19).

**Formalization Note.** Defined as `p_H(1 − t)`; it unfolds to `−(t/2) ln t`. At `t = 0`
`Real.log 0 = 0` gives `p_D(0) = 0`, the limit value. -/
noncomputable def pD (t : ℝ) : ℝ :=
  pH (1 - t)

end RandLatEnum


