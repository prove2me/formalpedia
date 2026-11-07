-- Prove2me | Definitions.Def_BeatingGV42_numPlaces
-- name    : BeatingGV42_numPlaces
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:58.434807+00:00
-- url     : https://prove2.me/theorems/a864ad47-abbc-44be-907d-127ff23160e2
-- title:
--   Number of places of degree $r$, $B_r(F)$
-- statement:
--   For a function field $F/\mathbb F_Q$ and $r\ge 1$, $B_r(F)$ is the **number of places of $F$ of degree $r$**; $N(F)=B_1(F)$ is the number of rational places, which is the length of the Goppa codes built from all of them.
--
--   **Formalization Note** `Nat.card {v : Place k F // v.deg = r}` with the platform's places and degrees. There are finitely many places of each degree over a finite field, so the junk value $0$ of an infinite `Nat.card` does not occur.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §3, pp.10–11 (PDF pp.12–13), and §4.3, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace BeatingGV42

/-- **Number of places of degree `r`**, `B_r(F)` (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §3, pp.10–11 (PDF pp.12–13), and §4.3,
p.17 (PDF p.19)). `N(F) = B_1(F)` is the number of rational places.

**Formalization Note** `Nat.card {v : Place k F // v.deg = r}`, with the platform's `Place` and
`Place.deg = [κ(v) : k]`. For a function field over a finite field there are finitely many places of
each degree, so the junk value `0` of an infinite `Nat.card` does not occur. -/
noncomputable def numPlaces (k F : Type*) [Field k] [Field F] [Algebra k F] (r : ℕ) : ℕ :=
  Nat.card {v : Place k F // v.deg = r}

end BeatingGV42


