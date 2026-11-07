-- Prove2me | Definitions.Def_LCPlanarSteiner_Dlog
-- name    : LCPlanarSteiner_Dlog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:02:19.929196+00:00
-- url     : https://prove2.me/theorems/b20cd50e-87b5-48be-8746-f8f491c3cf11
-- title:
--   $D_r = 1 + \lceil \log_2 r \rceil$
-- statement:
--   For a natural number $r$,
--   $$
--   D_r = 1 + \lceil \log_2 r \rceil \qquad (r \ge 1),
--   $$
--   so $D_1 = 1$, $D_2 = 2$, $D_3 = D_4 = 3$. It bounds the depth of a halving recursion on $r$ items. The same function gives $D$ (for $k$ terminals) in §3 and $D_q$ in Theorem 1.2.
--
--   **Formalization Note** Computed as $1 + \lceil \log_2 r\rceil$ with Mathlib's `Nat.clog 2 r`; the value at $r = 0$ is $1$.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §4, p.9; Theorem 1.2, p.2; §3, p.4 (logarithms have base two)

import Mathlib

namespace LCPlanarSteiner

/-- **`D_r = 1 + ⌈log₂ r⌉`.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §4, p.9: "Write D_r = 1 + ⌈log₂ r⌉ for
r ≥ 1"; Theorem 1.2, p.2: "Writing D_q = 1 + ⌈log₂ q⌉"; §3, p.4: "D = 1 + ⌈log₂ k⌉ … All logarithms
have base two."

`Dlog r = 1 + Nat.clog 2 r`, where `Nat.clog 2 r` is the least `c` with `r ≤ 2^c`, i.e.
`⌈log₂ r⌉` for `r ≥ 1`.

**Formalization Note.** `Dlog 1 = 1`, `Dlog 2 = 2`, `Dlog 3 = 3`, `Dlog 4 = 3` (checked in the
sanity file). For `r = 0` (an empty terminal set, "free", p.4) the value is `1`. -/
def Dlog (r : ℕ) : ℕ := 1 + Nat.clog 2 r

end LCPlanarSteiner


