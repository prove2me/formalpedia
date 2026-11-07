-- Prove2me | Definitions.Def_CallCountPOPBR_wt
-- name    : CallCountPOPBR_wt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:19.201877+00:00
-- url     : https://prove2.me/theorems/1bffb5de-1b0c-43bf-af49-096b9a96f845
-- title:
--   Binary weight $\mathrm{wt}(x)$
-- statement:
--   For a natural number $x$, $\mathrm{wt}(x)$ is the number of ones in the binary expansion of $x$ (the sum of its base-2 digits).
--
--   It measures how many powers of two a free value of the reduction is built from (Claims 1–2).
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), proof of Theorem 2.8, p.6

import Mathlib

set_option autoImplicit false

namespace CallCountPOPBR

/-- **Binary weight** (proof of Theorem 2.8). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), proof of Theorem 2.8, p.6: "Write wt(x)
for the number of ones in the binary expansion of x".

`wt x` is the sum of the base-2 digits of `x`. -/
def wt (x : ℕ) : ℕ := (Nat.digits 2 x).sum

end CallCountPOPBR


