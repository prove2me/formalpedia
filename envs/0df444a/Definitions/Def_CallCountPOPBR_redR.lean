-- Prove2me | Definitions.Def_CallCountPOPBR_redR
-- name    : CallCountPOPBR_redR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:23.735289+00:00
-- url     : https://prove2.me/theorems/865c059c-d576-4a89-8fe5-e809b32c3103
-- title:
--   The window radius $R=4n^2$
-- statement:
--   For a graph on $n$ vertices, the reduction's window radius is $R=4n^2$.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), Section 2.1, p.5

import Mathlib

set_option autoImplicit false

namespace CallCountPOPBR

/-- **The window radius `R = 4n²`** of the reduction. Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Section 2.1, p.5: "Put
R = 4n²". -/
def redR (n : ℕ) : ℕ := 4 * n ^ 2

end CallCountPOPBR


