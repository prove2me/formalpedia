-- Prove2me | Definitions.Def_CallCountPOPBR_redS
-- name    : CallCountPOPBR_redS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:22.41473+00:00
-- url     : https://prove2.me/theorems/15af52e8-bb92-49c0-9ff7-035caea13953
-- title:
--   The exponent spacing $s=8n^2+4$
-- statement:
--   For a graph on $n$ vertices, the reduction spaces the vertex exponents $s=8n^2+4$ apart.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), Section 2.1, p.5

import Mathlib

set_option autoImplicit false

namespace CallCountPOPBR

/-- **The exponent spacing `s = 8n² + 4`** of the reduction. Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Section 2.1, p.5:
"s = 8n² + 4". -/
def redS (n : ℕ) : ℕ := 8 * n ^ 2 + 4

end CallCountPOPBR


