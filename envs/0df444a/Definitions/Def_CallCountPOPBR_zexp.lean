-- Prove2me | Definitions.Def_CallCountPOPBR_zexp
-- name    : CallCountPOPBR_zexp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:05:08.347781+00:00
-- url     : https://prove2.me/theorems/a8951bf6-da6b-4e81-a15d-40178997262e
-- title:
--   The top exponent $a_z=s(n+1)$
-- statement:
--   For a graph on $n$ vertices, the top exponent is $a_z=s(n+1)$ with $s=8n^2+4$.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), Section 2.1, p.5

import Definitions.Def_CallCountPOPBR_redS

set_option autoImplicit false

namespace CallCountPOPBR

/-- **The top exponent `a_z = s(n + 1)`** of the reduction. Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Section 2.1, p.5:
"a_z = s(n + 1)". -/
def zexp (n : ℕ) : ℕ := redS n * (n + 1)

end CallCountPOPBR


