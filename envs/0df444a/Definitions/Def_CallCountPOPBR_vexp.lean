-- Prove2me | Definitions.Def_CallCountPOPBR_vexp
-- name    : CallCountPOPBR_vexp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:05:15.999089+00:00
-- url     : https://prove2.me/theorems/74db5feb-14db-40fa-8e18-884e40f6684b
-- title:
--   The vertex exponent $a_v=sv$
-- statement:
--   For a graph on $n$ vertices, vertex $v$ gets the exponent $a_v=sv$ with $s=8n^2+4$.
--
--   **Formalization Note** Vertices of the published `NPGraph.Graph` are $0,\dots,n-1$; vertex $v$ stands for the paper's vertex $v+1$. Accordingly vertex $v$ gets exponent $s(v+1)$, so the exponents are the paper's $s,2s,\dots,ns$.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), Section 2.1, p.5

import Definitions.Def_CallCountPOPBR_redS

set_option autoImplicit false

namespace CallCountPOPBR

/-- **The vertex exponent `a_v = sv`** of the reduction. Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Section 2.1, p.5:
"a_v = sv (v ∈ V)".

**Formalization Note.** Vertices are `0, …, n − 1` (the published `NPGraph.Graph`); vertex `v`
is the paper's vertex `v + 1`, so `vexp n v = s · (v + 1)`. Every vertex exponent is positive
and the exponents are exactly the paper's `s, 2s, …, ns`. -/
def vexp (n v : ℕ) : ℕ := redS n * (v + 1)

end CallCountPOPBR


