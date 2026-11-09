-- Prove2me | Definitions.Def_NondetConn_ndcc
-- name    : NondetConn_ndcc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:24:22.672743+00:00
-- url     : https://prove2.me/theorems/5b3a6f31-6996-436a-bc0f-c1fd1825f391
-- title:
--   Nondeterministic communication complexity $N(f)$
-- statement:
--   The **nondeterministic communication complexity** of a two-party function $f$ is
--   $$
--   N(f) = \lceil \log_2 C^1(f) \rceil ,
--   $$
--   where $C^1(f)$ is the least number of 1-monochromatic rectangles covering $f^{-1}(1)$. A nondeterministic protocol whose certificate has $c$ bits yields a cover by $2^c$ such rectangles, and conversely, so $N(f)$ does not depend on the number of rounds.
--
--   **Formalization Note** The paper calls $N(\cdot)$ standard without defining it; this is the standard rectangle-cover characterization (Kushilevitz–Nisan, *Communication Complexity*, Ch. 2). Conventions differ by at most an additive constant, which the paper's $\Theta(\cdot)$ absorbs.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §3 "Communication complexity", p.8 (PDF p.10)

import Mathlib
import Definitions.Def_NondetConn_coverNumber

namespace NondetConn

/-- **Nondeterministic communication complexity** `N(f)` (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac),
§3 "Communication complexity", p.8; the characterization used in the proof of Theorem 4.1,
p.10): `N(f) = ⌈log₂ C¹(f)⌉`, where `C¹(f)` is the 1-cover number of `f` (`coverNumber`).
A nondeterministic protocol with `c` bits of certificate yields a cover by `2^c` 1-rectangles
and conversely; the measure does not depend on the number of rounds.

**Formalization Note** The paper calls `N(·)` standard and does not define it; this is the
standard rectangle-cover characterization (Kushilevitz–Nisan, Ch. 2). `Nat.clog 2` rounds
`log₂` up; conventions differ by at most an additive constant, which a `Θ(·)` statement
absorbs. -/
noncomputable def ndcc {α β : Type*} (f : α → β → Prop) : ℕ :=
  Nat.clog 2 (coverNumber f)

end NondetConn


