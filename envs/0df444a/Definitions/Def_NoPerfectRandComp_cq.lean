-- Prove2me | Definitions.Def_NoPerfectRandComp_cq
-- name    : NoPerfectRandComp_cq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:09.548183+00:00
-- url     : https://prove2.me/theorems/fa7f1545-7e77-4cf3-8cbb-ada0d9492a37
-- title:
--   Number of cores $c_q = 100\lceil\log_2 q\rceil$
-- statement:
--   The number of cores of the outer function is
--   $$
--   c_q = 100\,\lceil \log_2 q\rceil .
--   $$
--   For $q = 2^s - 1$ with $s \ge 2$ this is $100s$.
--
--   **Formalization Note** $\lceil\log_2 q\rceil$ is `Nat.clog 2 q`.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Eq. (13), p.15, and Eq. (16), p.17

import Mathlib

namespace NoPerfectRandComp

/-- The number of cores `c_q = 100 ⌈log₂ q⌉` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), (13), p.15 and (16), p.17).

**Formalization Note** `⌈log₂ q⌉` is `Nat.clog 2 q`; for `q = 2ˢ − 1` with `s ≥ 2` it equals `s`. -/
def cq (q : ℕ) : ℕ := 100 * Nat.clog 2 q

end NoPerfectRandComp


