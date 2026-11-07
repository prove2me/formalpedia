-- Prove2me | Definitions.Def_QPACLarge_rN
-- name    : QPACLarge_rN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:25.842891+00:00
-- url     : https://prove2.me/theorems/760cd113-d69e-46f1-ad46-e30c7aede941
-- title:
--   Parameter $r_n=2^{k\lceil\log_2 n\rceil}$
-- statement:
--   For an integer $k \ge 1$, $r_n = 2^{k\lceil \log_2 n\rceil}$, a power of two with $n^k \le r_n \le (2n)^k$.
--
--   **Formalization Note** $\lceil\log_2 n\rceil$ is `Nat.clog 2 n`, the least $e$ with $n \le 2^e$.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 5, p.33

import Mathlib

namespace QPACLarge

/-- **The parameter `rₙ = 2^{k⌈log₂ n⌉}`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 5, p.33: "`rₙ ≜ 2^{k⌈log₂ n⌉}`, so that `nᵏ ≤ rₙ = n^{O(1)}`" (`k` an integer).

**Formalization Note.** `⌈log₂ n⌉` is Mathlib's `Nat.clog 2 n` (the least `e` with `n ≤ 2^e`). -/
def rN (k n : ℕ) : ℕ := 2 ^ (k * Nat.clog 2 n)

end QPACLarge


