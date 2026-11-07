-- Prove2me | Definitions.Def_QPACLarge_mN
-- name    : QPACLarge_mN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:29.040289+00:00
-- url     : https://prove2.me/theorems/afa7f088-f672-4a43-bfe7-69d1239d93c1
-- title:
--   Core length $m_n=2s(n)+3k\lceil\log_2 n\rceil+4$
-- statement:
--   With $s(n)$ from Eq. (9) and an integer $k \ge 1$, the core input length is
--   $$
--   m_n = 2s(n) + 3k\lceil\log_2 n\rceil + 4, \qquad M_n = 2^{m_n} = \frac{16 r_n^3}{\theta_n^2},\quad \theta_n = 2^{-s(n)} .
--   $$
--
--   **Formalization Note** $\lceil\log_2 n\rceil$ is `Nat.clog 2 n`.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 5.2, p.36

import Mathlib

namespace QPACLarge

/-- **The core input length `mₙ = 2s(n) + 3k⌈log₂ n⌉ + 4`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 5.2, p.36: "`mₙ ≜ 2s(n) + 3k⌈log₂ n⌉ + 4`, `Mₙ ≜ 2^{mₙ} = 16rₙ³/θₙ²`".

`mN k n s` with `s = s(n)`.

**Formalization Note.** `⌈log₂ n⌉` is `Nat.clog 2 n`. -/
def mN (k n s : ℕ) : ℕ := 2 * s + 3 * k * Nat.clog 2 n + 4

end QPACLarge


