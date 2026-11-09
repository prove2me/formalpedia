-- Prove2me | Definitions.Def_NondetConn_S
-- name    : NondetConn_S
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:28:56.269393+00:00
-- url     : https://prove2.me/theorems/3bdf776d-6cb4-4d18-92c4-64e10df534b6
-- title:
--   $S_n$, the log-size of the largest 1-monochromatic rectangle
-- statement:
--   For $N = 2n$, define
--   $$
--   S_n = \max_{\mathcal A\times\mathcal B \subseteq \mathsf{bConn}_N^{-1}(1)} \log_2 |\mathcal A \times \mathcal B| = \log_2 \mathrm{maxRect}(n).
--   $$
--   Logarithms are base 2 throughout the paper. The proof of Theorem 4.1 bounds $S_n$ through the recurrence of Lemma 4.3 and then counts rectangles.
--
--   **Formalization Note** $S_n$ is a real number; $\mathrm{maxRect}(n) \ge 1$, so the logarithm is never applied to $0$.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), proof of Theorem 4.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_NondetConn_maxRect

namespace NondetConn

/-- **`S_n`**, the log-size of the largest 1-monochromatic rectangle (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac),
proof of Theorem 4.1, p.9):
`S_n = max_{𝒜 × ℬ ⊆ bConn_N⁻¹(1)} log |𝒜 × ℬ|`, with `N = 2n` and logarithms base 2 (p.8).

**Formalization Note** `S n = log₂ (maxRect n)` as a real number; `maxRect n ≥ 1`, so the
logarithm is never taken of `0`. -/
noncomputable def S (n : ℕ) : ℝ :=
  Real.logb 2 (maxRect n)

end NondetConn


