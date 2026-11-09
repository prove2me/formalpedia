-- Prove2me | Definitions.Def_DirTeleMC_rho
-- name    : DirTeleMC_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:07.535723+00:00
-- url     : https://prove2.me/theorems/898a3fee-26bf-4a26-b666-78e0c3e04203
-- title:
--   $\rho = \lceil k^{1/\ell} \rceil$
-- statement:
--   For natural numbers $k$ and $\ell \ge 1$,
--   $$\rho = \lceil k^{1/\ell} \rceil,$$
--   the least natural number $r$ with $k \le r^\ell$. It is the hub threshold of the height reduction (Lemma 4.2) and enters the load bound $\Lambda = \ell(\theta + \rho + 1)$ of Algorithm 2.
--
--   **Formalization Note** The least such $r$ is found among $0, \dots, k$; its equality with the real ceiling $\lceil k^{1/\ell}\rceil$ is checked in the sanity file for $(k,\ell) = (2,2), (8,3), (9,3)$.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Lemma 4.2, p.11 (PDF p.12); Algorithm 2, line 5, p.24 (PDF p.25)

import Mathlib

namespace DirTeleMC

/-- **`ρ = ⌈k^{1/ℓ}⌉`**, as the least natural number `r` with `k ≤ r^ℓ`.
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Lemma 4.2, p.11 ("let ρ = ⌈k^{1/ℓ}⌉"); Algorithm 2, line 5, p.24.

**Formalization Note.** For `ℓ ≥ 1` the least such `r` is at most `k`, so the search over `0, …, k` finds it, and
it equals `⌈k^{1/ℓ}⌉` (the real `ℓ`-th root rounded up), since `k ≤ r^ℓ ↔ k^{1/ℓ} ≤ r` for natural `r`
(`Solutions/verification/DirTeleMC_sanity.lean`). The value at `ℓ = 0` is not used. -/
def rho (k ℓ : ℕ) : ℕ := ((List.range (k + 1)).find? fun r => decide (k ≤ r ^ ℓ)).getD 0

end DirTeleMC


