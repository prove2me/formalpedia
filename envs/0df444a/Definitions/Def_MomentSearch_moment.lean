-- Prove2me | Definitions.Def_MomentSearch_moment
-- name    : MomentSearch_moment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:48.529703+00:00
-- url     : https://prove2.me/theorems/33bc5370-2d16-4d8f-a0d2-0388b023a7aa
-- title:
--   Moments $\mu_i(p)$ and the $k$-moment sketch $\sigma_k$
-- statement:
--   For a distribution $p$ on $[n]_0$, the **$i$-th moment** is
--
--   $$
--   \mu_i(p) := \sum_{t=0}^{n-1} p_t\, t^i ,
--   $$
--
--   and the **$k$-moment sketch** is $\sigma_k(p):=(\mu_0(p),\dots,\mu_k(p))$. On $\Delta_n$, $\mu_0(p)=1$.
--
--   The collection $\mathcal U_{\sigma_k}$ groups distributions with identical first $k$ moments; the paper's main negative result concerns its approximability factor.
--
--   **Formalization Note** The convention $0^0=1$ is used, so $\mu_0(p)=\sum_t p_t$, as in the paper. The sketch takes values in $\mathbb R^{k+1}$, indexed by $\{0,\dots,k\}$.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4, p.9 (PDF p.11)

import Mathlib

namespace MomentSearch

/-- The `i`-th moment of a distribution `p` on `[n]₀`, `µ_i(p) := ∑_{t=0}^{n−1} p_t t^i`
(Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4, p.9 (PDF p.11)).

**Formalization Note.** The target `t : Fin n` is read as the real number `t`, and
`0 ^ 0 = 1`, so `µ_0(p) = ∑_t p_t` (which is `1` on the simplex), as in the paper. -/
def moment {n : ℕ} (p : Fin n → ℝ) (i : ℕ) : ℝ :=
  ∑ t : Fin n, p t * ((t : ℕ) : ℝ) ^ i

/-- The `k`-moment sketch `σ_k(p) := (µ_0(p), …, µ_k(p))` (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4, p.9 (PDF p.11)).
The entry with index `i : Fin (k + 1)` is `µ_i(p)`. -/
def momentSketch (n k : ℕ) (p : Fin n → ℝ) : Fin (k + 1) → ℝ :=
  fun i => moment p (i : ℕ)

end MomentSearch


