-- Prove2me | Definitions.Def_MomentSearch_SolvesCorrection
-- name    : MomentSearch_SolvesCorrection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:08:47.290203+00:00
-- url     : https://prove2.me/theorems/8df4e93b-49fd-47f9-9ee3-c701082d375f
-- title:
--   Signed-correction system (7)
-- statement:
--   Fix peak positions $m,m_0\in[n]_0$ and a degree bound $k$. A vector $a\in\mathbb R^n$ **solves the signed-correction system** if
--
--   $$
--   \sum_{t=0}^{n-1} a_t\,\tau_t^i = \tau_m^i-\tau_{m_0}^i\qquad\text{for all } i=0,\dots,k.
--   $$
--
--   Equivalently, $a+\delta_{m_0}-\delta_m$ has vanishing moments of orders $0,\dots,k$ on the grid: adding $a$ to the point mass at $m_0$ produces a signed vector with the same first $k$ moments as the point mass at $m$.
--
--   **Formalization Note** $\tau_t$ is the scaled grid; the system is the paper's (7), identical to the main text's (3).
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.1, eq. (7), p.21 (PDF p.23); = eq. (3), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_MomentSearch_grid

namespace MomentSearch

/-- `a ∈ ℝ^n` solves the signed-correction system for the peak positions `m, m₀ ∈ [n]₀`
(Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.1, eq. (7), p.21 (PDF p.23); = eq. (3), p.11 (PDF p.13)):
`∑_{t=0}^{n−1} a_t τ_t^i = τ_m^i − τ_{m₀}^i` for all `i = 0, …, k`.

**Formalization Note.** `τ_t` is `grid n t`; the vector `a` is indexed by `Fin n` and the peak
positions are natural numbers (in uses they are elements of `Fin n`). -/
def SolvesCorrection (n k m m₀ : ℕ) (a : Fin n → ℝ) : Prop :=
  ∀ i : ℕ, i ≤ k → ∑ t : Fin n, a t * grid n (t : ℕ) ^ i = grid n m ^ i - grid n m₀ ^ i

end MomentSearch


