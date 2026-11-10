-- Prove2me | Definitions.Def_MomentSearch_grid
-- name    : MomentSearch_grid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:58.732068+00:00
-- url     : https://prove2.me/theorems/f8a800ee-81f1-4e07-9b98-576738846b8c
-- title:
--   Scaled grid $\tau_t = 2t/(n-1)-1$
-- statement:
--   Let $x(t):=\frac{2t-(n-1)}{n-1}$ be the affine map sending $[0,n-1]$ onto $[-1,1]$. The **scaled grid** consists of the points
--
--   $$
--   \tau_t := x(t) = \frac{2t}{n-1}-1,\qquad t\in[n]_0,
--   $$
--
--   so $T=\{\tau_0,\dots,\tau_{n-1}\}=\{-1,-1+\tfrac{2}{n-1},\dots,1-\tfrac2{n-1},1\}$, with consecutive points at distance $2/(n-1)$. Moment conditions on $[n]_0$ are rewritten on this grid to compare with polynomials on $[-1,1]$.
--
--   **Formalization Note** Defined for every natural number $t$; all statements use it for $t\in[n]_0$ and assume $n\ge2$, the paper's standing assumption, so the division is by a positive number.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.1, Step 1, p.21 (PDF p.23); main text §4.1, Step 1, p.11 (PDF p.13)

import Mathlib

namespace MomentSearch

/-- The scaled grid `τ_t := x(t) = 2t/(n − 1) − 1` for `t ∈ [n]₀`, the image of `t` under the
affine map sending `[0, n − 1]` onto `[−1, 1]` (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.1, Step 1, p.21 (PDF p.23);
main text §4.1, Step 1, p.11 (PDF p.13)). The grid is `T = {τ_0, …, τ_{n−1}}`, with
`τ_0 = −1` and `τ_{n−1} = 1`.

**Formalization Note.** Defined for every natural number `t`; statements use it for
`t ∈ [n]₀` and always assume `n ≥ 2` (the paper's standing assumption), so that the division by
`n − 1` is by a positive real. -/
noncomputable def grid (n t : ℕ) : ℝ :=
  2 * (t : ℝ) / ((n : ℝ) - 1) - 1

end MomentSearch


