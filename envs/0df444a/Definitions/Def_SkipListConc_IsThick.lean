-- Prove2me | Definitions.Def_SkipListConc_IsThick
-- name    : SkipListConc_IsThick
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:57.660402+00:00
-- url     : https://prove2.me/theorems/b7fa0748-e423-410b-b3db-ff41f94d5763
-- title:
--   $\beta$-thick distributions (Definition 3.1)
-- statement:
--   For $0<\beta\le 1$, a probability distribution $\mu=(\mu_\ell)_{\ell\ge1}$ on the positive integers is **$\beta$-thick** if
--   $$
--   \mu_\ell\ \ge\ \beta\,\mu_{\ell-1}\qquad\text{for every }\ell\ge 2 .
--   $$
--   Thickness says the distribution has no thin spot; summed over a tail it gives the hazard bound $\Pr[X\ge \ell+1\mid X\ge\ell]\ge\beta$.
--
--   **Formalization Note** A distribution on the positive integers is a sequence of nonnegative point masses $\mu:\mathbb N\to\mathbb R$ with $\mu_0=0$ and total mass $1$; the range $0<\beta\le1$ is part of the predicate.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 3.1, p.16

import Mathlib

namespace SkipListConc

/-- `β`-thick distributions (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists:
Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), Definition 3.1,
p.16): for `0 < β ≤ 1`, a probability distribution `μ = (μ_ℓ)_{ℓ ≥ 1}` on the positive integers
is `β`-thick if `μ_ℓ ≥ β μ_{ℓ−1}` for every `ℓ ≥ 2`.

**Formalization Note** A distribution on the positive integers is a sequence `μ : ℕ → ℝ` of
nonnegative point masses with `μ 0 = 0` summing to `1`. The range `0 < β ≤ 1` of the definition
is part of the predicate. -/
def IsThick (β : ℝ) (μ : ℕ → ℝ) : Prop :=
  0 < β ∧ β ≤ 1 ∧ (∀ ℓ, 0 ≤ μ ℓ) ∧ μ 0 = 0 ∧ HasSum μ 1 ∧
    ∀ ℓ : ℕ, 2 ≤ ℓ → β * μ (ℓ - 1) ≤ μ ℓ

end SkipListConc


