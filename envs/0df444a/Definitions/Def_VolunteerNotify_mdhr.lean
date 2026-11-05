-- Prove2me | Definitions.Def_VolunteerNotify_mdhr
-- name    : VolunteerNotify_mdhr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:36:55.338084+00:00
-- url     : https://prove2.me/theorems/18c2899e-d890-4152-98c7-61ea929a01d3
-- title:
--   Definition 1 — CDF, discrete hazard rate and the minimum discrete hazard rate $q$
-- statement:
--   Let $g$ be a probability mass function on $\{1,2,\dots\}$ and $G(n)=\sum_{k\le n} g(k)$ its CDF. The **discrete hazard rate** at a period $\tau\ge 1$ is
--   $$
--   h(\tau)=\frac{g(\tau)}{1-G(\tau-1)},
--   $$
--   with the convention that $0/0=1$. The **minimum discrete hazard rate** (MDHR) of $g$ is
--   $$
--   q=\inf_{\tau\ge 1} h(\tau).
--   $$
--   It lies in $[0,1]$. It measures how fast an inactive volunteer becomes active again: the geometric law with parameter $q$ has MDHR $q$, and the point mass at $2$ has MDHR $0$.
--
--   **Formalization Note** The source writes a minimum, which need not be attained; the infimum agrees with it whenever it exists. The zero denominator is an explicit case because Lean's $x/0=0$ differs from the source's convention.
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Definition 1 and fn. 9, p.10

import Mathlib

namespace VolunteerNotify

/-- The CDF `G(n) = ∑_{k ≤ n} g(k)` of a mass function `g` on the natural numbers.
Manshadi–Rodilitz, *Online Policies for Efficient Volunteer Crowdsourcing*, arXiv:2002.08474v7,
Definition 1, p.10. -/
noncomputable def cdf (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), g k

/-- The discrete hazard rate `g(τ) / (1 − G(τ − 1))` at a period `τ ≥ 1`, with the convention
of arXiv:2002.08474v7, fn. 9, p.10: the fraction `0/0` equals `1`.

**Formalization Note.** Lean's `x / 0 = 0` is not the paper's convention, so the zero denominator
is an explicit `if`. For a probability law `1 − G(τ − 1) = 0` forces `g(τ) = 0`, so the `if`
branch is exactly the `0/0` case. Only `τ ≥ 1` is used, so `τ - 1` never truncates. -/
noncomputable def hazard (g : ℕ → ℝ) (τ : ℕ) : ℝ :=
  if 1 - cdf g (τ - 1) = 0 then 1 else g τ / (1 - cdf g (τ - 1))

/-- The **minimum discrete hazard rate** (MDHR) `q` of `g`, arXiv:2002.08474v7, Definition 1,
p.10: `q = min_{τ ∈ ℕ} g(τ) / (1 − G(τ − 1))`, where `ℕ = {1, 2, …}`.

**Formalization Note.** The printed `min` need not be attained, so this is an infimum, over
positive periods `τ + 1`. It agrees with the minimum whenever that exists. For a probability law
on `{1, 2, …}` the hazards lie in `[0, 1]`, so the real `⨅` is over a nonempty bounded family. -/
noncomputable def mdhr (g : ℕ → ℝ) : ℝ :=
  ⨅ τ : ℕ, hazard g (τ + 1)

end VolunteerNotify


