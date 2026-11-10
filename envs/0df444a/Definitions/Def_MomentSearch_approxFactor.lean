-- Prove2me | Definitions.Def_MomentSearch_approxFactor
-- name    : MomentSearch_approxFactor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:11:20.83107+00:00
-- url     : https://prove2.me/theorems/01c387a1-1249-4384-a02b-c9ad80c31c8c
-- title:
--   Approximability factor $\alpha(\mathcal U)$ of an uncertainty collection
-- statement:
--   Let $\Delta_n$ be the simplex of probability distributions on $[n]_0$, and let $\mathcal U$ be a collection of sets of distributions (an **uncertainty collection**). The **approximability factor** of $\mathcal U$ is
--
--   $$
--   \alpha(\mathcal U) := \sup_{U\in\mathcal U}\ \inf_S\ \sup_{p\in U} \frac{\mathrm{cost}_p(S)}{\mathrm{OPT}(p)},
--   $$
--
--   where $S$ ranges over correct deterministic search strategies. A searcher told only which uncertainty set $U$ contains the true distribution chooses a strategy; the adversary then picks the worst distribution in $U$; $\alpha(\mathcal U)$ is the worst case of the resulting competitive ratio over all uncertainty sets.
--
--   **Formalization Note** The value lies in the extended nonnegative reals $[0,\infty]$: each ratio enters through $\mathrm{ofReal}$, and the suprema and the infimum are taken there, so no default value of a real supremum of an unbounded set can occur. The quantifier order is the paper's (set, then strategy, then distribution). For $n\ge2$ and distributions in $\Delta_n$ the ratios are nonnegative and finite, since $\mathrm{OPT}(p)\ge1$.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.2, eq. (1), p.5 (PDF p.7)

import Mathlib
import Definitions.Def_MomentSearch_OPT

open scoped ENNReal

namespace MomentSearch

/-- The approximability factor of an uncertainty collection `𝒰` of sets of distributions on
`[n]₀` (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.2, eq. (1), p.5 (PDF p.7)):
`α(𝒰) := sup_{U∈𝒰} inf_S sup_{p∈U} cost_p(S)/OPT(p)`,
where `S` ranges over correct deterministic search strategies.

**Formalization Note.** The value is taken in `ℝ≥0∞` (each ratio enters through
`ENNReal.ofReal`), so the outer suprema may be `∞` and no junk value of a real `sSup` on an
unbounded set arises. The quantifier order is the paper's: the uncertainty set `U` first, then
the strategy `S` (chosen knowing only `U`), then the distribution `p ∈ U`. The ratios are
nonnegative for `p` in the simplex, so `ENNReal.ofReal` changes no value; for `n ≥ 2` and `p` in
the simplex `OPT p ≥ 1`, so no ratio divides by zero. -/
noncomputable def approxFactor {n : ℕ} (𝒰 : Set (Set (Fin n → ℝ))) : ℝ≥0∞ :=
  ⨆ U ∈ 𝒰, ⨅ S : Strategy n, ⨆ p ∈ U, ENNReal.ofReal (cost p S / OPT p)

end MomentSearch


