-- Prove2me | Definitions.Def_MetricMatchingDistortion_Supplement_optCost
-- name    : MetricMatchingDistortion_Supplement_optCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:01:42.34135+00:00
-- url     : https://prove2.me/theorems/ddf47cfe-1c98-40bf-beae-9d2c3ecf42cd
-- title:
--   Optimal cost $\mathrm{OPT}=\min_{M^*}\mathrm{cost}(M^*,d)$ over perfect integral matchings
-- statement:
--   For an instance with $n$ agents and $n$ items and a distance function $d$ on agents and items, the **optimal cost** is
--   $$\mathrm{OPT}(d)=\min_{\pi}\ \mathrm{cost}(\pi,d)=\min_{\pi}\sum_{a}d(a,\pi(a)),$$
--   the minimum over all perfect integral matchings $\pi$ (bijections from agents to items).
--
--   It is the denominator of the distortion $\mathrm{distortion}(M,\sigma)=\sup_{d\in\rho(\sigma)}\mathbb E[\mathrm{cost}(M,d)]/\mathrm{OPT}(d)$ and is used to state the paper's distortion lower bounds.
--
--   **Formalization Note** The minimum is taken over the finite, nonempty set of permutations of `Fin n`, so it is attained.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), §2, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_matchingCost

namespace MetricMatchingDistortion.Supplement

open MetricMatchingDistortion

/-- **The optimal cost `min_{M∗} cost(M∗, d)`.** Charikar et al., *Sublinear Metric Distortion for
Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), §2, p.10 (PDF p.12): "The distortion
of a perfect integral matching M with respect to a metric d is the ratio of that matching's cost
compared to that of the optimal (integral) matching M∗: distortion(M, d) := cost(M, d) /
min_{M∗} cost(M∗, d)."

`optCost d` is the minimum of `matchingCost π d` over all perfect integral matchings
`π : Equiv.Perm (Fin n)`.

**Formalization Note.** The minimum is a `Finset.inf'` over the finite, nonempty set of
permutations (the identity is always one), so it is attained and no junk value arises. It is used
to state the paper's distortion lower bounds, written as `0 < optCost d` together with
`L · optCost d ≤ E[cost]`. -/
noncomputable def optCost {n : ℕ} (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).inf' Finset.univ_nonempty
    fun π => matchingCost π d

end MetricMatchingDistortion.Supplement


