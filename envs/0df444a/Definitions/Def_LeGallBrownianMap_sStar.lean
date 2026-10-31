-- Prove2me | Definitions.Def_LeGallBrownianMap_sStar
-- name    : LeGallBrownianMap_sStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:52.372853+00:00
-- url     : https://prove2.me/theorems/cf751652-7868-4a25-a9de-e1822ce5d6d9
-- title:
--   The minimizing time $s_*$ of the labels
-- statement:
--   For a continuous label path $Z$ on $[0,1]$, $s_*$ is a time at which $Z$ attains its minimum $-\Delta$. For Brownian labels on the CRT there is almost surely a unique such instant, $s_*\in(0,1)$, and $x_*=p(s_*)$ is the distinguished point of the Brownian map.
--
--   **Formalization Note** A minimizer chosen by choice (`0` if none exists); the a.s. uniqueness makes the choice immaterial.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.4, p.14

import Mathlib

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.4, p.14:
"It is known (see [19], Proposition 2.5) that there is an almost surely unique instant
s∗ ∈ (0, 1) such that Z_{s∗} = −∆."

`sStar Z` is a time at which the path `Z` attains its minimum.

**Formalization Note.** Chosen by `Classical.choose` among the minimizers when one exists (always,
for a continuous `Z` on `[0,1]`), and `0` otherwise. For the paper's labels the minimizer is a.s.
unique, so the choice is immaterial for almost every path. -/
noncomputable def sStar (Z : unitInterval → ℝ) : unitInterval := by
  classical
  exact if h : ∃ s, ∀ t, Z s ≤ Z t then h.choose else 0

end LeGallBrownianMap


