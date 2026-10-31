-- Prove2me | Definitions.Def_LeGallBrownianMap_simpleGeodesicTime
-- name    : LeGallBrownianMap_simpleGeodesicTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:12.065591+00:00
-- url     : https://prove2.me/theorems/7e20e85d-3586-4e62-acfa-e28bb286ef66
-- title:
--   Times $\varphi_s(r)$ of the simple geodesics $\Gamma_s$
-- statement:
--   For a label path $Z$, $s\in[0,1]$ and $r\in[0,D(s,s_*)]$,
--
--   $$
--   \varphi_s(r)=\begin{cases}\inf\{t\in[s,1]:Z_t=Z_s-r\}, & \text{if } \min\{Z_t: t\in[s,1]\}\le Z_s-r,\\ \inf\{t\in[0,s]: Z_t=Z_s-r\}, &\text{otherwise.}\end{cases}
--   $$
--
--   The **simple geodesic** from $p(s)$ to $x_*$ is $\Gamma_s(r)=p(\varphi_s(r))$, $0\le r\le D(s,s_*)$.
--
--   **Formalization Note** The real infimum is mapped into $[0,1]$ by projection, which is the identity on $[0,1]$.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.6, pp.18–19

import Mathlib

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.6, p.18:
"Let s ∈ [0, 1]. For every r ∈ [0, D(s, s∗)], we set
ϕ_s(r) = inf{t ∈ [s, 1] : Z_t = Z_s − r}, if min{Z_t : t ∈ [s, 1]} ≤ Z_s − r,
ϕ_s(r) = inf{t ∈ [0, s] : Z_t = Z_s − r}, otherwise."
and p.19: "set Γ_s(r) = p(ϕ_s(r)). […] The geodesics of the form Γ_s are called simple
geodesics."

`simpleGeodesicTime Z s r = ϕ_s(r)`, the time in `[0,1]` whose image in `m∞` is the point at
distance `r` from `p(s)` on the simple geodesic `Γ_s`.

**Formalization Note.** The infima are real infima of subsets of `[0,1]`, mapped into
`unitInterval` by `Set.projIcc` (which is the identity on `[0,1]`). For a continuous `Z` and
`r ∈ [0, Z_s + ∆]` the relevant set is nonempty and closed, so the infimum is attained; the
minimum is written `sInf (Z '' [s,1])`. -/
noncomputable def simpleGeodesicTime (Z : unitInterval → ℝ) (s : unitInterval) (r : ℝ) :
    unitInterval := by
  classical
  exact Set.projIcc (0 : ℝ) 1 zero_le_one
    (if sInf (Z '' Set.Icc s 1) ≤ Z s - r then
      sInf {x : ℝ | ∃ t : unitInterval, (t : ℝ) = x ∧ s ≤ t ∧ Z t = Z s - r}
    else
      sInf {x : ℝ | ∃ t : unitInterval, (t : ℝ) = x ∧ t ≤ s ∧ Z t = Z s - r})

end LeGallBrownianMap


