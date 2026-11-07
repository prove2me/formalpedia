-- Prove2me | Definitions.Def_OnlineCAP_OnlineHSInstance_OPTfrac
-- name    : OnlineCAP_OnlineHSInstance_OPTfrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:27.142491+00:00
-- url     : https://prove2.me/theorems/9d3d5f7f-bc4e-400a-93a0-5054aca79f2e
-- title:
--   Offline fractional optimum
-- statement:
--   For an instance with ground set $G$, costs $c$ and a request list $s$, write $y(r)=\sum_{e\in G\cap\mathrm{cov}(r)}y_e$ for the fractional mass of a request. The **offline fractional optimum** is the value of the covering linear program of §2.2,
--
--   $$\mathrm{OPT}_{\mathrm{frac}}(s)=\inf\Big\{\sum_{e\in G}c(e)\,y_e\;:\;y\ge0,\ y(r)\ge1\text{ for every request } r\text{ of } s\Big\}.$$
--
--   It is at most $\mathrm{OPT}(s)$, since indicator vectors of feasible sets are fractional covers.
--
--   **Formalization Note** A real infimum; for a valid list the feasible set is nonempty ($y\equiv1$) and for nonnegative costs it is bounded below by $0$.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §2.2, p.10

import Mathlib
import Definitions.Def_OnlineCAP_OnlineHSInstance

namespace OnlineCAP

/-- **Fractional mass of a request.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §2.2, p.10: the left side `∑_{e ∈ R} x_e` of the
covering constraint, summed over the ground set: `I.mass y r = ∑_{e ∈ G ∩ cov r} y(e)`. -/
noncomputable def OnlineHSInstance.mass {U Req : Type} (I : OnlineHSInstance U Req)
    (y : U → ℝ) (r : Req) : ℝ :=
  ∑ e ∈ I.G, (I.cov r).indicator y e

/-- **The offline fractional optimum.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §2.2, p.10 (PDF p.10): the online covering LP
"minimize ∑_{e∈U} c(e) x_e subject to ∑_{e∈R_{t′}} x_e ≥ 1 ∀ t′ ≤ t, x_e ≥ 0", solved offline
("the optimal offline fractional solution").

`I.OPTfrac s` is the infimum of `∑_{e ∈ G} c(e) y(e)` over `y ≥ 0` with `∑_{e ∈ G ∩ cov r} y(e) ≥ 1`
for every request `r` of `s`.

**Formalization Note.** A real infimum (`sInf`). For a valid list the set is nonempty (`y = 1`),
and for nonnegative costs it is bounded below by `0`, so the value is the LP optimum. -/
noncomputable def OnlineHSInstance.OPTfrac {U Req : Type} (I : OnlineHSInstance U Req)
    (s : List Req) : ℝ :=
  sInf ((fun y : U → ℝ => ∑ e ∈ I.G, I.c e * y e) ''
    {y : U → ℝ | (∀ e, 0 ≤ y e) ∧ ∀ r ∈ s, 1 ≤ I.mass y r})

end OnlineCAP


