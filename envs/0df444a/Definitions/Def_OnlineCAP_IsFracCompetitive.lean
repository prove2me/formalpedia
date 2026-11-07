-- Prove2me | Definitions.Def_OnlineCAP_IsFracCompetitive
-- name    : OnlineCAP_IsFracCompetitive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:04.329078+00:00
-- url     : https://prove2.me/theorems/b8312cf1-3496-47bd-97fd-12133cfcecca
-- title:
--   ρ-competitive online fractional algorithm
-- statement:
--   An online fractional algorithm $x$ is **$\rho$-competitive** on an instance if, for every valid request list $s$,
--
--   1. the current vector $x=x(s)$ covers every revealed request: $\sum_{e\in G\cap\mathrm{cov}(r)}x_e\ge1$ for every request $r$ of $s$;
--   2. its cost is at most $\rho$ times the offline fractional optimum:
--   $$\sum_{e\in G}c(e)\,x_e\le\rho\cdot\mathrm{OPT}_{\mathrm{frac}}(s).$$
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §2.2, p.10

import Mathlib
import Definitions.Def_OnlineCAP_OnlineHSInstance
import Definitions.Def_OnlineCAP_OnlineHSInstance_OPTfrac
import Definitions.Def_OnlineCAP_FracOnlineAlg

namespace OnlineCAP

/-- **ρ-competitive online fractional algorithm.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §2.2, p.10 (PDF p.10): "An online
fractional algorithm is α-competitive if it maintains a valid fractional solution xt whose total
cost is at most α times the cost of the optimal offline fractional solution."

On every valid request list `s`: the current vector `x = X.x s` covers every revealed request,
`∑_{e ∈ G ∩ cov r} x_e ≥ 1`, and its cost `∑_{e ∈ G} c(e) x_e` is at most `ρ · OPT_frac(s)`. -/
def IsFracCompetitive {U Req : Type} (I : OnlineHSInstance U Req) (X : FracOnlineAlg U Req)
    (ρ : ℝ) : Prop :=
  ∀ s, I.Valid s →
    (∀ r ∈ s, 1 ≤ I.mass (X.x s) r) ∧ ∑ e ∈ I.G, I.c e * X.x s e ≤ ρ * I.OPTfrac s

end OnlineCAP


