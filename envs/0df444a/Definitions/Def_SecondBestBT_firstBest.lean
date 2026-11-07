-- Prove2me | Definitions.Def_SecondBestBT_firstBest
-- name    : SecondBestBT_firstBest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:37.35012+00:00
-- url     : https://prove2.me/theorems/f37171c2-2396-438f-afd1-d3580565a4e5
-- title:
--   First-best gains from trade $\mathrm{FB}_{F_S,F_B}$
-- statement:
--   The first-best allocation trades whenever $b>s$. Its gains from trade are
--   $$
--   \mathrm{FB}_{F_S,F_B}=\int (b-s)^+\,dF_S(s)\,dF_B(b).
--   $$
--   Since the integrand is nonnegative, "$\mathrm{FB}<\infty$" means that $(b-s)^+$ is integrable for $F_S\otimes F_B$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 2, p.4

import Mathlib

open MeasureTheory

namespace SecondBestBT

/-- The first-best gains from trade `FB_{F_S,F_B} = ∫ (b − s)⁺ dF_S(s) dF_B(b)`, achieved by trading
whenever `b > s` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Section 2,
p.4).

**Formalization Note** The integrand `max (b − s) 0` is nonnegative, so "FB < ∞" is exactly its
integrability, which every theorem that needs it states as a hypothesis. -/
noncomputable def firstBest (μS μB : Measure ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, max (p.2 - p.1) 0 ∂(μS.prod μB)

end SecondBestBT


