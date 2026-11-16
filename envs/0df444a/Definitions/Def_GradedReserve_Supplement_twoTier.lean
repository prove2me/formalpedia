-- Prove2me | Definitions.Def_GradedReserve_Supplement_twoTier
-- name    : GradedReserve_Supplement_twoTier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:45:57.106875+00:00
-- url     : https://prove2.me/theorems/f16a4ac1-c9fe-4ca7-8910-1da36a6b7382
-- title:
--   Two-tier graded reserve $\pi_{h,\rho,r'}$
-- statement:
--   Given $r$, $h>0$, $\rho\in[0,1]$ and an upper reserve $r'$, the two-tier rule accepts the highest bid $b$ with probability
--   $$\pi(b)=\begin{cases}0,& b<r-h,\\ \rho,& r-h\le b<r',\\ 1,& r'\le b\le1.\end{cases}$$
--   At $\rho=0$, $r'=r$ it is the hard reserve $\mathbf 1\{b\ge r\}$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.6, p.8 (PDF 9); proof p.16 (PDF 17)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The two-tier graded reserve of Theorem 3.6 (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.6, p.8, PDF 9; proof p.16, PDF 17):
"Accept the highest bid with probability `0` below `r − h`, with probability `ρ` on `[r − h, r′)`,
and with probability one on `[r′, 1]`". At `ρ = 0`, `r′ = r` it is the hard reserve `1{b ≥ r}`. -/
noncomputable def twoTier (r h ρ r' : ℝ) (b : ℝ) : ℝ :=
  if b < r - h then 0 else if b < r' then ρ else 1

end GradedReserve.Supplement


