-- Prove2me | Definitions.Def_GradedReserve_IsGradedReserve
-- name    : GradedReserve_IsGradedReserve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:50.572228+00:00
-- url     : https://prove2.me/theorems/2814913b-7894-425a-8116-8a921f6db379
-- title:
--   Graded reserve: non-decreasing $\pi:[0,1]\to[0,1]$
-- statement:
--   A **graded reserve** is a non-decreasing function $\pi:[0,1]\to[0,1]$. The graded-reserve auction $G_\pi$ collects sealed bids in $[0,1]$, sells the item to the highest bidder with probability $\pi(b_{(1)})$, where $b_{(1)}$ is the highest bid, and charges the winner its bid; ties are broken uniformly at random. Every bidder may also stay out and pay nothing.
--
--   The first-price auction with reserve $r$ is $G_\pi$ with $\pi=\mathbf 1\{b\ge r\}$.
--
--   **Formalization Note** $\pi$ is a function on $\mathbb R$ whose values matter only on $[0,1]$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Definition 2.3, p.4 (PDF 5)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- Definition 2.3 (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Definition 2.3, p.4, PDF 5): a graded reserve is a non-decreasing
`π : [0, 1] → [0, 1]`; the auction `G_π` sells to the highest bidder with probability `π(b₍₁₎)`.

**Formalization Note.** `π` is a function `ℝ → ℝ`; only its values on `[0, 1]` are constrained
and used (every bid lies in `[0, 1]`). -/
def IsGradedReserve (π : ℝ → ℝ) : Prop :=
  MonotoneOn π (Icc 0 1) ∧ ∀ b ∈ Icc (0:ℝ) 1, π b ∈ Icc (0:ℝ) 1

end GradedReserve


