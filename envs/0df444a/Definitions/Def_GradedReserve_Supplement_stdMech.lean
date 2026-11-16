-- Prove2me | Definitions.Def_GradedReserve_Supplement_stdMech
-- name    : GradedReserve_Supplement_stdMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:40:36.901488+00:00
-- url     : https://prove2.me/theorems/4e768b94-700c-49a1-941e-835d758dcaec
-- title:
--   Standard auction $S(\alpha,r)$
-- statement:
--   For $\alpha\in[0,1]$ and $r\in[0,1)$ the **standard auction** $S(\alpha,r)$ sells to the highest bidder if its bid is at least $r$ and breaks ties in favor of the lowest index. The winner pays
--   $$\alpha\,b_{(1)}+(1-\alpha)\max\{b_{(2)},r\},$$
--   where $b_{(1)}\ge b_{(2)}$ are the two highest bids. $\alpha=1$ and $\alpha=0$ give the first- and second-price auctions with reserve $r$. Exit never wins and does not count as a bid.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, "Mechanisms", p.4 (PDF 5)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_Mechanism
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

open Classical in
/-- The standard auction `S(α, r)` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, "Mechanisms", p.4, PDF 5): it sells to the
highest bidder if its bid is at least `r` and breaks ties in favor of the lowest index; the winner
pays `α b₍₁₎ + (1 − α) max{b₍₂₎, r}`, where `b₍₁₎ ≥ b₍₂₎` are the two highest bids. `α = 1` and
`α = 0` give the first- and second-price auctions with reserve `r`.

**Formalization Note.** Actions outside `[0, 1]` are exit. For the winner `i`,
`max{b₍₂₎, r}` is the maximum of `r` and the other bidders' bids in `[0, 1]` (a fold of `max`
starting from `r`; exits contribute `r`). -/
noncomputable def stdMech (n : ℕ) (α r : ℝ) : Mechanism n where
  alloc x i :=
    if (x i ∈ Icc (0:ℝ) 1 ∧ r ≤ x i) ∧
        ∀ j, x j ∈ Icc (0:ℝ) 1 → x j < x i ∨ (x j = x i ∧ i ≤ j) then 1
    else 0
  pay x i :=
    if (x i ∈ Icc (0:ℝ) 1 ∧ r ≤ x i) ∧
        ∀ j, x j ∈ Icc (0:ℝ) 1 → x j < x i ∨ (x j = x i ∧ i ≤ j) then
      α * x i + (1 - α) *
        (Finset.univ.erase i).fold max r (fun j => if x j ∈ Icc (0:ℝ) 1 then x j else r)
    else 0

end GradedReserve.Supplement


