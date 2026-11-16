-- Prove2me | Definitions.Def_GradedReserve_Supplement_gradedMech
-- name    : GradedReserve_Supplement_gradedMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:38:50.213574+00:00
-- url     : https://prove2.me/theorems/ad206da6-f6c3-4233-bca5-7024eddde156
-- title:
--   Graded-reserve auction $G_\pi$ as a mechanism
-- statement:
--   The **graded-reserve auction** $G_\pi$ sells the item to the highest bidder with probability $\pi(b_{(1)})$ and charges the winner its bid; ties are broken uniformly at random. Thus a bidder whose bid $x_i\in[0,1]$ is not exceeded by any other bid receives the item with probability
--   $$\frac{\pi(x_i)}{\#\{j:\ x_j=x_i\}}$$
--   and pays $x_i$ when it does. Exit (an action outside $[0,1]$) never wins and is ignored in the ranking.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Definition 2.3, p.4 (PDF 5)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_Mechanism
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

open Classical in
/-- The graded-reserve auction `G_π` as a mechanism (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Definition 2.3, p.4, PDF 5): the highest
bidder receives the item with probability `π(b₍₁₎)` and pays its bid; ties among the highest bids
are broken uniformly at random. Bidder `i` with bid `x i ∈ [0, 1]` is among the highest bids when
no other bid exceeds it; it then receives the item with probability `π(x i) / #(ties)`, where the
count includes `i` itself, and pays `x i` when it receives it.

**Formalization Note.** Actions outside `[0, 1]` are exit: they never win, pay nothing and are
ignored in the ranking. -/
noncomputable def gradedMech (n : ℕ) (π : ℝ → ℝ) : Mechanism n where
  alloc x i :=
    if x i ∈ Icc (0:ℝ) 1 ∧ ∀ j, x j ∈ Icc (0:ℝ) 1 → x j ≤ x i then
      π (x i) / ((Finset.univ.filter fun j => x j = x i).card : ℝ)
    else 0
  pay x i :=
    if x i ∈ Icc (0:ℝ) 1 ∧ ∀ j, x j ∈ Icc (0:ℝ) 1 → x j ≤ x i then
      x i * (π (x i) / ((Finset.univ.filter fun j => x j = x i).card : ℝ))
    else 0

end GradedReserve.Supplement


