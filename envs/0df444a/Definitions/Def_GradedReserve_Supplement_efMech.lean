-- Prove2me | Definitions.Def_GradedReserve_Supplement_efMech
-- name    : GradedReserve_Supplement_efMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:39:53.148469+00:00
-- url     : https://prove2.me/theorems/020bbaef-6367-4d67-9152-04e7bc81a1cc
-- title:
--   Entry-fee mechanism $\mathrm{EF}(e,r)$
-- statement:
--   The **entry-fee mechanism** $\mathrm{EF}(e,r)$ charges every bidder with a bid of at least $r$ (and positive) a fee $e\ge0$, and the highest such bidder also pays its bid and receives the item; ties among the highest entering bids go to the lowest index. Exit pays nothing.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 4 after Definition 4.1, p.9 (PDF 10); Theorem 4.2 part 1, p.9 (PDF 10)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_Mechanism
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

open Classical in
/-- The entry-fee mechanism `EF(e, r)` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 4 after Definition 4.1, p.9, PDF 10): every
bidder with a bid of at least `r` pays the fee `e ≥ 0`, and the highest such bidder also pays its
bid (and receives the item). A bidder enters when its bid is at least `r` and positive (Theorem
4.2 part 1: "`eP(Xᵢ ≥ r, Xᵢ > 0)`"); ties among the highest entering bids go to the lowest index
(Section 2, p.4: standard and loser-payment auctions break ties by the lowest index; Theorem 6.1).

**Formalization Note.** Actions outside `[0, 1]` are exit. -/
noncomputable def efMech (n : ℕ) (e r : ℝ) : Mechanism n where
  alloc x i :=
    if (x i ∈ Icc (0:ℝ) 1 ∧ r ≤ x i ∧ 0 < x i) ∧
        ∀ j, (x j ∈ Icc (0:ℝ) 1 ∧ r ≤ x j ∧ 0 < x j) → x j < x i ∨ (x j = x i ∧ i ≤ j) then 1
    else 0
  pay x i :=
    (if x i ∈ Icc (0:ℝ) 1 ∧ r ≤ x i ∧ 0 < x i then e else 0) +
    (if (x i ∈ Icc (0:ℝ) 1 ∧ r ≤ x i ∧ 0 < x i) ∧
        ∀ j, (x j ∈ Icc (0:ℝ) 1 ∧ r ≤ x j ∧ 0 < x j) → x j < x i ∨ (x j = x i ∧ i ≤ j) then x i
      else 0)

end GradedReserve.Supplement


