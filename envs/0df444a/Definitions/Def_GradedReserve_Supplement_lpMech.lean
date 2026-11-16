-- Prove2me | Definitions.Def_GradedReserve_Supplement_lpMech
-- name    : GradedReserve_Supplement_lpMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:39:20.783479+00:00
-- url     : https://prove2.me/theorems/5fac971e-85e3-4205-9e96-9251bb57441e
-- title:
--   Loser-payment mechanism $\mathrm{LP}(d,\lambda)$ (Definition 4.1)
-- statement:
--   For $d\in(0,1]$ and $\lambda\in[0,1]$, $\mathrm{LP}(d,\lambda)$ treats a bid $b_i$ as **valid** if $b_i\ge d$ and $b_i>0$; the highest valid bid wins and pays its bid, every other valid bidder pays $\lambda b_i$, invalid bids and exit pay nothing, and ties go to the lowest index. $\mathrm{LP}(d,0)$ is the first-price auction with reserve $d$ and $\mathrm{LP}(d,1)$ the all-pay auction with minimum bid $d$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Definition 4.1, p.9 (PDF 10)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_Mechanism
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

open Classical in
/-- Definition 4.1, the loser-payment mechanism `LP(d, λ)` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Definition 4.1, p.9, PDF 10): a
bid `bᵢ` is valid if `bᵢ ≥ d` and `bᵢ > 0`; the highest valid bid wins and pays its bid, every
other valid bidder pays `λ bᵢ`, invalid bids pay nothing, and ties go to the lowest index.
`LP(d, 0)` is the first-price auction with reserve `d` and `LP(d, 1)` the all-pay auction with
minimum bid `d`.

**Formalization Note.** Actions outside `[0, 1]` are exit (invalid). Bidder `i` wins when its bid
is valid and every other valid bid is strictly lower or equal with a higher index; the
allocation is `1` for the winner and `0` otherwise. The binder `lam` is the paper's `λ`. -/
noncomputable def lpMech (n : ℕ) (d lam : ℝ) : Mechanism n where
  alloc x i :=
    if (x i ∈ Icc (0:ℝ) 1 ∧ d ≤ x i ∧ 0 < x i) ∧
        ∀ j, (x j ∈ Icc (0:ℝ) 1 ∧ d ≤ x j ∧ 0 < x j) → x j < x i ∨ (x j = x i ∧ i ≤ j) then 1
    else 0
  pay x i :=
    if (x i ∈ Icc (0:ℝ) 1 ∧ d ≤ x i ∧ 0 < x i) ∧
        ∀ j, (x j ∈ Icc (0:ℝ) 1 ∧ d ≤ x j ∧ 0 < x j) → x j < x i ∨ (x j = x i ∧ i ≤ j) then x i
    else if x i ∈ Icc (0:ℝ) 1 ∧ d ≤ x i ∧ 0 < x i then lam * x i
    else 0

end GradedReserve.Supplement


