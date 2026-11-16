-- Prove2me | Definitions.Def_GradedReserve_Supplement_spReserveMech
-- name    : GradedReserve_Supplement_spReserveMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:41:05.103569+00:00
-- url     : https://prove2.me/theorems/345a7c37-3044-47f6-8cbf-fd0aa7035860
-- title:
--   Second-price auction with bidder-specific reserves applied before ranking
-- statement:
--   Given reserves $r_1,\dots,r_n$, bidder $i$ **qualifies** when its bid is at least $r_i$. The highest qualified bid wins (ties to the lowest index) and pays its critical price, the maximum of its own reserve and the competing qualified bids:
--   $$\max\{r_i,\ \max\{b_j:\ j\ne i,\ b_j\ge r_j\}\}.$$
--   Without reserves, $r_i=0$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 6.1, p.11 (PDF 12); proof p.33 (PDF 34); Section D, p.35 (PDF 36)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_Mechanism
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

open Classical in
/-- The second-price auction with bidder-specific reserves `rᵢ` applied before ranking (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission),
Theorem 6.1, p.11, PDF 12; proof p.33, PDF 34; Section D, p.35, PDF 36): bidder `i` qualifies when
its bid is at least its reserve `rᵢ`; the highest qualified bid wins (ties to the lowest index,
Theorem 6.1) and pays the maximum of its own reserve and the competing qualified bids, its critical
price `max{rᵢ, Y}`. Without reserves, `rᵢ = 0`.

**Formalization Note.** Actions outside `[0, 1]` are exit (never qualified). -/
noncomputable def spReserveMech (n : ℕ) (rr : Fin n → ℝ) : Mechanism n where
  alloc x i :=
    if (x i ∈ Icc (0:ℝ) 1 ∧ rr i ≤ x i) ∧
        ∀ j, (x j ∈ Icc (0:ℝ) 1 ∧ rr j ≤ x j) → x j < x i ∨ (x j = x i ∧ i ≤ j) then 1
    else 0
  pay x i :=
    if (x i ∈ Icc (0:ℝ) 1 ∧ rr i ≤ x i) ∧
        ∀ j, (x j ∈ Icc (0:ℝ) 1 ∧ rr j ≤ x j) → x j < x i ∨ (x j = x i ∧ i ≤ j) then
      (Finset.univ.erase i).fold max (rr i)
        (fun j => if x j ∈ Icc (0:ℝ) 1 ∧ rr j ≤ x j then x j else rr i)
    else 0

end GradedReserve.Supplement


