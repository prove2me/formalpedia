-- Prove2me | Definitions.Def_GradedReserve_Supplement_realizedRevenue
-- name    : GradedReserve_Supplement_realizedRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:33:22.148221+00:00
-- url     : https://prove2.me/theorems/436a3a7a-3403-490c-a4d5-181c98478f33
-- title:
--   Realized revenue $\sum_i p_i(x)$ at an action profile
-- statement:
--   The seller's revenue at a realized action profile $x$ is the sum of all payments,
--   $$\mathrm{Rev}(x)=\sum_{i=1}^n p_i(x).$$
--   For $\mathrm{LP}(d,\lambda)$ with $d>0$ this is display (8), $\mathrm{Rev}_\lambda(b)=\lambda\sum_i b_i\mathbf 1\{b_i\ge d\}+(1-\lambda)\,b_{(1)}\mathbf 1\{b_{(1)}\ge d\}$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), display (8), p.9 (PDF 10); Theorem 6.1 part 1, p.11 (PDF 12)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_Mechanism
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The seller's (expected) revenue at one realized action profile `x`: the sum of all bidders'
payments (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), display (8), p.9, PDF 10, and Theorem 6.1 part 1, p.11, PDF 12: "the seller's
revenue … in every realization"). For `LP(d, λ)` with `d > 0` this is display (8),
`Rev_λ(b) = λ Σᵢ bᵢ 1{bᵢ ≥ d} + (1 − λ) b₍₁₎ 1{b₍₁₎ ≥ d}`. -/
noncomputable def realizedRevenue {n : ℕ} (M : Mechanism n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, M.pay x i

end GradedReserve.Supplement


