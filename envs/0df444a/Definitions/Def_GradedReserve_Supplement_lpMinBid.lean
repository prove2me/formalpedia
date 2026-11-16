-- Prove2me | Definitions.Def_GradedReserve_Supplement_lpMinBid
-- name    : GradedReserve_Supplement_lpMinBid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:42:57.5993+00:00
-- url     : https://prove2.me/theorems/b265407a-f078-47df-8c2a-d83dd5b8a21c
-- title:
--   Minimum bid $d_\lambda=aQ(a)/T_\lambda(a)$
-- statement:
--   For $a\in(0,1)$ and $\lambda\in[0,1]$, the minimum bid
--   $$d_\lambda=\frac{aQ(a)}{T_\lambda(a)}$$
--   makes $a$ the participation threshold of $\mathrm{LP}(d_\lambda,\lambda)$.
--
--   **Formalization Note** For $a\in(0,1)$, $Q(a)>0$ and so $T_\lambda(a)>0$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 4.3, p.9 (PDF 10)

import Mathlib
import Definitions.Def_GradedReserve_oppCdf
import Definitions.Def_GradedReserve_Supplement_lpT
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The minimum bid `d_λ = a Q(a) / T_λ(a)` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 4.3, p.9, PDF 10) that makes `a` the
participation threshold of `LP(d_λ, λ)`. The binder `lam` is the paper's `λ`.

**Formalization Note.** Used for `a ∈ (0, 1)`, where `Q(a) > 0` and so `T_λ(a) > 0`; Lean's
`x / 0 = 0` is never reached there. -/
noncomputable def lpMinBid (f : ℝ → ℝ) (n : ℕ) (a lam : ℝ) : ℝ :=
  a * oppCdf f n a / lpT f n lam a

end GradedReserve.Supplement


