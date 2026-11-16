-- Prove2me | Definitions.Def_GradedReserve_Supplement_lpBid
-- name    : GradedReserve_Supplement_lpBid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:43:41.25091+00:00
-- url     : https://prove2.me/theorems/d2b9294c-bacb-4aa1-bc2a-10a6d3d37c14
-- title:
--   Equilibrium bid $\beta_\lambda=m_a/T_\lambda$ of $\mathrm{LP}(d_\lambda,\lambda)$
-- statement:
--   The bid function of Theorem 4.3 part 1:
--   $$\beta_\lambda(v)=\frac{m_a(v)}{T_\lambda(v)}\quad(v\ge a),$$
--   with exit below $a$.
--
--   **Formalization Note** Exit is the action $-1$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 4.3, p.9 (PDF 10); Lemma B.9, p.31 (PDF 32)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_lpT
import Definitions.Def_GradedReserve_Supplement_lpM
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The bid function `β_λ` of Theorem 4.3 part 1 (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 4.3, p.9, PDF 10; Lemma B.9,
p.31, PDF 32): `β_λ(v) = m_a(v) / T_λ(v)` for `v ≥ a`, with exit below `a`.

**Formalization Note.** Exit is encoded by the action `−1` (every negative action is exit). For
`v ≥ a > 0`, `T_λ(v) ≥ min{1, Q(a)} > 0`. -/
noncomputable def lpBid (f : ℝ → ℝ) (n : ℕ) (a lam v : ℝ) : ℝ :=
  if v < a then -1 else lpM f n a v / lpT f n lam v

end GradedReserve.Supplement


