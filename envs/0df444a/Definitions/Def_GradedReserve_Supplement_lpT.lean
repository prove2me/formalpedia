-- Prove2me | Definitions.Def_GradedReserve_Supplement_lpT
-- name    : GradedReserve_Supplement_lpT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:41:46.914612+00:00
-- url     : https://prove2.me/theorems/c16a6f49-2d72-4bb5-89e9-416d4229ba4d
-- title:
--   $T_\lambda(v)=\lambda+(1-\lambda)Q(v)$
-- statement:
--   For $\lambda\in[0,1]$,
--   $$T_\lambda(v)=\lambda+(1-\lambda)Q(v),\qquad Q=F^{n-1}.$$
--   It is the expected payment per unit of bid of a valid bid in $\mathrm{LP}(d,\lambda)$ that wins with probability $Q(v)$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 4.3, p.9 (PDF 10); Lemma B.9, p.31 (PDF 32)

import Mathlib
import Definitions.Def_GradedReserve_oppCdf
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- `T_λ(v) = λ + (1 − λ) Q(v)` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 4.3, p.9, PDF 10; Lemma B.9, p.31, PDF 32), the
expected payment per unit of bid of a valid bid that wins with probability `Q(v)` in `LP(d, λ)`.
The binder `lam` is the paper's `λ`. -/
noncomputable def lpT (f : ℝ → ℝ) (n : ℕ) (lam v : ℝ) : ℝ :=
  lam + (1 - lam) * oppCdf f n v

end GradedReserve.Supplement


