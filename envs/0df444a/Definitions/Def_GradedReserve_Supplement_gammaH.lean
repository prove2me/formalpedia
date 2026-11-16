-- Prove2me | Definitions.Def_GradedReserve_Supplement_gammaH
-- name    : GradedReserve_Supplement_gammaH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:46:25.111848+00:00
-- url     : https://prove2.me/theorems/172fb3f3-8b6b-40bc-8d18-0a655325b860
-- title:
--   $\Gamma(h)$ of Theorem 3.6
-- statement:
--   For $r\in(0,1)$ and $h>0$,
--   $$\Gamma(h)=n\int_{r-h}^r vQ(v)f(v)\,dv+nrQ(r)f(r)\,\frac{\int_{r-h}^rQ}{Q(r)}-\frac{r}{\varphi(r)}\,n\int_{r-h}^r\varphi Qf .$$
--
--   **Formalization Note** $\varphi Qf$ is written $(vf(v)-(1-F(v)))Q(v)$, which equals it wherever $f>0$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.6, p.8 (PDF 9); proof p.17 (PDF 18)

import Mathlib
import Definitions.Def_GradedReserve_valueCdf
import Definitions.Def_GradedReserve_oppCdf
import Definitions.Def_GradedReserve_virtualValue
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- `Γ(h)` of Theorem 3.6 (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.6, p.8, PDF 9; proof p.17, PDF 18):
`Γ(h) = n ∫_{r−h}^r v Q f + n r Q(r) f(r) (∫_{r−h}^r Q)/Q(r) − (r/φ(r)) n ∫_{r−h}^r φ Q f`.

**Formalization Note.** `φ Q f` is written `(v f(v) − (1 − F(v))) Q(v)`, as in the base mission's
`revCurve`; it equals `φQf` wherever `f > 0`. In Theorem 3.6, `0 < r < r*`, so `Q(r) > 0` and
`φ(r) < 0`, and neither division is Lean's `x / 0 = 0`. -/
noncomputable def gammaH (f : ℝ → ℝ) (n : ℕ) (r h : ℝ) : ℝ :=
  (n : ℝ) * (∫ v in (r - h)..r, v * oppCdf f n v * f v)
    + (n : ℝ) * r * oppCdf f n r * f r * (∫ v in (r - h)..r, oppCdf f n v) / oppCdf f n r
    - r / virtualValue f r *
      ((n : ℝ) * ∫ v in (r - h)..r, (v * f v - (1 - valueCdf f v)) * oppCdf f n v)

end GradedReserve.Supplement


