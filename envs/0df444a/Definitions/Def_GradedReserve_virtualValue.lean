-- Prove2me | Definitions.Def_GradedReserve_virtualValue
-- name    : GradedReserve_virtualValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:42.865973+00:00
-- url     : https://prove2.me/theorems/b8177dab-9a24-4e28-b5df-9aef4c1161d6
-- title:
--   Virtual value $\varphi(v)=v-(1-F(v))/f(v)$
-- statement:
--   The (Myerson) virtual value of the value law is
--   $$\varphi(v)=v-\frac{1-F(v)}{f(v)} .$$
--
--   **Formalization Note** $\varphi$ is only read where $f>0$, i.e. on $(0,1)$, and at $v=1$, where $1-F(1)=0$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5)

import Mathlib
import Definitions.Def_GradedReserve_valueCdf
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The virtual value `φ(v) = v − (1 − F(v))/f(v)` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4, PDF 5).

**Formalization Note.** `φ` is read only where `f > 0` (on `(0, 1)`, and at `1` where
`1 − F(1) = 0`); Lean's `x / 0 = 0` at other points is never used. -/
noncomputable def virtualValue (f : ℝ → ℝ) (v : ℝ) : ℝ := v - (1 - valueCdf f v) / f v

end GradedReserve


