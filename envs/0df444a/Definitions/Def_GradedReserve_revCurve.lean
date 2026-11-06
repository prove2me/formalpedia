-- Prove2me | Definitions.Def_GradedReserve_revCurve
-- name    : GradedReserve_revCurve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:29.287571+00:00
-- url     : https://prove2.me/theorems/eb9f087d-8b2b-4933-b559-7d6ff039451e
-- title:
--   Reserve revenue curve $R_n(r)$, display (1)
-- statement:
--   For a reserve $r\in[0,1]$, the revenue of a standard auction with reserve $r$ in its symmetric equilibrium is
--   $$R_n(r)=n\int_r^1\varphi(v)\,Q(v)\,f(v)\,dv .$$
--
--   $R_n(0)$ is the revenue without reserve and $R^*=R_n(r^*)$ the optimal one; the guarantee of the mission is stated relative to $R^*$.
--
--   **Formalization Note** The integrand is written $\big(vf(v)-(1-F(v))\big)Q(v)$, which equals $\varphi Qf$ wherever $f>0$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5), display (1)

import Mathlib
import Definitions.Def_GradedReserve_valueCdf
import Definitions.Def_GradedReserve_oppCdf
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- Display (1) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4, PDF 5): the revenue of a standard auction with reserve `r`,
`R_n(r) = n ∫_r^1 φ(v) Q(v) f(v) dv`.

**Formalization Note.** The integrand is written `(v f(v) − (1 − F(v))) Q(v)`, which equals
`φ(v) Q(v) f(v)` wherever `f(v) > 0` (almost everywhere on `[0, 1]`), and avoids Lean's
`x / 0 = 0`. -/
noncomputable def revCurve (f : ℝ → ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  (n : ℝ) * ∫ v in r..1, (v * f v - (1 - valueCdf f v)) * oppCdf f n v

end GradedReserve


