-- Prove2me | Definitions.Def_GradedReserve_rStar
-- name    : GradedReserve_rStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:54.7902+00:00
-- url     : https://prove2.me/theorems/a9741b1e-2a65-4a21-82be-b4ca22207d6a
-- title:
--   Crossing point $r^*=\inf\{v:\varphi(v)\ge0\}$
-- statement:
--   The crossing point of the virtual value,
--   $$r^*=\inf\{v:\varphi(v)\ge0\},$$
--   which is the root of $\varphi$ when $\varphi$ is continuous. For a regular law it is the optimal reserve.
--
--   **Formalization Note** The infimum is over $v\in(0,1]$, where $\varphi$ is defined; the set contains $v=1$, so it is nonempty.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5)

import Mathlib
import Definitions.Def_GradedReserve_virtualValue
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The crossing point `r* = inf{v : φ(v) ≥ 0}` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4, PDF 5).

**Formalization Note.** The infimum is over `v ∈ (0, 1]`, where `φ` is defined; the set contains
`1` (`φ(1) = 1`), so it is nonempty and bounded below, and no junk value `φ(0)` enters. -/
noncomputable def rStar (f : ℝ → ℝ) : ℝ := sInf {v ∈ Ioc (0:ℝ) 1 | 0 ≤ virtualValue f v}

end GradedReserve


