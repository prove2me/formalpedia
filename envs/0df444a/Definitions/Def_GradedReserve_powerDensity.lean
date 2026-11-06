-- Prove2me | Definitions.Def_GradedReserve_powerDensity
-- name    : GradedReserve_powerDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:48.398241+00:00
-- url     : https://prove2.me/theorems/b7792a80-832d-4d8e-a575-9d69339e6646
-- title:
--   Power law $F(v)=v^k$ (density $kv^{k-1}$)
-- statement:
--   For a real $k\ge1$, the power law $F(v)=v^k$ on $[0,1]$, given by its density
--   $$f(v)=k\,v^{k-1},\qquad v\in[0,1],$$
--   and $f=0$ outside $[0,1]$. For $k=1$ it is the uniform law.
--
--   **Formalization Note** $k$ is real and $v^{k-1}$ is the real power function.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.1, p.5 (PDF 6)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The power law `F(v) = v^k` of Theorem 3.1 (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.1, p.5, PDF 6), given by its density
`f(v) = k v^{k−1}` on `[0, 1]` (and `0` elsewhere).

**Formalization Note.** `k` is real and the power is `Real.rpow` (at `v = 0`, `k = 1` it is
`0^0 = 1`, the uniform density). -/
noncomputable def powerDensity (k : ℝ) (v : ℝ) : ℝ :=
  if v ∈ Icc (0:ℝ) 1 then k * v ^ (k - 1) else 0

end GradedReserve


