-- Prove2me | Definitions.Def_SecondBestBT_gft
-- name    : SecondBestBT_gft
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:38.619465+00:00
-- url     : https://prove2.me/theorems/47982908-8cd6-4529-8306-f016e4b233cc
-- title:
--   Expected gains from trade $\mathrm{GFT}_{F_S,F_B}(x)$
-- statement:
--   The expected **gains from trade** of an allocation rule $x$ under independent priors $F_S,F_B$ are
--   $$
--   \mathrm{GFT}_{F_S,F_B}(x)=\int (b-s)\,x(s,b)\,dF_S(s)\,dF_B(b).
--   $$
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 2, p.4

import Mathlib

open MeasureTheory

namespace SecondBestBT

/-- The expected gains from trade of an allocation rule,
`GFT_{F_S,F_B}(x) = ∫ (b − s) x(s, b) dF_S(s) dF_B(b)` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held
version sha256 17184930…, Section 2, p.4).

**Formalization Note** `p = (s, b)`, seller first; the product measure encodes independence.
For mechanisms, integrability of the integrand is part of `WellDefined`. -/
noncomputable def gft (μS μB : Measure ℝ) (x : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, (p.2 - p.1) * x p ∂(μS.prod μB)

end SecondBestBT


