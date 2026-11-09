-- Prove2me | Definitions.Def_SecondBestMatch_betaExpect
-- name    : SecondBestMatch_betaExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:36.595276+00:00
-- url     : https://prove2.me/theorems/efb548d5-3e1a-45ed-b019-c1158ab16a48
-- title:
--   Expectation under $\mathrm{Beta}(a,b)$
-- statement:
--   For $Z\sim\mathrm{Beta}(a,b)$, the law on $(0,1)$ with density $f_{a,b}(z) = z^{a-1}(1-z)^{b-1}/\mathrm B(a,b)$, and a function $h$,
--   $$
--   \mathbb E_Z[h(Z)] = \int_0^1 h(z)\,\frac{z^{a-1}(1-z)^{b-1}}{\mathrm B(a,b)}\,dz .
--   $$
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 4.2, p.14

import Mathlib
import Definitions.Def_SecondBestMatch_betaFn

open MeasureTheory Set

namespace SecondBestMatch

/-- The expectation `E_Z[h(Z)]` for `Z ∼ Beta(a, b)`, the law on `(0, 1)` with density
`z^{a−1}(1 − z)^{b−1} / B(a, b)` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.2, p.14). -/
noncomputable def betaExpect (a b : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..1, h z * (z ^ (a - 1) * (1 - z) ^ (b - 1) / betaFn a b)

end SecondBestMatch


