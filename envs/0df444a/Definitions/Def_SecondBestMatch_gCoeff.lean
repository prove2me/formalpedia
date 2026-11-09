-- Prove2me | Definitions.Def_SecondBestMatch_gCoeff
-- name    : SecondBestMatch_gCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:29.645217+00:00
-- url     : https://prove2.me/theorems/e79c0de2-f694-462e-900b-eb2c4802ee86
-- title:
--   Beta coefficient $g_\alpha$
-- statement:
--   For a multiplier $\alpha$, the **Beta coefficient** is
--   $$
--   g_\alpha := \frac{1+\alpha}{\mathrm B\big(\tfrac1{1+\alpha},\tfrac1{1+\alpha}\big)} .
--   $$
--   It is the fraction of first-best surplus that the edge-level Beta contraction retains in the fixed-$\alpha$ Lagrangian; $g_0 = 1$ and $g_\alpha\downarrow 1/2$ as $\alpha\to\infty$.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 4.2, p.14

import Mathlib
import Definitions.Def_SecondBestMatch_betaFn

open MeasureTheory Set

namespace SecondBestMatch

/-- The Beta coefficient `g_α := (1 + α) / B(1/(1+α), 1/(1+α))` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.2, p.14). -/
noncomputable def gCoeff (α : ℝ) : ℝ :=
  (1 + α) / betaFn (1 / (1 + α)) (1 / (1 + α))

end SecondBestMatch


