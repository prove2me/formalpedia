-- Prove2me | Definitions.Def_SecondBestMatch_betaFn
-- name    : SecondBestMatch_betaFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:39.795399+00:00
-- url     : https://prove2.me/theorems/93217ae9-2730-4b45-8a73-549a6643f1f9
-- title:
--   Beta function $\mathrm B(a,b)$
-- statement:
--   The **Beta function** is
--   $$
--   \mathrm B(a,b) := \int_0^1 z^{a-1}(1-z)^{b-1}\,dz ,
--   $$
--   with real powers.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 4.2, p.14

import Mathlib

open MeasureTheory Set

namespace SecondBestMatch

/-- The Beta function `B(a, b) := ∫₀¹ z^{a−1} (1 − z)^{b−1} dz` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.2, p.14), with real
powers. -/
noncomputable def betaFn (a b : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..1, z ^ (a - 1) * (1 - z) ^ (b - 1)

end SecondBestMatch


