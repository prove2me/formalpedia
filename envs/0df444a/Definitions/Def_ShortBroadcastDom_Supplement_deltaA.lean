-- Prove2me | Definitions.Def_ShortBroadcastDom_Supplement_deltaA
-- name    : ShortBroadcastDom_Supplement_deltaA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:38:51.463846+00:00
-- url     : https://prove2.me/theorems/18409b2f-e0a1-4d33-912d-cf781ee6b033
-- title:
--   The slack constant $\delta_a$ of Theorem B
-- statement:
--   For a rational $a\ge1$ put $\theta=2a-\lfloor 2a\rfloor$. The slack constant of Theorem B is
--
--   $$
--   \delta_a=\frac{1}{2a(2a+1)^2}\quad\text{if }2a\in\mathbb Z,\qquad
--   \delta_a=\min\Bigl\{\frac{1-\theta}{a(a+1)},\ \frac{\theta}{\lfloor 2a\rfloor+1}\Bigr\}\quad\text{otherwise.}
--   $$
--
--   For example $\delta_1=1/18$ and $\delta_{5/4}=1/6$. It is the slack that threshold rounding achieves after the transformation of Theorem B.
--
--   **Formalization Note** $\theta$ is `Int.fract (2a)`, and "$2a$ is an integer" is `Int.fract (2a) = 0`.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §1.1, p.2 (PDF p.5), Theorem B

import Mathlib

namespace ShortBroadcastDom.Supplement

open Classical in
/-- **The slack constant `δ_a` of Theorem B.** For `a ≥ 1` with `θ = 2a − ⌊2a⌋`,
`δ_a = 1 / (2a(2a + 1)²)` if `2a` is an integer, and
`δ_a = min{(1 − θ)/(a(a + 1)), θ/(⌊2a⌋ + 1)}` otherwise.

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), Theorem B, §1.1, p.2 (PDF 5): "threshold rounding has slack at least
δa = 1/(2a(2a + 1)²) if 2a is an integer, δa = min{(1 − θ)/(a(a + 1)), θ/(⌊2a⌋ + 1)} otherwise,
where θ = 2a − ⌊2a⌋."

**Formalization Note** `θ = Int.fract (2a) = 2a − ⌊2a⌋`, and "`2a` is an integer" is
`Int.fract (2a) = 0`. Hand check: `a = 1` gives `1/18` (`= 1/(d b²)` with `d = 2`, `b = 3`, as in
the proof on p.48); `a = 5/4` gives `θ = 1/2` and `min{(1/2)/(45/16), (1/2)/3} = 1/6`. -/
noncomputable def deltaA (a : ℝ) : ℝ :=
  if Int.fract (2 * a) = 0 then 1 / (2 * a * (2 * a + 1) ^ 2)
  else min ((1 - Int.fract (2 * a)) / (a * (a + 1))) (Int.fract (2 * a) / ((⌊2 * a⌋ : ℝ) + 1))

end ShortBroadcastDom.Supplement


