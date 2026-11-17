-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqF
-- name    : GrothendieckLB_Supplement_cqF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:38:39.060584+00:00
-- url     : https://prove2.me/theorems/39b8cece-0ec0-4662-b601-5b79d860b6c8
-- title:
--   Cubic–quintic partition $f(w,x)=\mathrm{sgn}(w+\vartheta\,\mathrm{He}_3(x))$
-- statement:
--   For real parameters $\eta,s_3,s_5$, set $V=1+s_3^2+s_5^2$ and $\vartheta=\eta/\sqrt V$. The partition $f:\mathbb R^2\to\{-1,1\}$ of the cubic–quintic scheme is
--   $$
--   f(w,x)=\mathrm{sgn}\bigl(w+\vartheta\,\mathrm{He}_3(x)\bigr),\qquad \mathrm{He}_3(x)=\frac{x^3-3x}{\sqrt6} .
--   $$
--   Together with the other partition and the correlation maps $\rho(t)$ and $t$ it forms the two-dimensional cubic–quintic limiting scheme (Definition 4.1).
--
--   **Formalization Note** $\mathrm{sgn}$ takes values in $\{-1,1\}$ with $\mathrm{sgn}\,0=1$; the threshold curve is a null set, so this convention does not affect any expectation.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 4.1, (12), p.24

import Mathlib
import Definitions.Def_GrothendieckLB_he

namespace GrothendieckLB

namespace Supplement

/-- The partition `f` of the cubic–quintic limiting scheme (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 4.1, (12), p.24):
`f(w, x) = sgn(w + ϑ He₃(x))`, with `ϑ = η/√V`, `V = 1 + s₃² + s₅²` and
`He₃(x) = (x³ − 3x)/√6` the orthonormal cubic Hermite polynomial.

**Formalization Note** `sgn` takes values in `{−1, 1}`, with `sgn 0 = 1`; the threshold set
`{w + ϑ He₃(x) = 0}` is a null set, so the convention does not affect any Gaussian
expectation. `He₃` is the base mission's `GrothendieckLB.he 3`. The parameters `(η, s₃, s₅)` are
free reals; the paper's are (10). -/
noncomputable def cqF (η s₃ s₅ : ℝ) (w x : ℝ) : ℝ :=
  if 0 ≤ w + η / Real.sqrt (1 + s₃ ^ 2 + s₅ ^ 2) * he 3 x then 1 else -1

end Supplement

end GrothendieckLB


