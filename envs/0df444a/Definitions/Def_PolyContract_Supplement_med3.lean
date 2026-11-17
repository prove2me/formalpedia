-- Prove2me | Definitions.Def_PolyContract_Supplement_med3
-- name    : PolyContract_Supplement_med3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:59:04.607012+00:00
-- url     : https://prove2.me/theorems/1a963381-b135-4f5e-8b3b-5433c074f7b7
-- title:
--   Median of three numbers and clamp
-- statement:
--   For real numbers $a,b,c$, $\operatorname{med}(a,b,c)$ is the median of the three, and for $a\le a'$,
--   $$\operatorname{clamp}(v,a,a'):=\min(\max(v,a),a').$$
--
--   They describe the marginals of a one-element extension in Theorem B.12.
--
--   **Formalization Note** The median is written $\max(\min(a,b),\min(\max(a,b),c))$.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem B.12, p.35 (PDF p.36)

import Mathlib

set_option autoImplicit false

namespace PolyContract.Supplement

/-- `med(a, b, c)`, the median of three real numbers (Klimm, Lippke, Warode, arXiv:2611.04934,
version of November 3, 2026, sha256 18cfc0a5…, Theorem B.12(b), p.35). -/
def med3 (a b c : ℝ) : ℝ := max (min a b) (min (max a b) c)

/-- `clamp(v, a, a′) := min(max(v, a), a′)` (arXiv:2611.04934, Theorem B.12(c), p.35); the paper
uses it for `a ≤ a′`. -/
def clamp (v a a' : ℝ) : ℝ := min (max v a) a'

end PolyContract.Supplement


