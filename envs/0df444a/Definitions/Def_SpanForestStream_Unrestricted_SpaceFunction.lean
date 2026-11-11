-- Prove2me | Definitions.Def_SpanForestStream_Unrestricted_SpaceFunction
-- name    : SpanForestStream_Unrestricted_SpaceFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:30:57.172674+00:00
-- url     : https://prove2.me/theorems/baa3d185-3405-40eb-813a-cd7ff2e597f5
-- title:
--   The space function f(v, δ) and the parameters A, t, τ₀
-- statement:
--   With binary logarithms,
--   $$f(v,\delta)=\min\Big\{v^2,\; v\log_2(v/\delta)\,\log_2^2\Big(2+\frac{v}{\log_2(v/\delta)}\Big)\Big\},$$
--   the space order of Theorems 1.1 and 1.2 (Eq. (1.1)). The auxiliary parameters are $A=\lceil\log_2(v+1)\rceil$, $t=1+\log_2(1/\delta)$ and $\tau_0=\lceil\log_2(64/\delta)\rceil$. For $v\ge 2$ and $0<\delta\le 1/4$ one has $v/\delta\ge 8$, so every logarithm here is positive.
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 3 (PDF 6), Eq. (1.1); p. 8 (PDF 11), §2; p. 21 (PDF 24), Proposition 3.6

import Mathlib

namespace SpanForestStream.Unrestricted

/-!
# The space function and the parameters `A`, `t`, `τ₀`

Chao, Cen, Ma, Wang, arXiv:2611.04365: Eq. (1.1), p. 3; §2, p. 8; Proposition 3.6, p. 21.
All logarithms are binary (App. A, p. 45).
-/

/-- `f(v, δ) = min{v², v log₂(v/δ) log₂²(2 + v / log₂(v/δ))}`, Eq. (1.1). -/
noncomputable def spaceFn (v : ℕ) (δ : ℝ) : ℝ :=
  min ((v : ℝ) ^ 2)
    ((v : ℝ) * Real.logb 2 (v / δ) * (Real.logb 2 (2 + v / Real.logb 2 (v / δ))) ^ 2)

/-- `A = ⌈log₂(v + 1)⌉`. -/
noncomputable def ceilLog (v : ℕ) : ℕ :=
  ⌈Real.logb 2 ((v : ℝ) + 1)⌉₊

/-- `t = 1 + log₂(1/δ)`. -/
noncomputable def confT (δ : ℝ) : ℝ :=
  1 + Real.logb 2 (1 / δ)

/-- `τ₀ = ⌈log₂(64/δ)⌉`. -/
noncomputable def tau0 (δ : ℝ) : ℕ :=
  ⌈Real.logb 2 (64 / δ)⌉₊

end SpanForestStream.Unrestricted


