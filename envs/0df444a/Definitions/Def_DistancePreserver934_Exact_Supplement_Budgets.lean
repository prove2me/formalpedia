-- Prove2me | Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets
-- name    : DistancePreserver934_Exact_Supplement_Budgets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:21:32.922272+00:00
-- url     : https://prove2.me/theorems/ae9589e4-cf33-4ad8-aa33-b6d406b24eb1
-- title:
--   Source-sensitive and sourcewise numerical budgets
-- statement:
--   For a nonnegative vertex count $n$, source count $\sigma$, demand count $p$, and integer level $k$, define the numerical expressions
--
--   $$F_k(n,\sigma,p)=n^{(8+8k)/(9+8k)}(p\sigma^k)^{4/(9+8k)},\qquad W_k(n,\sigma)=n^{(8+8k)/(5+8k)}\sigma^{4k/(5+8k)}.$$
--
--   These are real powers, with $k$ cast to a real number before division. They describe cost scales without asserting existence of any graph. The linear term $n$ is kept separately in the theorem statements.
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Theorem 37, printed pp. 32–33 (PDF pp. 33–34); Theorem 40, printed p. 34 (PDF p. 35)

import Mathlib

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

/-- The nonlinear source-sensitive term of Theorem 37, defined also at level zero. -/
noncomputable def F (k : ℕ) (n σ p : ℝ) : ℝ :=
  n ^ ((8 + 8 * (k : ℝ)) / (9 + 8 * (k : ℝ))) *
    (p * σ ^ k) ^ ((4 : ℝ) / (9 + 8 * (k : ℝ)))

/-- The nonlinear complete-sourcewise term of Theorem 40. -/
noncomputable def W (k : ℕ) (n σ : ℝ) : ℝ :=
  n ^ ((8 + 8 * (k : ℝ)) / (5 + 8 * (k : ℝ))) *
    σ ^ ((4 * (k : ℝ)) / (5 + 8 * (k : ℝ)))

end DistancePreserver934.Exact.Supplement


