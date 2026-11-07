-- Prove2me | Definitions.Def_NoPerfectRandComp_sbias
-- name    : NoPerfectRandComp_sbias
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:14.50222+00:00
-- url     : https://prove2.me/theorems/e1ce9610-88ef-43ad-83a7-dfaa0e231056
-- title:
--   Signed bias $\mathrm{sbias}(A,x)=(-1)^{f(x)}(1-2\Pr[A(x)=1])$
-- statement:
--   For an algorithm $A$ intended to compute $f$ and $x \in \mathrm{Dom}(f)$, the **signed bias** is
--   $$
--   \mathrm{sbias}(A,x) = (-1)^{f(x)}\big(1 - 2\Pr[A(x)=1]\big) = 1 - 2\,\mathrm{err}(A,x),
--   $$
--   positive exactly when $A$ leans towards the truth at $x$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.4, pp.5–6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_PartialFn

namespace NoPerfectRandComp

/-- The signed bias of an algorithm `A` for `f` at `x` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.4, p.5):
`sbias(A, x) = (−1)^{f(x)} (1 − 2 Pr[A(x) = 1]) = 1 − 2 err(A, x)`, positive exactly when `A`
leans towards the truth at `x`. Meaningful for `x ∈ Dom(f)`. -/
noncomputable def sbias {ι : Type} (A : QAlgorithms.RandDecisionTree ι Bool Bool)
    (f : PartialFn ι) (x : ι → Bool) : ℝ :=
  (if f.val x then -1 else 1) * (1 - 2 * QAlgorithms.successProb A x true)

end NoPerfectRandComp


