-- Prove2me | Definitions.Def_LindbladStructLearn_Fvec
-- name    : LindbladStructLearn_Fvec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:00:29.797033+00:00
-- url     : https://prove2.me/theorems/f9d0c700-5ca9-4390-a5f3-35897ba9b7c8
-- title:
--   Error vector $\mathcal F(x) = E(x)/t - E(\lambda)/t$
-- statement:
--   For the true parameter vector $\lambda$ and a time $t$, $\mathcal F(x) = \frac1t E(x) - \frac1t E(\lambda)$. Its first-order part is $A_k(x - \lambda)$, which is why the algorithm updates $x \leftarrow x - A_k^{-1}\widehat{\mathcal F}(x)$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eqs. (5.7)–(5.8), p.33

import Mathlib
import Definitions.Def_LindbladStructLearn_expVec

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The error vector (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eqs. (5.7)–(5.8), p.33): `F(x) = E(x)/t − E(λ)/t`, with `λ` the
true parameter vector. -/
def Fvec {n k : ℕ} (t : ℝ) (lam x : Idx n k → ℂ) : Idx n k → ℂ := fun a =>
  (expVec t x a - expVec t lam a) / (t : ℂ)

end LindbladStructLearn


