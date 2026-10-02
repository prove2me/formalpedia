-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_IsSeparableConvex
-- name    : DiscreteConvex_ConjugacyDualityD_IsSeparableConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:58:22.963246+00:00
-- url     : https://prove2.me/theorems/ebeead65-b161-4480-9056-1011f90ff84d
-- title:
--   IsSeparableConvex
-- statement:
--   $f$ is separable convex: $f(x)=\sum_v\psi_v(x(v))$ for univariate discrete-convex $\psi_v$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.234, adjacent to Theorem 8.49.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.234, adjacent to Theorem 8.49

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_DiscreteConvexUnivariate

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is separable convex: `f(x) = Σ_v ψ_v(x(v))` for univariate discrete-convex `ψ_v`. -/
def IsSeparableConvex (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ psi : V → ℤ → WithTop ℝ, (∀ v, DiscreteConvexUnivariate (psi v)) ∧
    ∀ x, f x = ∑ v, psi v (x v)

end DiscreteConvex.ConjugacyDualityD


