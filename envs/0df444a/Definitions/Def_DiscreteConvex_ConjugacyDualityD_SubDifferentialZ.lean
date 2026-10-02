-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_SubDifferentialZ
-- name    : DiscreteConvex_ConjugacyDualityD_SubDifferentialZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:56:11.148737+00:00
-- url     : https://prove2.me/theorems/5cbe6bae-1cb2-439d-9be0-10463454c329
-- title:
--   SubDifferentialZ
-- statement:
--   The integer subdifferential $\partial_{\mathbb Z} f(x)\subseteq\mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, Eq. (6.86), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, Eq. (6.86), redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The integer subdifferential `∂_Z f(x) ⊆ Zⱽ`. -/
def SubDifferentialZ (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) : Set (V → ℤ) :=
  {p : V → ℤ | ∀ y : V → ℤ,
    f y - f x ≥ (((∑ v, (p v : ℝ) * ((y v : ℝ) - (x v : ℝ))) : ℝ) : WithTop ℝ)}

end DiscreteConvex.ConjugacyDualityD


