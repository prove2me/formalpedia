-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_SubDifferentialR
-- name    : DiscreteConvex_ConjugacyDualityC_SubDifferentialR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:19.910089+00:00
-- url     : https://prove2.me/theorems/a2f986a9-a764-4ed3-884d-79b44219d593
-- title:
--   SubDifferentialR
-- statement:
--   The real subdifferential $\partial_{\mathbb R} f(x)$ of an integer-domain function at an integer point.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, cf. Eq. (3.23).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, cf. Eq. (3.23)

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The real subdifferential `∂_R f(x) ⊆ Rⱽ` of an integer-domain function at an integer
point. -/
def SubDifferentialR (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) : Set (V → ℝ) :=
  {p : V → ℝ | ∀ y : V → ℤ, f y - f x ≥ (((∑ v, p v * ((y v : ℝ) - (x v : ℝ))) : ℝ) : WithTop ℝ)}

end DiscreteConvex.ConjugacyDualityC


