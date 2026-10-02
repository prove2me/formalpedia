-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_SubDifferentialZ
-- name    : DiscreteConvex_ConjugacyDualityC_SubDifferentialZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:13.582905+00:00
-- url     : https://prove2.me/theorems/7841ba3c-4554-4341-a975-6e698ce03920
-- title:
--   SubDifferentialZ
-- statement:
--   The integer subdifferential $\partial_{\mathbb Z} f(x)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, Eq. (6.86).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.165, Eq. (6.86)

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The integer subdifferential `∂_Z f(x) ⊆ Zⱽ`. -/
def SubDifferentialZ (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) : Set (V → ℤ) :=
  {p : V → ℤ | ∀ y : V → ℤ,
    f y - f x ≥ (((∑ v, (p v : ℝ) * ((y v : ℝ) - (x v : ℝ))) : ℝ) : WithTop ℝ)}

end DiscreteConvex.ConjugacyDualityC


