-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_TRF
-- name    : DiscreteConvex_AlgorithmsC_TRF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:18:21.939449+00:00
-- url     : https://prove2.me/theorems/100dec80-cee7-452f-b25c-f871965acb67
-- title:
--   TRF
-- statement:
--   Axiom (TRF[Z]): $\exists r$, $g(p+\mathbf 1)=g(p)+r$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z]), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z]), redeclared

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (TRF[Z]). -/
def TRF (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)

end DiscreteConvex.AlgorithmsC


