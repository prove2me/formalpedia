-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_TRF
-- name    : DiscreteConvex_ConjugacyDualityD_TRF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:55:51.692286+00:00
-- url     : https://prove2.me/theorems/db509570-c236-4900-b667-22a9864040cd
-- title:
--   TRF
-- statement:
--   Axiom (TRF[Z]): $\exists r$, $g(p+\mathbf 1)=g(p)+r$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z]), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z]), redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (TRF[Z]): `∃r, g(p+1) = g(p)+r`. -/
def TRF (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)

end DiscreteConvex.ConjugacyDualityD


