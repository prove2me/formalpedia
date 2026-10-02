-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_TRF
-- name    : DiscreteConvex_ConjugacyDualityC_TRF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:01.257527+00:00
-- url     : https://prove2.me/theorems/f1e6f285-22ae-4058-bf77-8f63b312d784
-- title:
--   TRF
-- statement:
--   Axiom (TRF[Z]): $\exists r$, $g(p+\mathbf 1)=g(p)+r$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z])

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (TRF[Z]): `∃r, g(p+1) = g(p)+r`. -/
def TRF (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)

end DiscreteConvex.ConjugacyDualityC


