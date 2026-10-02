-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_TRFR
-- name    : DiscreteConvex_ConjugacyDualityB_TRFR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:43.120309+00:00
-- url     : https://prove2.me/theorems/10710346-1f51-4c1f-abfb-fff85e992373
-- title:
--   TRFR
-- statement:
--   Axiom (TRF[R]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, axiom (TRF[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, axiom (TRF[R])

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (TRF[R]). -/
def TRFR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℝ, ∀ alpha : ℝ, g (fun v => p v + alpha) = g p + (alpha * r : WithTop ℝ)

end DiscreteConvex.ConjugacyDualityB


