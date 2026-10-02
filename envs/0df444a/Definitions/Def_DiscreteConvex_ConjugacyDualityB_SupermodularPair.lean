-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_SupermodularPair
-- name    : DiscreteConvex_ConjugacyDualityB_SupermodularPair
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:28:09.822888+00:00
-- url     : https://prove2.me/theorems/5f6e6057-c238-4b15-9180-30e313f6cb84
-- title:
--   SupermodularPair
-- statement:
--   $f$ is supermodular.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.207, standard notion.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.207, standard notion

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is supermodular. -/
def SupermodularPair (f : (Fin 2 → ℝ) → WithTop ℝ) : Prop :=
  ∀ p q : Fin 2 → ℝ, f p + f q ≤ f (p ⊔ q) + f (p ⊓ q)

end DiscreteConvex.ConjugacyDualityB


