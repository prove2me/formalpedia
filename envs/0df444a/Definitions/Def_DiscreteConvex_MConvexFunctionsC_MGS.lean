-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_MGS
-- name    : DiscreteConvex_MConvexFunctionsC_MGS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:24:39.559652+00:00
-- url     : https://prove2.me/theorems/232f8fff-7780-4deb-abed-8eef9d8a2c89
-- title:
--   MGS
-- statement:
--   Axiom (M-GS[Z]), the **gross substitutes property**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.153, Eq. (6.60).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.153, Eq. (6.60)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_LinearWeight
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ArgMinOn

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M-GS[Z]), Eq. (6.60). -/
def MGS (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℝ, (∀ v, p v ≤ q v) → ∀ x ∈ ArgMinOn (LinearWeight f p),
    (ArgMinOn (LinearWeight f q)).Nonempty →
    ∃ y ∈ ArgMinOn (LinearWeight f q), ∀ v, p v = q v → y v ≥ x v

end DiscreteConvex.MConvexFunctionsC


