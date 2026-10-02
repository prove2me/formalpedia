-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_QSBw
-- name    : DiscreteConvex_LConvexFunctionsD_QSBw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:02:57.243648+00:00
-- url     : https://prove2.me/theorems/535d2802-e591-4a31-8602-84caf7d636cf
-- title:
--   QSBw
-- statement:
--   Axiom (QSBw), the weaker variant of (QSB).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, axiom (QSBw).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, axiom (QSBw)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomZ

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (QSBw), the weaker variant of (QSB). -/
def QSBw (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p ∈ DomZ g, ∀ q ∈ DomZ g, max (g p) (g q) ≥ min (g (p ⊓ q)) (g (p ⊔ q))

end DiscreteConvex.LConvexFunctionsD


