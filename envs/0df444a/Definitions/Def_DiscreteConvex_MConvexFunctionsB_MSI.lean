-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_MSI
-- name    : DiscreteConvex_MConvexFunctionsB_MSI
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:08:18.323176+00:00
-- url     : https://prove2.me/theorems/5528e136-908d-4430-8e05-6ce9422b408c
-- title:
--   MSI
-- statement:
--   Axiom **(M-SI[Z])**, Eq. (6.51): sequential improvement under every linear weighting $f[p]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.148, Eq. (6.51), axiom (M-SI[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.148, Eq. (6.51), axiom (M-SI[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_LinearWeight

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.148, Eq. (6.51), axiom (M-SI[Z]), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Axiom **(M-SI[Z])**, Eq. (6.51): sequential improvement under every linear weighting. -/
def MSI {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p : V → ℝ, ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, LinearWeight f p x > LinearWeight f p y →
    LinearWeight f p x > (SuppPos x y).inf (fun u => (SuppNeg x y).inf (fun v =>
      LinearWeight f p (fun w => x w - CharVec u w + CharVec v w)))

end DiscreteConvex.MConvexFunctionsB


