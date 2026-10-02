-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNatSI
-- name    : DiscreteConvex_MConvexFunctionsB_MNatSI
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:09:52.798259+00:00
-- url     : https://prove2.me/theorems/8a935214-db65-40f9-bd25-717f244242fd
-- title:
--   MNatSI
-- statement:
--   Axiom **(M$^\natural$-SI[Z])**, Eq. (6.52): the M$^\natural$-version, allowing $u$ or $v$ to be skipped ($\chi_0=0$).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.148, Eq. (6.52), axiom (M-nat-SI[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.148, Eq. (6.52), axiom (M-nat-SI[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVecOpt
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_LinearWeight

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.148, Eq. (6.52), axiom (M-nat-SI[Z]), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Axiom **(M♮-SI[Z])**, Eq. (6.52): the M♮-version, allowing `u` or `v` to be skipped
(`χ₀ = 0`). -/
def MNatSI {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p : V → ℝ, ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, LinearWeight f p x > LinearWeight f p y →
    LinearWeight f p x >
      (insert none ((SuppPos x y).image some)).inf (fun u =>
        (insert none ((SuppNeg x y).image some)).inf (fun v =>
          LinearWeight f p (fun w => x w - CharVecOpt u w + CharVecOpt v w)))

end DiscreteConvex.MConvexFunctionsB


