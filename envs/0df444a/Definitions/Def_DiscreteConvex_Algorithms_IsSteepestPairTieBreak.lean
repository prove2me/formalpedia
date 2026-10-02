-- Prove2me | Definitions.Def_DiscreteConvex_Algorithms_IsSteepestPairTieBreak
-- name    : DiscreteConvex_Algorithms_IsSteepestPairTieBreak
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:26:37.074984+00:00
-- url     : https://prove2.me/theorems/df638ce1-ce27-4547-acb5-0f1b032da53f
-- title:
--   Steepest pair with tie-breaking rule (Eq. 10.2)
-- statement:
--   $(u,v)$ is a steepest pair at $x$ for $f$, chosen by the **tie-breaking rule (10.2)** for a fixed ordering $\varphi$: among all pairs $u' \ne v'$ minimizing $f(x - \chi_{u'} + \chi_{v'})$, $(u,v)$ lexicographically minimizes $\Phi(u,v)$ among those achieving the minimum.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Eq. (10.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Eq. (10.2)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_Algorithms_Phi
import Definitions.Def_DiscreteConvex_Algorithms_PhiLE

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.Algorithms

/-- `(u,v)` is a steepest pair at `x` for `f`, chosen by the tie-breaking rule (10.2) for a
fixed ordering `φ`: among all pairs `u' ≠ v'` minimizing `f(x - χ_{u'} + χ_{v'})`, `(u,v)`
lexicographically minimizes `Φ(u,v)`. -/
def IsSteepestPairTieBreak {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (φ : V → ℕ) (x : V → ℤ) (u v : V) : Prop :=
  u ≠ v ∧ ∀ u' v' : V, u' ≠ v' →
    f (fun w => x w - CharVec u w + CharVec v w) ≤
        f (fun w => x w - CharVec u' w + CharVec v' w) ∧
      (f (fun w => x w - CharVec u w + CharVec v w) =
          f (fun w => x w - CharVec u' w + CharVec v' w) →
        PhiLE (Phi φ u v) (Phi φ u' v'))

end DiscreteConvex.Algorithms


