-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_FCheck
-- name    : DiscreteConvex_MConvexFunctionsB_FCheck
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:08:39.215843+00:00
-- url     : https://prove2.me/theorems/f48b5ecb-08d2-4f36-aaab-f49f79cd136a
-- title:
--   FCheck
-- statement:
--   The "checked" subgradient value $\check f(x,y)$, Eq. (6.55): the infimum, over integer flows $\lambda : V\times V \to \mathbb Z_+$ routing $y-x$, of the total exchange cost.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.148, Eq. (6.55).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.148, Eq. (6.55)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVec

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.148, Eq. (6.55), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

open Classical in
/-- The "checked" subgradient value `f̌(x,y)`, Eq. (6.55): the infimum, over integer flows
`λ : V × V → Z₊` routing `y-x`, of the total exchange cost. -/
noncomputable def FCheck {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (x y : V → ℤ) : WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ lam : V → V → ℕ,
    (∀ w, y w - x w = ∑ u, ∑ v, (lam u v : ℤ) * (CharVec v w - CharVec u w)) ∧
    L = ∑ u, ∑ v, (lam u v) • (f (fun w => x w - CharVec u w + CharVec v w) - f x)}

end DiscreteConvex.MConvexFunctionsB


