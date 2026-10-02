-- Prove2me | Definitions.Def_DiscreteConvex_Algorithms_IsK1
-- name    : DiscreteConvex_Algorithms_IsK1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:26:30.391022+00:00
-- url     : https://prove2.me/theorems/9f979122-845e-4491-b48f-69c4e7d85260
-- title:
--   The $\ell^1$-diameter $K_1$ of an effective domain (Eq. 10.1)
-- statement:
--   $k$ is the **$\ell^1$-diameter** $K_1 = \max\{\|x-y\|_1 : x,y \in \operatorname{dom} f\}$ of $f$'s effective domain (Eq. (10.1)).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Eq. (10.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Eq. (10.1)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_Algorithms_L1Dist

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.Algorithms

/-- `k` is the **`ℓ¹`-diameter** `K1 = max\{‖x-y‖₁ : x,y ∈ dom f\}` of `f`'s effective domain
(Eq. (10.1)). -/
def IsK1 {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) (k : ℕ) : Prop :=
  (∀ x ∈ DomZ f, ∀ y ∈ DomZ f, L1Dist x y ≤ k) ∧ (∃ x ∈ DomZ f, ∃ y ∈ DomZ f, L1Dist x y = k)

end DiscreteConvex.Algorithms


