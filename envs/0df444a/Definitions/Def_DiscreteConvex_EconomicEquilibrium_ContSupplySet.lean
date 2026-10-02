-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_ContSupplySet
-- name    : DiscreteConvex_EconomicEquilibrium_ContSupplySet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:58:51.10644+00:00
-- url     : https://prove2.me/theorems/447d3a05-f17d-4435-9759-663558ec6276
-- title:
--   Continuous supply correspondence (Eq. 11.32)
-- statement:
--   The continuous supply set (Eq. (11.32)) $\hat S_l(p) = \arg\max_{y \in \mathbb R^K} (\langle p,y\rangle - \hat C_l(y))$, where $\hat C_l$ is the convex closure of $C_l$. Part of the "derived continuous economy" used in Theorem 11.14's hypothesis.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337, Eq. (11.32).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337, Eq. (11.32)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_ConvexClosureR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.337, Eq. (11.32): the continuous supply
correspondence of the derived continuous economy, in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The continuous supply set (Eq. (11.32)) `Ŝl(p) = arg max_{y ∈ Rᴷ} (⟨p,y⟩ − Ĉl(y))`, where
`Ĉl` is the convex closure of `Cl`. -/
def ContSupplySet {K : Type*} [Fintype K] (C : (K → ℤ) → WithTop ℝ) (p : K → ℝ) : Set (K → ℝ) :=
  {y | ∀ z : K → ℝ,
    ((∑ k, p k * z k : ℝ) : EReal) + (-ConvexClosureR C z) ≤
      ((∑ k, p k * y k : ℝ) : EReal) + (-ConvexClosureR C y)}

end DiscreteConvex.EconomicEquilibrium


