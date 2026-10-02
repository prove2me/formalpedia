-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_ContDemandSet
-- name    : DiscreteConvex_EconomicEquilibrium_ContDemandSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:58:47.546842+00:00
-- url     : https://prove2.me/theorems/225312fb-7195-4981-8915-8cbb51f0402d
-- title:
--   Continuous demand correspondence (Eq. 11.31)
-- statement:
--   The continuous demand set (Eq. (11.31)) $\hat D_h(p) = \arg\max_{x \in \mathbb R^K} (\hat U_h(x) - \langle p,x\rangle)$, where $\hat U_h$ is the concave closure of $U_h$. Part of the "derived continuous economy" used in Theorem 11.14's hypothesis.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337, Eq. (11.31).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337, Eq. (11.31)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_ConcaveClosureR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.337, Eq. (11.31): the continuous demand
correspondence of the derived continuous economy, in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The continuous demand set (Eq. (11.31)) `D̂h(p) = arg max_{x ∈ Rᴷ} (Ûh(x) − ⟨p,x⟩)`, where
`Ûh` is the concave closure of `Uh`. -/
def ContDemandSet {K : Type*} [Fintype K] (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) : Set (K → ℝ) :=
  {x | ∀ z : K → ℝ,
    ConcaveClosureR U z + ((-(∑ k, p k * z k) : ℝ) : EReal) ≤
      ConcaveClosureR U x + ((-(∑ k, p k * x k) : ℝ) : EReal)}

end DiscreteConvex.EconomicEquilibrium


