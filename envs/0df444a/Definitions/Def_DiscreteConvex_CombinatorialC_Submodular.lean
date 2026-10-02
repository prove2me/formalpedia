-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_Submodular
-- name    : DiscreteConvex_CombinatorialC_Submodular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:39:33.249454+00:00
-- url     : https://prove2.me/theorems/8979c2d4-0672-4303-81b2-0f21c7f3653c
-- title:
--   Submodularity of a real function
-- statement:
--   $g(p)+g(q)\ge g(p\vee q)+g(p\wedge q)$ for all $p,q$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83, Eq. (2.53).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83, Eq. (2.53)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83, Eq. (2.53): submodularity of a real-valued
function, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Submodularity** (2.53) of `g : Rᵂ → R`: `g(p) + g(q) ≥ g(p ∨ q) + g(p ∧ q)`. -/
def Submodular {W : Type*} [Fintype W] (g : (W → ℝ) → ℝ) : Prop :=
  ∀ p q : W → ℝ, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.CombinatorialC


