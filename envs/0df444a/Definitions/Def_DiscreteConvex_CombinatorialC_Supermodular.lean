-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_Supermodular
-- name    : DiscreteConvex_CombinatorialC_Supermodular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:39:39.446297+00:00
-- url     : https://prove2.me/theorems/81de2db9-99d9-4888-9519-629a4a353ba2
-- title:
--   Supermodularity of a real function
-- statement:
--   $g(p)+g(q)\le g(p\vee q)+g(p\wedge q)$ for all $p,q$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83, Eq. (2.54).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83, Eq. (2.54)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83, Eq. (2.54): supermodularity of a
real-valued function, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Supermodularity** (2.54) of `g : Rᵂ → R`: `g(p) + g(q) ≤ g(p ∨ q) + g(p ∧ q)`. -/
def Supermodular {W : Type*} [Fintype W] (g : (W → ℝ) → ℝ) : Prop :=
  ∀ p q : W → ℝ, g p + g q ≤ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.CombinatorialC


