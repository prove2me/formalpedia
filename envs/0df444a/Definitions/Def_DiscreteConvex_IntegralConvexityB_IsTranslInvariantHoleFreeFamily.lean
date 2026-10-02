-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_IsTranslInvariantHoleFreeFamily
-- name    : DiscreteConvex_IntegralConvexityB_IsTranslInvariantHoleFreeFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:05:04.400561+00:00
-- url     : https://prove2.me/theorems/aaabefee-7d8c-49c3-8f7d-ed9523c419ce
-- title:
--   Translation-invariant hole-free family
-- statement:
--   Every member hole free; the family closed under integer translation.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.91, Eq. (3.53).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.91, Eq. (3.53)

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_HoleFree

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.91, Eq. (3.53): a translation-invariant family
of hole-free discrete sets, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `F` satisfies (3.53): every `S ∈ F` is hole free, and `F` is closed under translation by
any integer vector (`x - S ∈ F` for all `x ∈ Zⱽ`). -/
def IsTranslInvariantHoleFreeFamily {V : Type*} (F : Set (Set (V → ℤ))) : Prop :=
  ∀ S ∈ F, HoleFree S ∧ ∀ x : V → ℤ, (fun y => x - y) '' S ∈ F

end DiscreteConvex.IntegralConvexityB


