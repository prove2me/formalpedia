-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_SubmodularOn
-- name    : DiscreteConvex_CombinatorialC_SubmodularOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:39:35.270675+00:00
-- url     : https://prove2.me/theorems/67c1c0ec-2697-4791-a92f-a77bac27438c
-- title:
--   Submodularity on a set of arguments
-- statement:
--   $g(p)+g(q)\ge g(p\vee q)+g(p\wedge q)$ for all $p,q \in S$: submodularity asked only of the arguments in $S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83, Eq. (2.53), restricted to a set of arguments.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83, Eq. (2.53)

import Mathlib

namespace DiscreteConvex.CombinatorialC

/-- `g` is submodular on `S`: submodularity asked only of the arguments in `S`. Murota,
*Discrete Convex Analysis*, SIAM 2003, p. 74 defines `F(w,c)` for `c ≥ 0` only, so the `c` part
of Theorem 2.22 is a statement on the nonnegative orthant. -/
def SubmodularOn {W : Type*} [Fintype W] (S : Set (W → ℝ)) (g : (W → ℝ) → ℝ) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.CombinatorialC


