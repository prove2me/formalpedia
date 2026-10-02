-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_SupermodularOn
-- name    : DiscreteConvex_CombinatorialC_SupermodularOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:39:50.253042+00:00
-- url     : https://prove2.me/theorems/076e4ecf-f4aa-4720-96c3-adb43def93c1
-- title:
--   Supermodularity on a set of arguments
-- statement:
--   $g(p)+g(q)\le g(p\vee q)+g(p\wedge q)$ for all $p,q \in S$: supermodularity asked only of the arguments in $S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83, restricted to a set of arguments.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83

import Mathlib

namespace DiscreteConvex.CombinatorialC

/-- `g` is supermodular on `S`: supermodularity asked only of the arguments in `S`. Murota,
*Discrete Convex Analysis*, SIAM 2003, p. 74 defines `F(w,c)` for `c ≥ 0` only, so the `c` part
of Theorem 2.22 is a statement on the nonnegative orthant. -/
def SupermodularOn {W : Type*} [Fintype W] (S : Set (W → ℝ)) (g : (W → ℝ) → ℝ) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, g p + g q ≤ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.CombinatorialC


