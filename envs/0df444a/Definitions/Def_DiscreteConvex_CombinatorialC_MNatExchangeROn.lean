-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_MNatExchangeROn
-- name    : DiscreteConvex_CombinatorialC_MNatExchangeROn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:41:31.2591+00:00
-- url     : https://prove2.me/theorems/cc5cd3d7-15ab-4f43-994a-4463635933a7
-- title:
--   The M-natural exchange property on a set of arguments
-- statement:
--   The M$^\natural$ exchange property (M$^\natural$-EXC[R]) asked only of arguments $x,y \in S$: for every $i \in \mathrm{supp}^+(x-y)$ there is either a $j \in \mathrm{supp}^-(x-y)$ and an $\alpha_0>0$ with $f(x)+f(y)\ge f(x-\alpha(\chi_i-\chi_j))+f(y+\alpha(\chi_i-\chi_j))$ for all $0\le\alpha\le\alpha_0$, or an $\alpha_0>0$ with $f(x)+f(y)\ge f(x-\alpha\chi_i)+f(y+\alpha\chi_i)$ for all $0\le\alpha\le\alpha_0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.84, restricted to a set of arguments.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.84

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppNegR
import Definitions.Def_DiscreteConvex_CombinatorialC_CharVec

namespace DiscreteConvex.CombinatorialC

/-- The M♮ exchange property on `S`: the exchange asked only of the arguments in `S`. Murota,
*Discrete Convex Analysis*, SIAM 2003, p. 74 defines `F(w,c)` for `c ≥ 0` only, so the `c` part
of Theorem 2.23 is a statement on the nonnegative orthant. -/
def MNatExchangeROn {W : Type*} [Fintype W] [DecidableEq W] (S : Set (W → ℝ))
    (f : (W → ℝ) → ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ i ∈ SuppPosR (x - y),
    (∃ j ∈ SuppNegR (x - y), ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      f x + f y ≥ f (x - α • (CharVec i - CharVec j)) + f (y + α • (CharVec i - CharVec j))) ∨
    (∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      f x + f y ≥ f (x - α • CharVec i) + f (y + α • CharVec i))

end DiscreteConvex.CombinatorialC


