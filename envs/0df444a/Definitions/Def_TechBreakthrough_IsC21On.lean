-- Prove2me | Definitions.Def_TechBreakthrough_IsC21On
-- name    : TechBreakthrough_IsC21On
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:47.239071+00:00
-- url     : https://prove2.me/theorems/84c44548-2d37-4180-91f6-ca1392d8ea85
-- title:
--   $C^1$ and $C^{2,1}$ on non-open sets of the plane
-- statement:
--   For a set $K\subset\mathbb R^2$, not necessarily open, $W\in C^1(K)$ means: there are functions $p,q$ continuous on $K$ such that, at each point $(x,m)\in K$, $p(x,m)$ is the derivative of $W(\cdot,m)$ at $x$ within the horizontal slice of $K$, and $q(x,m)$ is the derivative of $W(x,\cdot)$ at $m$ within the vertical slice of $K$. $W\in C^{2,1}(K)$ asks moreover for a continuous $s$ on $K$, with $s(x,m)$ the slice derivative of $p(\cdot,m)$ at $x$.
--
--   **Formalization Note** The paper uses these classes on closed wedges without defining them. Slice derivatives are the reading under which the paper's own $W$ lies in the class.
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, Theorem 1, p.18

import Mathlib

namespace TechBreakthrough

/-- `W ∈ C¹(K)` for a set `K` of the plane that need not be open: the partial derivatives exist
along the horizontal and vertical slices of `K` and extend to continuous functions `p`, `q` on `K`.

**Formalization Note** The paper does not define `C¹` or `C^{2,1}` on non-open sets
(arXiv:2106.05112v1, p.18). Slice derivatives are the reading under which the paper's own `W` lies
in the class `𝒱` at the diagonal and on the curve `x = b(m)`. -/
def IsC1On (W : ℝ → ℝ → ℝ) (K : Set (ℝ × ℝ)) : Prop :=
  ∃ p q : ℝ → ℝ → ℝ,
    ContinuousOn (Function.uncurry p) K ∧ ContinuousOn (Function.uncurry q) K ∧
    ∀ z ∈ K,
      HasDerivWithinAt (fun y => W y z.2) (p z.1 z.2) {y | (y, z.2) ∈ K} z.1 ∧
      HasDerivWithinAt (fun n => W z.1 n) (q z.1 z.2) {n | (z.1, n) ∈ K} z.2

/-- `W ∈ C^{2,1}(K)` for a set `K` of the plane that need not be open: as `IsC1On`, with moreover
a second horizontal slice derivative `s` continuous on `K`, arXiv:2106.05112v1, p.18. -/
def IsC21On (W : ℝ → ℝ → ℝ) (K : Set (ℝ × ℝ)) : Prop :=
  ∃ p q s : ℝ → ℝ → ℝ,
    ContinuousOn (Function.uncurry p) K ∧ ContinuousOn (Function.uncurry q) K ∧
    ContinuousOn (Function.uncurry s) K ∧
    ∀ z ∈ K,
      HasDerivWithinAt (fun y => W y z.2) (p z.1 z.2) {y | (y, z.2) ∈ K} z.1 ∧
      HasDerivWithinAt (fun y => p y z.2) (s z.1 z.2) {y | (y, z.2) ∈ K} z.1 ∧
      HasDerivWithinAt (fun n => W z.1 n) (q z.1 z.2) {n | (z.1, n) ∈ K} z.2

end TechBreakthrough


