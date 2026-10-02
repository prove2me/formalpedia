-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_ConvexClosure
-- name    : DiscreteConvex_IntegralConvexityC_ConvexClosure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:00.134612+00:00
-- url     : https://prove2.me/theorems/1849c9df-cae1-4aeb-a7d5-443c7e6ae817
-- title:
--   Convex closure of a discrete function
-- statement:
--   $\bar f(x)=\sup_{p,\alpha}\{\langle p,x\rangle+\alpha:\langle p,y\rangle+\alpha\le f(y)\ \forall y\in\mathbb Z^n\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.56).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.56)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93, Eq. (3.56): the convex closure of a
function on the integer lattice, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- The convex closure `f̄ : Rⁿ → R ∪ {±∞}` of `f : Zⁿ → R ∪ {+∞}` (Eq. (3.56)). -/
noncomputable def ConvexClosure {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (x : Fin n → ℝ) : EReal :=
  sSup {v : EReal | ∃ (p : Fin n → ℝ) (a : ℝ),
    (∀ y : Fin n → ℤ, ((a + ∑ i, p i * (y i : ℝ) : ℝ) : EReal) ≤ WithBot.some (f y)) ∧
    v = ((a + ∑ i, p i * x i : ℝ) : EReal)}

end DiscreteConvex.IntegralConvexityC


