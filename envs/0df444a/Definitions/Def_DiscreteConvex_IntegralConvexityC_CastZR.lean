-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_CastZR
-- name    : DiscreteConvex_IntegralConvexityC_CastZR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:22.000957+00:00
-- url     : https://prove2.me/theorems/dc2a204e-02d1-4cd8-8f3f-d0e788ea82bf
-- title:
--   Cast of an integer-valued function into a real-valued one
-- statement:
--   $(\mathbb Z^n\to\mathbb Z\cup\{+\infty\})\to(\mathbb Z^n\to\mathbb R\cup\{+\infty\})$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Proposition 3.30.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Proposition 3.30

import Mathlib

/-!
Casting an integer-valued function `Zⁿ → Z ∪ {+∞}` into a real-valued one `Zⁿ → R ∪ {+∞}`
(Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, Proposition 3.30's `f : Zⁿ → Z∪{+∞}`), in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- The cast `(Zⁿ → Z∪\{+∞\}) → (Zⁿ → R∪\{+∞\})`. -/
def CastZR {n : ℕ} (f : (Fin n → ℤ) → WithTop ℤ) : (Fin n → ℤ) → WithTop ℝ :=
  fun x => WithTop.map (fun z : ℤ => (z : ℝ)) (f x)

end DiscreteConvex.IntegralConvexityC


