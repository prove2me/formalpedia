-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_ConcConjF
-- name    : DiscreteConvex_IntegralConvexityB_ConcConjF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:59:13.369989+00:00
-- url     : https://prove2.me/theorems/8b38cf6b-01b5-4839-a3d8-0efe3f6efdad
-- title:
--   Concave conjugate
-- statement:
--   $h^\circ(p)=\inf_x\{\langle p,x\rangle-h(x)\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, Eq. (3.28).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, Eq. (3.28)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101, Eq. (3.28): the concave conjugate, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- The **concave conjugate** `h◦(p) = inf_x \{⟨p,x⟩ - h(x)\}` (Eq. (3.28)). -/
noncomputable def ConcConjF {V : Type*} [Fintype V] (h : (V → ℝ) → EReal) (p : V → ℝ) : EReal :=
  sInf {v : EReal | ∃ x : V → ℝ, v = ((dotProduct p x : ℝ) : EReal) - h x}

end DiscreteConvex.IntegralConvexityB


