-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_ConjF
-- name    : DiscreteConvex_IntegralConvexityB_ConjF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:59:13.805693+00:00
-- url     : https://prove2.me/theorems/82bcd573-77f7-4a52-8f54-82ff6be5540f
-- title:
--   Convex conjugate (Legendre-Fenchel transform)
-- statement:
--   $f^\bullet(p)=\sup_x\{\langle p,x\rangle-f(x)\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, Eq. (3.26).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, Eq. (3.26)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101, Eq. (3.26): the Legendre-Fenchel
transform (convex conjugate), in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- The **convex conjugate** `f•(p) = sup_x \{⟨p,x⟩ - f(x)\}` (Eq. (3.26)). -/
noncomputable def ConjF {V : Type*} [Fintype V] (f : (V → ℝ) → EReal) (p : V → ℝ) : EReal :=
  sSup {v : EReal | ∃ x : V → ℝ, v = ((dotProduct p x : ℝ) : EReal) - f x}

end DiscreteConvex.IntegralConvexityB


