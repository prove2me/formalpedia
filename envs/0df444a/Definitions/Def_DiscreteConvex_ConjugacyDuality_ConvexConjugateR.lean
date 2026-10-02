-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_ConvexConjugateR
-- name    : DiscreteConvex_ConjugacyDuality_ConvexConjugateR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:10:22.233299+00:00
-- url     : https://prove2.me/theorems/b5b9629e-1c60-4651-ba94-464694d54744
-- title:
--   Real (continuous) Legendre-Fenchel transform (Eq. 8.3)
-- statement:
--   The real Legendre-Fenchel transform $f^\bullet(p) = \sup\{\langle p,x\rangle - f(x) ; x \in \mathbb R^V\}$ for $p \in \mathbb R^V$, landing in `EReal` since the supremum need not be finite.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.206, Eq. (8.3).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.206, Eq. (8.3)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ToEReal

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.206, Eq. (8.3): the real (continuous)
Legendre-Fenchel transform, in `DiscreteConvex.ConjugacyDuality`.
-/

namespace DiscreteConvex.ConjugacyDuality

/-- The real Legendre-Fenchel transform `f•(p) = sup\{⟨p,x⟩ - f(x) : x ∈ Rⱽ\}` for `p ∈ Rⱽ`
(Eq. (8.3)), landing in `EReal` since the supremum need not be finite. -/
noncomputable def ConvexConjugateR {V : Type*} [Fintype V] (f : (V → ℝ) → WithTop ℝ)
    (p : V → ℝ) : EReal :=
  sSup {v : EReal | ∃ x : V → ℝ,
    v = ((∑ i, p i * x i : ℝ) : EReal) - ToEReal (f x)}

end DiscreteConvex.ConjugacyDuality


