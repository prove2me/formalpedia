-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDuality_ConvexConjugate
-- name    : DiscreteConvex_ConjugacyDuality_ConvexConjugate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:10:18.776625+00:00
-- url     : https://prove2.me/theorems/d2174512-47b4-4505-a0c9-9018054a9889
-- title:
--   Discrete (integer) Legendre-Fenchel transform (Eq. 8.11-Z)
-- statement:
--   The **discrete Legendre-Fenchel transform** $f^\bullet(p) = \sup\{\langle p,x\rangle - f(x) : x \in \mathbb Z^V\}$ for $p \in \mathbb Z^V$ (Eq. (8.11) restricted to integer $p$, written $(8.11)_{\mathbb Z}$ in the book). The defining supremum is taken in `EReal` and projected back to `WithTop ℝ` via `FromEReal`, so $f^\bullet$ has the same type as $f$ itself and the transform can be iterated.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDuality_FromEReal

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.212, Eq. (8.11)_Z: the discrete (integer)
Legendre-Fenchel transform, in `DiscreteConvex.ConjugacyDuality`.
-/

namespace DiscreteConvex.ConjugacyDuality

/-- The discrete Legendre-Fenchel transform `f•(p) = sup\{⟨p,x⟩ - f(x) : x ∈ Zⱽ\}` for
`p ∈ Zⱽ` (Eq. (8.11) restricted to integer `p`, i.e. `(8.11)_Z`). The defining supremum is
taken in `EReal` (a complete lattice) and then projected back to `WithTop ℝ` via `FromEReal`,
so `f•` has the same type as `f` itself. -/
noncomputable def ConvexConjugate {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ)
    (p : V → ℤ) : WithTop ℝ :=
  FromEReal (sSup {v : EReal | ∃ x : V → ℤ,
    v = ((∑ i, (p i : ℝ) * (x i : ℝ) : ℝ) : EReal) - ToEReal (f x)})

end DiscreteConvex.ConjugacyDuality


