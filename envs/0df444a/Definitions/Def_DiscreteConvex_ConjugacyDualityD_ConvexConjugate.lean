-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConvexConjugate
-- name    : DiscreteConvex_ConjugacyDualityD_ConvexConjugate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:58:07.223274+00:00
-- url     : https://prove2.me/theorems/b1b43d0e-e5f6-4fc5-b248-e05f98ff2c90
-- title:
--   ConvexConjugate
-- statement:
--   The discrete Legendre-Fenchel transform $f^\bullet(p)=\sup\{\langle p,x\rangle-f(x):x\in\mathbb Z^V\}$ for $p\in\mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_FromEReal

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The discrete Legendre-Fenchel transform `f•(p) = sup{⟨p,x⟩ - f(x) : x ∈ Zⱽ}` for
`p ∈ Zⱽ`. -/
noncomputable def ConvexConjugate (f : (V → ℤ) → WithTop ℝ) (p : V → ℤ) : WithTop ℝ :=
  FromEReal (sSup {v : EReal | ∃ x : V → ℤ,
    v = ((∑ i, (p i : ℝ) * (x i : ℝ) : ℝ) : EReal) - ToEReal (f x)})

end DiscreteConvex.ConjugacyDualityD


