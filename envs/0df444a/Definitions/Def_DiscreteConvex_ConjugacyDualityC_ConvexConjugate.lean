-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_ConvexConjugate
-- name    : DiscreteConvex_ConjugacyDualityC_ConvexConjugate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:42:17.258896+00:00
-- url     : https://prove2.me/theorems/223f95b5-389a-40c4-8f69-c300f78d62eb
-- title:
--   ConvexConjugate
-- statement:
--   The discrete Legendre-Fenchel transform $f^\bullet(p)=\sup\{\langle p,x\rangle-f(x):x\in\mathbb Z^V\}$ for $p\in\mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_FromEReal

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The discrete Legendre-Fenchel transform `f•(p) = sup{⟨p,x⟩ - f(x) : x ∈ Zⱽ}` for
`p ∈ Zⱽ`. -/
noncomputable def ConvexConjugate (f : (V → ℤ) → WithTop ℝ) (p : V → ℤ) : WithTop ℝ :=
  FromEReal (sSup {v : EReal | ∃ x : V → ℤ,
    v = ((∑ i, (p i : ℝ) * (x i : ℝ) : ℝ) : EReal) - ToEReal (f x)})

end DiscreteConvex.ConjugacyDualityC


