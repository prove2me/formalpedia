-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateFromZE
-- name    : DiscreteConvex_AlgorithmsC_ConjugateFromZE
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:25:47.624252+00:00
-- url     : https://prove2.me/theorems/bb4fb594-e3e7-4b6b-b9ae-85ea9de70bc1
-- title:
--   ConjugateFromZE
-- statement:
--   $f(x)=\sup\{\langle p,x\rangle-g(p)\mid p\in\mathbb Z^V\}$, $EReal$-valued.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.319, Eq. (10.76), EReal version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.319, Eq. (10.76), EReal version

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_ToEReal

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f(x) = sup{⟨p,x⟩ - g(p) | p ∈ Zⱽ}`, `EReal`-valued, Eq. (10.76). -/
noncomputable def ConjugateFromZE (g : (V → ℤ) → WithTop ℝ) (x : V → ℝ) : EReal :=
  sSup {v : EReal | ∃ p : V → ℤ,
    v = ((∑ i, (p i : ℝ) * x i : ℝ) : EReal) - ToEReal (g p)}

end DiscreteConvex.AlgorithmsC


