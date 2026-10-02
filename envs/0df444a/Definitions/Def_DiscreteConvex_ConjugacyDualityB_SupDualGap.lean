-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_SupDualGap
-- name    : DiscreteConvex_ConjugacyDualityB_SupDualGap
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:33:01.105097+00:00
-- url     : https://prove2.me/theorems/29694009-2452-4830-b34b-e59eb99173cb
-- title:
--   SupDualGap
-- statement:
--   $\sup\{h^\circ(p)-f^\bullet(p):p\in\mathbb R^V\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.222, Eq. (8.31).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.222, Eq. (8.31)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateZR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConcaveConjugateZR

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `sup{h◦(p) - f•(p) : p ∈ Rⱽ}`. -/
noncomputable def SupDualGap (f h2 : (V → ℤ) → WithTop ℝ) : EReal :=
  sSup {v : EReal | ∃ p : V → ℝ, v = ConcaveConjugateZR h2 p - ConvexConjugateZR f p}

end DiscreteConvex.ConjugacyDualityB


