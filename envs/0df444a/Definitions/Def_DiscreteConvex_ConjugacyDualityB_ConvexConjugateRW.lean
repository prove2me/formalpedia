-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateRW
-- name    : DiscreteConvex_ConjugacyDualityB_ConvexConjugateRW
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:32:57.309763+00:00
-- url     : https://prove2.me/theorems/c119f757-08d4-4ad9-a82b-1e45d600dda2
-- title:
--   ConvexConjugateRW
-- statement:
--   $f^\bullet$, projected back to `WithTop ℝ`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.206, Eq. (8.3).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.206, Eq. (8.3)

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_FromEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateR

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f•`, projected back to `WithTop ℝ`. -/
noncomputable def ConvexConjugateRW (f : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : WithTop ℝ :=
  FromEReal (ConvexConjugateR f p)

end DiscreteConvex.ConjugacyDualityB


