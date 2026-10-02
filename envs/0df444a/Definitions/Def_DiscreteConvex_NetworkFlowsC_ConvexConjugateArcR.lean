-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_ConvexConjugateArcR
-- name    : DiscreteConvex_NetworkFlowsC_ConvexConjugateArcR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:32.448822+00:00
-- url     : https://prove2.me/theorems/34d3bdb0-b6ad-4843-b734-7b55faaba9ab
-- title:
--   ConvexConjugateArcR
-- statement:
--   The real-variable Legendre-Fenchel transform, univariate.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.26), univariate specialization.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.26), univariate specialization

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The (real-variable) Legendre-Fenchel transform, univariate. -/
noncomputable def ConvexConjugateArcR (g : ℝ → WithTop ℝ) (s : ℝ) : WithTop ℝ :=
  FromEReal (sSup {v : EReal | ∃ t : ℝ, v = ((s * t : ℝ) : EReal) - ToEReal (g t)})

end DiscreteConvex.NetworkFlowsC


