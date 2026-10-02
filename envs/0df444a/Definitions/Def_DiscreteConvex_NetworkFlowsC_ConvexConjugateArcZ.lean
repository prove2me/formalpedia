-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_ConvexConjugateArcZ
-- name    : DiscreteConvex_NetworkFlowsC_ConvexConjugateArcZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:19.232284+00:00
-- url     : https://prove2.me/theorems/a2d56b87-6fd4-44f5-be27-a5a4af6f5c5f
-- title:
--   ConvexConjugateArcZ
-- statement:
--   The discrete Legendre-Fenchel transform, univariate integer domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, univariate specialization.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, univariate specialization

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The discrete Legendre-Fenchel transform, univariate integer domain. -/
noncomputable def ConvexConjugateArcZ (g : ℤ → WithTop ℝ) (s : ℤ) : WithTop ℝ :=
  FromEReal (sSup {v : EReal | ∃ t : ℤ, v = (((s * t : ℤ) : ℝ) : EReal) - ToEReal (g t)})

-- ===== Base vocabulary, real domain (redeclared) =====

end DiscreteConvex.NetworkFlowsC


