-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateScaling
-- name    : DiscreteConvex_AlgorithmsC_ConjugateScaling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:42:13.439065+00:00
-- url     : https://prove2.me/theorems/e7fdd4a4-56e0-40d2-a2f2-aec9e8ba198b
-- title:
--   ConjugateScaling
-- statement:
--   $f\langle\alpha\rangle=\mathrm{ConjugateFromZ}(g_\alpha)$, the conjugate scaling of $f$ with scaling factor $\alpha$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.319, Eq. (10.77).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.319, Eq. (10.77)

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_FromEReal
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateScalingE

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f⟨α⟩ = ConjugateFromZ(g_α)`, the conjugate scaling of `f` with scaling factor `α`, Eq.
(10.77). -/
noncomputable def ConjugateScaling (g : (V → ℤ) → WithTop ℝ) (alpha : ℤ) (x : V → ℝ) : WithTop ℝ :=
  FromEReal (ConjugateScalingE g alpha x)

-- ===== Theorems =====

end DiscreteConvex.AlgorithmsC


