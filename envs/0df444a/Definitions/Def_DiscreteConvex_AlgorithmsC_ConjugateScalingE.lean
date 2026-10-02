-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateScalingE
-- name    : DiscreteConvex_AlgorithmsC_ConjugateScalingE
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:35:47.78436+00:00
-- url     : https://prove2.me/theorems/7444c74f-25b9-4cdc-bfd9-5c0ea87f24b2
-- title:
--   ConjugateScalingE
-- statement:
--   $f\langle\alpha\rangle$, $EReal$-valued.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.319, Eq. (10.77), EReal version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.319, Eq. (10.77), EReal version

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_ConjugateFromZE
import Definitions.Def_DiscreteConvex_AlgorithmsC_ScaledConjugate

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f⟨α⟩`, `EReal`-valued, Eq. (10.77). -/
noncomputable def ConjugateScalingE (g : (V → ℤ) → WithTop ℝ) (alpha : ℤ) (x : V → ℝ) : EReal :=
  ConjugateFromZE (ScaledConjugate g alpha) x

end DiscreteConvex.AlgorithmsC


