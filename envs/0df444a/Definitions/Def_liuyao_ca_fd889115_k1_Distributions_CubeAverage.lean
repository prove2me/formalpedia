-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Distributions_CubeAverage
-- name    : liuyao_ca_fd889115_k1_Distributions_CubeAverage
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:14:22.926509+00:00
-- url     : https://prove2.me/theorems/6b51c806-f5d9-4980-93d2-adc216db48ee
-- title:
--   Computable analysis · CubeAverage · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableDistributions/CubeAverage.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_CoordinateIntegration
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_CubeAverage

set_option autoImplicit true

namespace ComputableDistributions

export ComputableAnalysis (JointLipschitzSampler)

/-- The value sampler of a compact test, with its supplied joint bound. -/
def TestFunction.toJointLipschitzSampler {d : Nat} (φ : TestFunction d) :
    JointLipschitzSampler d where
  value x := ComputableAnalysis.RealApproximationOrder.parameter (φ.value x) (φ.value_valid x)
  bound := φ.derivativeLipschitz (zeroIndex d)
  nonnegative := φ.derivativeLipschitz_nonneg _
  control := φ.derivative_control (zeroIndex d)

/-- The distribution's action agrees with the foundation's point evaluator. -/
theorem diracAction_eq_diracValue {d : Nat} (φ : TestFunction d) :
    diracAction φ =
      (φ.toJointLipschitzSampler.diracValue (ComputableAnalysis.origin d)).real.preferred :=
  rfl

end ComputableDistributions


