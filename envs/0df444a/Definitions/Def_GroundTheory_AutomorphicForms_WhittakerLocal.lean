-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLocal
-- name    : GroundTheory_AutomorphicForms_WhittakerLocal
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:56:52.434599+00:00
-- url     : https://prove2.me/theorems/612cef40-c5dd-4f1e-966d-514137e79761
-- title:
--   Whittaker Local
-- statement:
--   Definitions and structural lemmas for Whittaker Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
namespace Whittaker
open MeasureTheory Measure ValuativeRel
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
section Measure
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
def thetaEquiv : GL (Fin n) F ≃* GL (Fin n) F where
  toFun := theta
  invFun := theta
  left_inv := theta_theta
  right_inv := theta_theta
  map_mul' := theta_mul
end Measure
end Whittaker
end GroundTheory.Automorphic


