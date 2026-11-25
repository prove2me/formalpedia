-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GL2_ExistsEqPowMulOfValuationLe
-- name    : GroundTheory_AutomorphicForms_GL2_ExistsEqPowMulOfValuationLe
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:03.620029+00:00
-- url     : https://prove2.me/theorems/9f7c4bee-7420-59df-8461-d3d6c50d7eaa
-- title:
--   Exists Eq Pow Mul Of Valuation Le
-- statement:
--   Definitions and structural lemmas for Exists Eq Pow Mul Of Valuation Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
end GodementJacquet
end GroundTheory.Automorphic


