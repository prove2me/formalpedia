-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_WeightOperators
-- name    : GroundTheory_AutomorphicForms_GL2Classical_WeightOperators
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:59.528467+00:00
-- url     : https://prove2.me/theorems/0772d7be-a617-4335-86bf-dfee09716fec
-- title:
--   Weight Operators
-- statement:
--   Definitions and structural lemmas for Weight Operators, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/WeightOperators.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
namespace GroundTheory.Automorphic
namespace GL2Classical
variable {E : Type*} [AddCommGroup E] [Module ℂ E] {Rr Ll Jj : Module.End ℂ E}
end GL2Classical
end GroundTheory.Automorphic


