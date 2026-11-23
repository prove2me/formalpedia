-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MinpolyProductMap
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MinpolyProductMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:25.342268+00:00
-- url     : https://prove2.me/theorems/a7482d86-4d23-4aec-ab90-1d6b4a5afc44
-- title:
--   Minpoly Product Map
-- statement:
--   Definitions and structural lemmas for Minpoly Product Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MinpolyProductMap.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Interface
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Algebra TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold


