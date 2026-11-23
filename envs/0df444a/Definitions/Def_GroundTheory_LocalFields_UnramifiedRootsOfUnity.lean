-- Prove2me | Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
-- name    : GroundTheory_LocalFields_UnramifiedRootsOfUnity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:49.723847+00:00
-- url     : https://prove2.me/theorems/2526376c-fcf2-4dd7-872f-ef8e2976a8ec
-- title:
--   Unramified Roots Of Unity
-- statement:
--   Definitions and structural lemmas for Unramified Roots Of Unity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedRootsOfUnity.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel Polynomial
section RootsOfUnity
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
end RootsOfUnity
section Degree
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
end Degree
end GroundTheory.LocalField


