-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteOrderParams
-- name    : GroundTheory_GlobalFields_TateThesis_FiniteOrderParams
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:01:13.865463+00:00
-- url     : https://prove2.me/theorems/5d19eb6c-d65e-54cd-a386-053f46b616af
-- title:
--   Finite Order Params
-- statement:
--   Definitions and structural lemmas for Finite Order Params, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteOrderParams.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing
namespace GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace HeckeCharacter
open IdeleGroup
variable (χ : HeckeCharacter K)
end HeckeCharacter
end
end GroundTheory.Global


