-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PEigenReflectionMaps
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PEigenReflectionMaps
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:44:16.192045+00:00
-- url     : https://prove2.me/theorems/c3216591-4d3d-4ea2-9974-67ae066b9a20
-- title:
--   PEigen Reflection Maps
-- statement:
--   Definitions and structural lemmas for PEigen Reflection Maps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PEigenReflectionMaps.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
open scoped ComplexOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


