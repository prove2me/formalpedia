-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWeightPos
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWeightPos
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:54.315995+00:00
-- url     : https://prove2.me/theorems/94dae2ab-0bc2-496e-89c8-ca47936adfb9
-- title:
--   PWeight Pos
-- statement:
--   Definitions and structural lemmas for PWeight Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWeightPos.lean

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
open NumberField Module Matrix
open scoped ComplexOrder
section Steps
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
end Steps
end GroundTheory.Heights₂.Heights.FiniteCovolume


