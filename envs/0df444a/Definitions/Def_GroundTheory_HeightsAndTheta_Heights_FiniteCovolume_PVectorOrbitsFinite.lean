-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVectorOrbitsFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVectorOrbitsFinite
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:48.482039+00:00
-- url     : https://prove2.me/theorems/ea7df24e-c830-457a-bb51-78c3e6db2ebb
-- title:
--   PVector Orbits Finite
-- statement:
--   Definitions and structural lemmas for PVector Orbits Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVectorOrbitsFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCongruenceUnitsFiniteIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
section Vectors
variable {E : Type*} [Field E] [NumberField E] {W : Type*} [AddCommGroup W] [Module E W]
end Vectors
section Spaces
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]
end Spaces
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


