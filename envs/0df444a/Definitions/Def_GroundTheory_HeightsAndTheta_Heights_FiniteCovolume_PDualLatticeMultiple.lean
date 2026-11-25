-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDualLatticeMultiple
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDualLatticeMultiple
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T04:22:33.737187+00:00
-- url     : https://prove2.me/theorems/ebc85640-e658-440f-9197-87c3673e4d80
-- title:
--   PDual Lattice Multiple
-- statement:
--   Definitions and structural lemmas for PDual Lattice Multiple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDualLatticeMultiple.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StDualLatticeMultiple
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
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


