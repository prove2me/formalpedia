-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:07:47.439707+00:00
-- url     : https://prove2.me/theorems/cec4ec0b-9a2d-552f-a220-27ae63ea0f65
-- title:
--   PLine Pair Orbits Finite
-- statement:
--   Definitions and structural lemmas for PLine Pair Orbits Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLinePairOrbitsFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
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
universe u
section Sandwich
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
variable [NoZeroSMulDivisors ℕ A]
end Sandwich
section Pairs
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W]
end Pairs
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


