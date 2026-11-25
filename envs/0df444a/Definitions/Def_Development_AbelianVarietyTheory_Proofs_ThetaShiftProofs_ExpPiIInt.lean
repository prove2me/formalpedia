-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpPiIInt
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpPiIInt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:28.031575+00:00
-- url     : https://prove2.me/theorems/f1cde188-1d89-4680-84f3-385bb339b226
-- title:
--   Exp Pi IInt
-- statement:
--   Definitions and structural lemmas for Exp Pi IInt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpPiIInt.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Complex
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W] [FiniteDimensional ℂ W]
  {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {O : Type} [CommRing O] [StarRing O]
  {Y M : Type} [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
  [AddCommGroup M] [Module O M] [Module.Free ℤ M] [Module.Finite ℤ M]
end GlobalTheory.OfPeriod


