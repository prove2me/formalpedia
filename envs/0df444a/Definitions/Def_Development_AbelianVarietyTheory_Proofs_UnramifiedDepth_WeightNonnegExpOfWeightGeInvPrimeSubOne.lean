-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightNonnegExpOfWeightGeInvPrimeSubOne
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightNonnegExpOfWeightGeInvPrimeSubOne
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:30:34.201786+00:00
-- url     : https://prove2.me/theorems/011526a5-0702-4db9-891e-748dea00f425
-- title:
--   Weight Nonneg Exp Of Weight Ge Inv Prime Sub One
-- statement:
--   Definitions and structural lemmas for Weight Nonneg Exp Of Weight Ge Inv Prime Sub One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WeightNonnegExpOfWeightGeInvPrimeSubOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
namespace GlobalTheory.ExpWeight
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
  {σ : Type} [DecidableEq σ] (ρ : σ → ℝ)
end GlobalTheory.ExpWeight


