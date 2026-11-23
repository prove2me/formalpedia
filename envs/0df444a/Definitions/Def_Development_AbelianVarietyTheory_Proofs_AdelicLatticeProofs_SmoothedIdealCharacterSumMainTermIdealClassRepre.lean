-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SmoothedIdealCharacterSumMainTermIdealClassRepre
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SmoothedIdealCharacterSumMainTermIdealClassRepre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:29:10.274204+00:00
-- url     : https://prove2.me/theorems/81c8113f-87de-48e0-818c-38e10c365f8c
-- title:
--   Smoothed Ideal Character Sum Main Term Ideal Class Repre
-- statement:
--   Definitions and structural lemmas for Smoothed Ideal Character Sum Main Term Ideal Class Repre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SmoothedIdealCharacterSumMainTermIdealClassRepre.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealSumPeriodicDilate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
end GlobalTheory


