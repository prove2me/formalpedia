-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:44.789816+00:00
-- url     : https://prove2.me/theorems/33016bf6-e95d-4523-be2c-9acb4faf889c
-- title:
--   Tendsto Coeff Zero
-- statement:
--   Definitions and structural lemmas for Tendsto Coeff Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TendstoCoeffZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries Filter Topology
namespace GlobalTheory.DiscUniformisation
def swap (L : PeriodPair) : PeriodPair where
  ω₁ := L.ω₂
  ω₂ := L.ω₁
  indep := LinearIndependent.pair_symm_iff.mp L.indep
end GlobalTheory.DiscUniformisation


