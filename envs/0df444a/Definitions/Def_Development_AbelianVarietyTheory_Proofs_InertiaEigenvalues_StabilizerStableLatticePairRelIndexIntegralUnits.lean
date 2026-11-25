-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StabilizerStableLatticePairRelIndexIntegralUnits
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StabilizerStableLatticePairRelIndexIntegralUnits
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T04:28:48.374901+00:00
-- url     : https://prove2.me/theorems/ee9a7996-7ddd-52fe-aa39-e9b358591441
-- title:
--   Stabilizer Stable Lattice Pair Rel Index Integral Units
-- statement:
--   Definitions and structural lemmas for Stabilizer Stable Lattice Pair Rel Index Integral Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StabilizerStableLatticePairRelIndexIntegralUnits.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma.PairStab
open GlobalTheory.UnitLemma Polynomial
section
variable (O : Type) [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂]
variable (E : Type) [Field E] [Algebra E A₁] [Algebra E A₂]
end
end GlobalTheory.UnitLemma.PairStab


