-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardFibreStableLatticePairProjection
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardFibreStableLatticePairProjection
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T04:29:02.791842+00:00
-- url     : https://prove2.me/theorems/04e51a6a-c759-5eb9-a01e-9bc024acfcad
-- title:
--   Ncard Fibre Stable Lattice Pair Projection
-- statement:
--   Definitions and structural lemmas for Ncard Fibre Stable Lattice Pair Projection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NcardFibreStableLatticePairProjection.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma
open Polynomial
section Fibre
variable {O E A₁ A₂ : Type} [CommRing O] [Field E] [Algebra O E]
  [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂]
  [IsScalarTower O E A₁] [IsScalarTower O E A₂]
end Fibre
end GlobalTheory.UnitLemma


