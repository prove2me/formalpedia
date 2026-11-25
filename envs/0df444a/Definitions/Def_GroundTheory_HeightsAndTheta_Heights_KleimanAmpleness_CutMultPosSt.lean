-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutMultPosSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutMultPosSt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:57:58.094393+00:00
-- url     : https://prove2.me/theorems/8e3224a4-6116-441f-9166-f8cc30fef2bc
-- title:
--   Cut Mult Pos St
-- statement:
--   Definitions and structural lemmas for Cut Mult Pos St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CutMultPosSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u
def CutMultPos.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (J qq : Ideal (Poly S N))
    (h : qq ∈ J.minimalPrimes),
    haveI : qq.IsPrime := h.1.1
    0 < cutMult J qq ∧ cutMult J qq < ⊤
end
end GroundTheory.Heights₂.Heights.Kleiman


