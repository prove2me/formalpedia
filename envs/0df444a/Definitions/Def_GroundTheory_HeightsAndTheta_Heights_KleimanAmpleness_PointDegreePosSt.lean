-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PointDegreePosSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PointDegreePosSt
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:54:21.710341+00:00
-- url     : https://prove2.me/theorems/7783fab6-16e4-4966-b8e3-af71bf0c08c5
-- title:
--   Point Degree Pos St
-- statement:
--   Definitions and structural lemmas for Point Degree Pos St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PointDegreePosSt.lean

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
universe u w
def PointDegreePos.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), IsSubvar x pp 0 →
    0 < FieldNumbers.resDeg (pp.comap (oneBlock (S := k) (N := N)).toRingHom)
end
end GroundTheory.Heights₂.Heights.Kleiman


