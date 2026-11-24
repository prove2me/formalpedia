-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ClosedEmb
-- name    : Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ClosedEmb
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:41.032379+00:00
-- url     : https://prove2.me/theorems/0e8be657-ddfe-4dc2-9c21-97eefef68c1f
-- title:
--   Closed Emb
-- statement:
--   Definitions and structural lemmas for Closed Emb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter Matrix NumberField IsDedekindDomain
open scoped Pointwise MatrixGroups
section Ring
variable {R : Type} [CommRing R]
def uni : Multiplicative R →* SL(2, R) where
  toFun x := ⟨!![1, x.toAdd; 0, 1], by simp⟩
  map_one' := Subtype.ext (by simp [Matrix.one_fin_two])
  map_mul' x y := Subtype.ext (by
    change _ = !![1, x.toAdd; 0, 1] * !![1, y.toAdd; 0, 1]
    simp [add_comm])
def dia : Rˣ →* SL(2, R) where
  toFun u := ⟨!![u.1, 0; 0, (u⁻¹).1], by simp⟩
  map_one' := Subtype.ext (by simp [Matrix.one_fin_two])
  map_mul' x y := Subtype.ext (by
    change _ = !![x.1, 0; 0, (x⁻¹).1] * !![y.1, 0; 0, (y⁻¹).1]
    simp [mul_comm])
variable [TopologicalSpace R] [IsTopologicalRing R]
end Ring
end PositivityTheory.ThKEnd.Two
end


