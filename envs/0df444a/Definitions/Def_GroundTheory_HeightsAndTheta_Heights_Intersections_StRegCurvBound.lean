-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRegCurvBound
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StRegCurvBound
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:53:06.447799+00:00
-- url     : https://prove2.me/theorems/0eb5b243-13f7-4ba9-a3a4-7cbdf1bff7a8
-- title:
--   St Reg Curv Bound
-- statement:
--   Definitions and structural lemmas for St Reg Curv Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StRegCurvBound.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def RegCurvBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (E : HermLine ι) (t : MRing ι)
    (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a),
    IsSmoothHerm E → ∃ C : ℕ, ∀ ε : ℝ, 0 < ε →
      IsSemiPosHerm ((E.tensor (regLine E t ht ε)).tensor
        (HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun _ => (C : ℤ))))
end GroundTheory.Heights₂.Heights.Inter


