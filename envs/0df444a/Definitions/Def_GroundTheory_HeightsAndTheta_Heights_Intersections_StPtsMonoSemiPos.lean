-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsMonoSemiPos
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsMonoSemiPos
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:20:28.282214+00:00
-- url     : https://prove2.me/theorems/c39d65cc-1755-5d8f-b567-2b00d42acf6a
-- title:
--   St Pts Mono Semi Pos
-- statement:
--   Definitions and structural lemmas for St Pts Mono Semi Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StPtsMonoSemiPos.lean

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
def PtsMonoSemiPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (M : Fin e → HermLine ι) (E D : HermLine ι) (t : MRing ι),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (M j)) → (∀ j, IsSemiPosHerm (M j)) →
    IsSmoothHerm E → IsSectionOn Q E t → IsSmoothHerm D → D.a = 0 →
    (∀ z ∈ mcPts Q, eval z (map (Int.castRingHom ℂ) t) ≠ 0 → logNorm E t z ≤ Real.log (D.h z)) →
    ptsIntegral Q (pot M) (logNorm E t) ≤ ptsIntegral Q (pot M) (fun z => Real.log (D.h z))
end GroundTheory.Heights₂.Heights.Inter


