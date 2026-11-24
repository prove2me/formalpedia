-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:36.815033+00:00
-- url     : https://prove2.me/theorems/5c9862c2-e021-4a8e-9d72-3de0f048db8b
-- title:
--   St Pts Add First
-- statement:
--   Definitions and structural lemmas for St Pts Add First, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StPtsAddFirst.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
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
def PtsAddFirst.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (M N E : HermLine ι) (t : MRing ι),
    IsArithVar Q (e + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm M → IsSmoothHerm N →
    IsSmoothHerm E → IsSectionOn Q E t →
    ptsIntegral Q (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) (logNorm E t) =
      ptsIntegral Q (Fin.cons (fun z => Real.log (M.h z)) (pot L)) (logNorm E t) +
        ptsIntegral Q (Fin.cons (fun z => Real.log (N.h z)) (pot L)) (logNorm E t)
end GroundTheory.Heights₂.Heights.Inter


