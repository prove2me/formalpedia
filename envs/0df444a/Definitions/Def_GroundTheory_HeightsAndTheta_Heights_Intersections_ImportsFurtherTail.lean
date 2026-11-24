-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTail
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTail
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:57.786361+00:00
-- url     : https://prove2.me/theorems/61ddc706-9039-42e8-a5ff-a3c43151e9b3
-- title:
--   Imports Further Tail
-- statement:
--   Definitions and structural lemmas for Imports Further Tail, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsFurtherTail.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
def pointForm_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d n : ℕ)
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (g : ((Σ k', ι' k') → ℂ) → ℝ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') d → d < n + 1 →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
    ptsIntegral P' (fun j z => Real.log ((L' j).h z)) g = 0
end GroundTheory.Heights₂.Heights.Inter


