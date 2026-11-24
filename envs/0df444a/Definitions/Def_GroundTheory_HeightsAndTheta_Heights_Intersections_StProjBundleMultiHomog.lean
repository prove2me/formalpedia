-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleMultiHomog
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleMultiHomog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:09.605151+00:00
-- url     : https://prove2.me/theorems/f0506604-d355-48db-b6cc-df6457179e7e
-- title:
--   St Proj Bundle Multi Homog
-- statement:
--   Definitions and structural lemmas for St Proj Bundle Multi Homog, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StProjBundleMultiHomog.lean

import Mathlib
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
def ProjBundleMultiHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t n : ℕ)
    (P : Ideal (MRing ι)) (d : ℕ) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)),
    IsArithVar P d → IsQuotRows P c m n → IsKerBasis P c B →
    IsMultiHomogIdeal (projBundleIdeal P B)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


