-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleArith
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleArith
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:17.03605+00:00
-- url     : https://prove2.me/theorems/ddc7bbf1-da20-492e-850d-6c73a91705cf
-- title:
--   St Proj Bundle Arith
-- statement:
--   Definitions and structural lemmas for St Proj Bundle Arith, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StProjBundleArith.lean

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
def ProjBundleArith.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t : ℕ)
    (P : Ideal (MRing ι)) (d : ℕ) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin 2) (Fin N1) (FnField P)),
    IsArithVar P d → IsQuotRows P c m 2 → IsKerBasis P c B →
    IsArithVar (projBundleIdeal P B) (d + 1)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


