-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleDim
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:28.618924+00:00
-- url     : https://prove2.me/theorems/43d0c8f0-ca8f-4ed3-88c9-10a29588e90d
-- title:
--   PProj Bundle Dim
-- statement:
--   Definitions and structural lemmas for PProj Bundle Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
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
section Bundle
variable {K : Type} {ι : K → Type}
def projBundleAlgHom (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    MRing (PBlk ι N1) →ₐ[ℤ] MvPolynomial (Fin n) (FnField P) :=
  ⟨projBundleMap P B, fun r => by simp⟩
end Bundle
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


