-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:01.811854+00:00
-- url     : https://prove2.me/theorems/6d12977d-7c82-499f-baab-274823601857
-- title:
--   PPlucker Rel
-- statement:
--   Definitions and structural lemmas for PPlucker Rel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerRel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace PluckerRelations
section Homog
variable {K : Type*} [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
end Homog
variable {D : ℕ} (S : ProjectiveLineBundle D)
def wedgeVal (k m : S.κ) : S.Ω :=
  S.φ k (S.e 0) * S.φ m (S.e 1) - S.φ k (S.e 1) * S.φ m (S.e 0)
end PluckerRelations
end
end GroundTheory.Heights₂.Heights.Inter


