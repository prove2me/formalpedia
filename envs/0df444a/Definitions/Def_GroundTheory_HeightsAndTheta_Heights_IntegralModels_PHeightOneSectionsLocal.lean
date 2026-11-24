-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneSectionsLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneSectionsLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:29:39.149889+00:00
-- url     : https://prove2.me/theorems/bf9de50b-038e-47c4-a99c-b30fe86b2401
-- title:
--   PHeight One Sections Local
-- statement:
--   Definitions and structural lemmas for PHeight One Sections Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace HeightOneSections
variable {X : Scheme.{0}} [IsIntegral X]
def comb (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W : X.Opens) (h : W ≤ V)
    (r : Fin n → Γ(X, W)) : Γ(E, W) :=
  ∑ i, r i • (E.presheaf.map (homOfLE h).op).hom (s i)
end HeightOneSections
end
end GroundTheory.Heights₂.Heights.Model


