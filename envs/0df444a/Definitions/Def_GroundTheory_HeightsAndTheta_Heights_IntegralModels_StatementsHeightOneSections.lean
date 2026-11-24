-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsHeightOneSections
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsHeightOneSections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:08.063125+00:00
-- url     : https://prove2.me/theorems/2fe453e5-2fdf-44f2-a501-1917e78a302f
-- title:
--   Statements Height One Sections
-- statement:
--   Definitions and structural lemmas for Statements Height One Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsHeightOneSections.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
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
def HeightOneSections.Statement : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], IsNormalScheme X →
    ∀ (E : X.Modules), IsVectorBundle E →
    ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (v : E.presheaf.stalk (genericPoint X)),
      (∀ x : X, x ∈ U → ringKrullDim (X.presheaf.stalk x) = 1 → v ∈ genericImage E x) →
      ∃ s : Γ(E, U), E.presheaf.germ U (genericPoint X) hU s = v
end GroundTheory.Heights₂.Heights.Model


