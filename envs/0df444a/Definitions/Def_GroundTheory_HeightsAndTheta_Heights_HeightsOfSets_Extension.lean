-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:30.507571+00:00
-- url     : https://prove2.me/theorems/aeb1efa6-99d5-4da9-a265-d21417e688ec
-- title:
--   Extension
-- statement:
--   Definitions and structural lemmas for Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open Matrix
open scoped ComplexOrder
noncomputable section
section GramGeometry
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
end GramGeometry
section GramGeometry2
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
instance hasOrthogonalProjection_span_range {ι : Type*} [Fintype ι] (v : ι → V) :
    (Submodule.span ℂ (Set.range v)).HasOrthogonalProjection := by
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range v)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  infer_instance
end GramGeometry2
end
end GroundTheory.Heights₂.Heights


