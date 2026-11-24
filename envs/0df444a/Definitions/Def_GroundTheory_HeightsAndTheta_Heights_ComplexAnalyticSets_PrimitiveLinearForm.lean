-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:30.500344+00:00
-- url     : https://prove2.me/theorems/281644ef-d0bc-4856-941c-cb73b0bc5065
-- title:
--   Primitive Linear Form
-- statement:
--   Definitions and structural lemmas for Primitive Linear Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PrimitiveLinearForm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.ComplexSets
open Polynomial TensorProduct
noncomputable section
namespace PrimitiveLinearForm
variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
abbrev tensorRightAlgebra : Algebra B (FractionRing R ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
attribute [local instance] tensorRightAlgebra
end PrimitiveLinearForm
end
end GroundTheory.Heights₂.Heights.ComplexSets


