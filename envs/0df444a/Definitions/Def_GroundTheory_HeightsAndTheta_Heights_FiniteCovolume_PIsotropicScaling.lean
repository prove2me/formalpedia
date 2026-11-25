-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIsotropicScaling
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIsotropicScaling
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:46:58.308543+00:00
-- url     : https://prove2.me/theorems/564cc8e1-8938-5168-aa90-152bca1ebba9
-- title:
--   PIsotropic Scaling
-- statement:
--   Definitions and structural lemmas for PIsotropic Scaling, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
namespace IsotropicScaling
section Maps
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
def scalingMap (h : HermitianForm F E W) (v w : W) (α β : E) : W →ₗ[E] W :=
  LinearMap.id + α • (h.toSesq w).smulRight v + β • (h.toSesq v).smulRight w
variable (h : HermitianForm F E W) {v w : W}
variable (hvv : h.toSesq v v = 0) (hww : h.toSesq w w = 0) (hvw : h.toSesq v w = 1)
  (hwv : h.toSesq w v = 1)
include hvv hww hvw hwv
end Maps
section Lattice
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
end Lattice
section Main
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
end Main
end IsotropicScaling
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


