-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineNormalForm
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineNormalForm
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:53:46.307013+00:00
-- url     : https://prove2.me/theorems/e253d88e-facc-4a80-94bd-c106c2af3ae0
-- title:
--   PLine Normal Form
-- statement:
--   Definitions and structural lemmas for PLine Normal Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIdealClassesFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineCoeffsFG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsCommonMultiple
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
noncomputable section
namespace LineNormalForm
section Denominators
variable {E : Type*} [Field E] [NumberField E]
variable (E) in

def intMultiples (N : ℕ) : AddSubgroup E :=
  (integralClosure ℤ E).toSubring.toAddSubgroup.comap (AddMonoidHom.mulLeft ((N : E)⁻¹))
end Denominators
end LineNormalForm
open LineNormalForm
section NormalForm
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
end NormalForm
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


