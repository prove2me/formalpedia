-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:17.669282+00:00
-- url     : https://prove2.me/theorems/4fc49c88-9784-4005-99f5-fe55931e8ef8
-- title:
--   Cfun Om Class Period Inv Conj
-- statement:
--   Definitions and structural lemmas for Cfun Om Class Period Inv Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
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
namespace GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup ModularForm Complex NumberField Module
open scoped Real Modular MatrixGroups nonZeroDivisors
namespace ClassPeriodInv
variable {K : Type*} [Field K] [NumberField K]
abbrev intAut (g : K ≃ₐ[ℚ] K) : 𝓞 K ≃ₐ[ℤ] 𝓞 K :=
  (RingOfIntegers.mapRingEquiv g.toRingEquiv).toIntAlgEquiv
end ClassPeriodInv
end GroundTheory.Heights₂.Theta


