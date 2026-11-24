-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:21.156685+00:00
-- url     : https://prove2.me/theorems/4b787154-6287-4cae-a3c4-98f095299a37
-- title:
--   Cfun Om Eta Log Period Neg Conj Pf
-- statement:
--   Definitions and structural lemmas for Cfun Om Eta Log Period Neg Conj Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmEtaLogPeriodNegConjPf.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_etaPeriod_pos_b13a4c259a1a

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
open UpperHalfPlane ModularForm Complex
open scoped Real
example : 0 < etaPeriod (negConj UpperHalfPlane.I) := etaPeriod_pos _
end GroundTheory.Heights₂.Theta


