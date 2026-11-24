-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsInertAtOfUniqueUnramifiedPrime
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsInertAtOfUniqueUnramifiedPrime
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:58:53.840776+00:00
-- url     : https://prove2.me/theorems/253fbb01-b315-427d-b085-f6556d68a6ff
-- title:
--   Is Inert At Of Unique Unramified Prime
-- statement:
--   Definitions and structural lemmas for Is Inert At Of Unique Unramified Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsInertAtOfUniqueUnramifiedPrime.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
namespace GlobalTheory.SelfDualGenus
end GlobalTheory.SelfDualGenus


