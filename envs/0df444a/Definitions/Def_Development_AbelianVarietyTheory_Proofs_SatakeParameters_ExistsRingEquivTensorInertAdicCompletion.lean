-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRingEquivTensorInertAdicCompletion
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRingEquivTensorInertAdicCompletion
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:58:46.500217+00:00
-- url     : https://prove2.me/theorems/df154472-a50a-4577-8638-59c1a2397048
-- title:
--   Exists Ring Equiv Tensor Inert Adic Completion
-- statement:
--   Definitions and structural lemmas for Exists Ring Equiv Tensor Inert Adic Completion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsRingEquivTensorInertAdicCompletion.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInert
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
namespace GlobalTheory.InertCompletion
end GlobalTheory.InertCompletion


