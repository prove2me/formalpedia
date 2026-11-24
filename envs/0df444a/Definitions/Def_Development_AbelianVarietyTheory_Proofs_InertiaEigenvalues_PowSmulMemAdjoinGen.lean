-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSmulMemAdjoinGen
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSmulMemAdjoinGen
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T14:55:55.827797+00:00
-- url     : https://prove2.me/theorems/41f001bf-fe99-48a6-b4fd-b82bb4a15823
-- title:
--   Pow Smul Mem Adjoin Gen
-- statement:
--   Definitions and structural lemmas for Pow Smul Mem Adjoin Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSmulMemAdjoinGen.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial
end GlobalTheory.UnitLemma.Desc


