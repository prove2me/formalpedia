-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCoefficientFieldOfCharZero
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCoefficientFieldOfCharZero
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:49.581354+00:00
-- url     : https://prove2.me/theorems/288f2596-2bd5-4348-8968-e54a9c8d493c
-- title:
--   Exists Coefficient Field Of Char Zero
-- statement:
--   Definitions and structural lemmas for Exists Coefficient Field Of Char Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCoefficientFieldOfCharZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CohenStructureFiniteOverNormalCompleteSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory.CohenRegular
section Field
open Polynomial
end Field
open MvPowerSeries GlobalTheory.CohenStructure
end GlobalTheory.CohenRegular


