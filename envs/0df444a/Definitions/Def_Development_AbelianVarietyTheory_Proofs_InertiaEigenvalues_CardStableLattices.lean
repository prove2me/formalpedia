-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLattices
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLattices
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:27:22.922395+00:00
-- url     : https://prove2.me/theorems/a3e186f0-ea3e-45c9-bf9d-11f3d6c86ce5
-- title:
--   Card Stable Lattices
-- statement:
--   Definitions and structural lemmas for Card Stable Lattices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardStableLattices.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableEqCardHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardCommMapsEqCardHomQuot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardKernelQuotOfBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapDetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeHomSubmoduleFgAndSpanEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetCommutatorMapEqCharpolyResultantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.StableLatCount
open GlobalTheory.UnitLemma Polynomial
end GlobalTheory.StableLatCount


