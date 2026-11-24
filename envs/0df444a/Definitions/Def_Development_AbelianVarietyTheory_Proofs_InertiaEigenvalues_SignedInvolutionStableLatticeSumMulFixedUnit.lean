-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SignedInvolutionStableLatticeSumMulFixedUnit
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SignedInvolutionStableLatticeSumMulFixedUnit
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:51:01.20522+00:00
-- url     : https://prove2.me/theorems/0a65bf13-0028-4654-a2a8-23dcf79d1403
-- title:
--   Signed Involution Stable Lattice Sum Mul Fixed Unit
-- statement:
--   Definitions and structural lemmas for Signed Involution Stable Lattice Sum Mul Fixed Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SignedInvolutionStableLatticeSumMulFixedUnit.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixedBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
namespace GlobalTheory.UnitLemma.Move
variable {K : UQ} (B : InvAlg K)
end GlobalTheory.UnitLemma.Move


