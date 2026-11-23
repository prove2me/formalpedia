-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:16.389203+00:00
-- url     : https://prove2.me/theorems/6f2646f0-a3ad-4040-a6ef-d6a96b9825e6
-- title:
--   Ind Apply One
-- statement:
--   Definitions and structural lemmas for Ind Apply One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndApplyOne.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__BrauerDegreeZero_fefd58e19a2fa426
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.BI
namespace GlobalTheory.BrauerZero
def D0 (G : Type) [Group G] : AddSubgroup (G → ℂ) :=
  AddSubgroup.closure {f | ∃ (H : Subgroup G) (χ : H →* ℂˣ),
    f = ind H (fun h => (χ h : ℂ)) - ind H (fun _ => 1)}
end GlobalTheory.BrauerZero


