-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HvecApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HvecApply
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T20:54:10.707372+00:00
-- url     : https://prove2.me/theorems/68be13f1-72d4-437d-8778-61c5f72f0fa2
-- title:
--   Hvec Apply
-- statement:
--   Definitions and structural lemmas for Hvec Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/HvecApply.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight
import Theorems.Thm_PI_SelfDualLoc_W_hform_add_right
import Theorems.Thm_PI_SelfDualLoc_W_hform_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
noncomputable section
namespace PI.SelfDualLoc.W
open PI.SelfDualLoc
def hvec {E : Type} [Field E] {n m : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) : (Fin n → E) →ₗ[E] (Fin m → E) where
  toFun y := fun i => hform σ J (x i) y
  map_add' y y' := by ext i; simp [hform_add_right]
  map_smul' c y := by ext i; simp [hform_smul_right]
end PI.SelfDualLoc.W


