-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_WCoreDef
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalMassType_WCoreDef
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:10:03.54642+00:00
-- url     : https://prove2.me/theorems/b05d17a0-b46f-42ba-8af6-6a8329891962
-- title:
--   WCore Def
-- statement:
--   Definitions and structural lemmas for WCore Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalMassType/WCoreDef.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LocMassTypW
open Matrix
def WCore : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (n m : ℕ) (A0 A B0 B : Matrix (Fin n) (Fin m) O),
    (∃ L : Matrix (Fin m) (Fin n) O, L * A0 = 1) → (∃ L : Matrix (Fin m) (Fin n) O, L * A = 1) →
    (∃ L : Matrix (Fin m) (Fin n) O, L * B0 = 1) → (∃ L : Matrix (Fin m) (Fin n) O, L * B = 1) →
    A0ᵀ * B0 = Aᵀ * B →
    ∃ k : Matrix (Fin n) (Fin n) O, IsUnit k ∧ k * A0 = A ∧ kᵀ * B = B0
end PI.LocMassTypW


