-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:38:48.145209+00:00
-- url     : https://prove2.me/theorems/b24253bf-683c-4bf0-8d2a-4558d36ba177
-- title:
--   Transference Key
-- statement:
--   Definitions and structural lemmas for Transference Key, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/TransferenceKey.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
namespace PI
def TransferenceKey : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (lam : ℝ) (u : E), 0 < lam →
    (∀ y : E, (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) → ‖y‖ < lam →
      ∃ m : ℤ, inner ℝ u y = (m : ℝ)) →
    ∃ l ∈ Λ, ‖u - l‖ * lam ≤ (finrank ℝ E : ℝ) / 2
end PI


