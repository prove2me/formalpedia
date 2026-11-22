-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitKron
-- name    : Formalism_PeriodIntegrals_UnitKron
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:30.868803+00:00
-- url     : https://prove2.me/theorems/859db871-5457-437f-a1e1-a5cd5551417b
-- title:
--   Unit Kron
-- statement:
--   Definitions and structural lemmas for Unit Kron, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitKron.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
open Matrix ComplexOrder
def UnitKron : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
  ∀ (k : ℕ) (J γ : Matrix (Fin k) (Fin k) E),
    (∀ φ : E →+* ℂ, (J.map φ).PosDef ∨ (-(J.map φ)).PosDef) →
    (γ.map c)ᵀ * J * γ = J → (∀ i, IsIntegral ℤ (γ.charpoly.coeff i)) →
    ∃ n : ℕ, 0 < n ∧ γ ^ n = 1
end PI


