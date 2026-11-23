-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IdealMulPrincipal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IdealMulPrincipal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:49.645142+00:00
-- url     : https://prove2.me/theorems/3f22f62f-5157-48e2-b567-237ead162d89
-- title:
--   Ideal Mul Principal
-- statement:
--   Definitions and structural lemmas for Ideal Mul Principal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/IdealMulPrincipal.lean

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
namespace PIW.AdelClassFin
open NumberField
open scoped nonZeroDivisors
def IdealBoundAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], ∃ B : ℕ, ∀ I : Ideal (𝓞 E), I ≠ ⊥ → ∃ c ∈ I, c ≠ 0 ∧ ∃ e : ℕ,
    1 ≤ e ∧ e ≤ B ∧ ∀ g ∈ I, ∃ q : 𝓞 E, (e : 𝓞 E) * g = c * q
end PIW.AdelClassFin


