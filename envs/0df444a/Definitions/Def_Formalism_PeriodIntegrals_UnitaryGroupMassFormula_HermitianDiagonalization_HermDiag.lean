-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_HermDiag
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_HermDiag
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:34.00565+00:00
-- url     : https://prove2.me/theorems/7c10fcc9-9774-47a7-add8-90f254594302
-- title:
--   Herm Diag
-- statement:
--   Definitions and structural lemmas for Herm Diag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianDiagonalization/HermDiag.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_HermDefONFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.UnitaryGroupMassFormula.HermConj
open Matrix
def HermDiag : Prop :=
  ∀ (E : Type) [Field E] [CharZero E] (σ : E →+* E), (∀ x, σ (σ x) = x) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (J.map σ)ᵀ = J →
      ∃ (Q : Matrix (Fin n) (Fin n) E) (d : Fin n → E), IsUnit Q.det ∧ (∀ i, σ (d i) = d i) ∧
        J = (Q.map σ)ᵀ * diagonal d * Q
end PI.UnitaryGroupMassFormula.HermConj


