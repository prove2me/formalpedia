-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_ExistsOrthogonalFamily
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_ExistsOrthogonalFamily
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:20.898777+00:00
-- url     : https://prove2.me/theorems/2e48d8cf-3b5e-4b80-afe7-e51362f5d149
-- title:
--   Exists Orthogonal Family
-- statement:
--   Definitions and structural lemmas for Exists Orthogonal Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianDiagonalization/ExistsOrthogonalFamily.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_HermDiag
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
variable {E : Type} [Field E]
structure IsHermForm (σ : E →+* E) {V : Type} [AddCommGroup V] [Module E V]
    (h : V → V → E) : Prop where
  add : ∀ x y z, h x (y + z) = h x y + h x z
  smul : ∀ x (a : E) y, h x (a • y) = a * h x y
  herm : ∀ x y, h y x = σ (h x y)
section Form
variable {σ : E →+* E} {V : Type} [AddCommGroup V] [Module E V] {h : V → V → E}
end Form
end PI.UnitaryGroupMassFormula.HermConj


