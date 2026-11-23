-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_ClassNum
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_ClassNum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:49.207167+00:00
-- url     : https://prove2.me/theorems/968e4a5e-f0e6-4c50-8829-e50eb1b856f5
-- title:
--   Class Num
-- statement:
--   Definitions and structural lemmas for Class Num, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ImaginaryQuadraticClassBound/ClassNum.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors
namespace PI.RayBoundIQW
section Lattice
variable {R : Type*} [CommRing R]
def HData (I : Ideal R) (e1 e2 : R) (a c b : ℕ) : Prop :=
  0 < a ∧ 0 < c ∧ b < a ∧ ((a : ℤ) : R) * e1 ∈ I ∧ ((b : ℤ) : R) * e1 + ((c : ℤ) : R) * e2 ∈ I ∧
    (∀ n : ℕ, 0 < n → n < a → ((n : ℤ) : R) * e1 ∉ I) ∧
    (∀ n : ℕ, 0 < n → n < c → ∀ x : ℤ, (x : R) * e1 + ((n : ℤ) : R) * e2 ∉ I)
end Lattice
end PI.RayBoundIQW


