-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:39.411806+00:00
-- url     : https://prove2.me/theorems/64d78465-4a40-41e8-a9f8-7dc5b1e9a9b7
-- title:
--   GLeft Inv
-- statement:
--   Definitions and structural lemmas for GLeft Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
def UT (k r : ℕ) (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j : Fin (2 * r + k + 1),
    (j.val ≤ i.val ∨ (r ≤ i.val ∧ i.val ≤ r + k ∧ r ≤ j.val ∧ j.val ≤ r + k)) →
      a i j = if i = j then 1 else 0
def dd (k r : ℕ) (c : Fin r → ℂ) (j : Fin (2 * r + k + 1)) : ℂ :=
  if h : j.val < r then c ⟨j.val, h⟩
  else if h2 : r + k < j.val then (star (c ⟨2 * r + k - j.val, by omega⟩))⁻¹ else 0
end PI.StabBigW


