-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:37:09.153796+00:00
-- url     : https://prove2.me/theorems/17254c7c-5ab3-44eb-adfa-9c9fd7a21111
-- title:
--   Hpk Row Es I
-- statement:
--   Definitions and structural lemmas for Hpk Row Es I, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
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
namespace PI.MirrorSection₂
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
section Grp
variable {k r : ℕ}
def lowS (k r a : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) where
  carrier := {y | ∀ i : Fin (2 * r + k + 1), a ≤ i.val → y i = 0}
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c x hx i hi
    simp [hx i hi]
end Grp
end PI.MirrorSection₂


