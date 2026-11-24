-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:12:50.208839+00:00
-- url     : https://prove2.me/theorems/df32ad55-a808-463b-9d9a-ef1b56e567e2
-- title:
--   Dj Curve B
-- statement:
--   Definitions and structural lemmas for Dj Curve B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveB.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
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
namespace PI.UnitaryCorollaryDerivatives.DjC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
section Curve
variable {N j : ℕ}
end Curve
section Concrete
variable (k j ρ : ℕ)
def eR : Fin j ↪ Fin (2 * (j + ρ) + k + 1) :=
  ⟨fun a => ⟨a.val, by omega⟩, fun a b h => Fin.ext (Fin.mk.inj_iff.1 h)⟩
def eL : Fin j ↪ Fin (2 * (j + ρ) + k + 1) :=
  ⟨fun a => ⟨2 * (j + ρ) + k - a.val, by omega⟩, fun a b h => Fin.ext (by have h' := Fin.mk.inj_iff.1 h; omega)⟩
variable {k j ρ}
end Concrete
end PI.UnitaryCorollaryDerivatives.DjC


