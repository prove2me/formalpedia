-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:13:41.108191+00:00
-- url     : https://prove2.me/theorems/5231188f-0f12-4e9d-a3dc-73f130764398
-- title:
--   Poly BB
-- statement:
--   Definitions and structural lemmas for Poly BB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
namespace PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section pb2
variable {k r : ℕ}
def pbCo (a b : Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => g a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }
def pbCc (a b : Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => star (g a b), map_add' := fun _ _ => by simp, map_smul' := fun _ _ => by simp }
def pbVar (g : B.Mat k r) : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℂ :=
  Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))
end pb2
end PI.UnitaryCorollaryDerivatives


