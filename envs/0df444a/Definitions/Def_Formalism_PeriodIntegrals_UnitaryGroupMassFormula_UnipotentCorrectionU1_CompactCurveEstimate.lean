-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompactCurveEstimate
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompactCurveEstimate
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:13:51.196311+00:00
-- url     : https://prove2.me/theorems/f69e34fb-a5bd-40e8-bf8d-a29af1594b64
-- title:
--   Compact Curve Estimate
-- statement:
--   Definitions and structural lemmas for Compact Curve Estimate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompactCurveEstimate.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
namespace PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace LatticeLocalGlobalTheory
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CCA
variable {k r : ℕ}
def Good (k r n : ℕ) (w : List (Bool × B.Mat k r)) : Prop :=
  ∃ u v : List (B.Mat k r), (∀ X ∈ u, unitLie k r X) ∧ (∀ X ∈ v, unitLie k r X) ∧
    u.length + v.length ≤ n ∧ w = wL u ++ wR v
def cw (cost : B.Mat k r → ℕ) (w : List (Bool × B.Mat k r)) : ℕ := (w.map (fun x => cost x.2)).sum
end LatticeLocalGlobalTheory
end PI.UnitaryCorollaryDerivatives


