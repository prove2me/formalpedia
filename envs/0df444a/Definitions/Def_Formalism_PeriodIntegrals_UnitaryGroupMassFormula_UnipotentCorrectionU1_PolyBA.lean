-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:50:54.036801+00:00
-- url     : https://prove2.me/theorems/9c0e137c-70a3-4914-8c33-5c65c1340b85
-- title:
--   Poly BA
-- statement:
--   Definitions and structural lemmas for Poly BA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBA.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
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
section pb
variable {k r : ℕ}
def PG (e : ℝ) (f : B.Mat k r → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ ∀ n : ℕ, ∃ C : ℝ, ∀ w : List (Bool × B.Mat k r),
    (∀ x ∈ w, B.unitLie k r x.2) → w.length ≤ n → ∀ g ∈ B.GV k r, ‖Dw w f g‖ ≤ C * B.gN g ^ e
end pb
end PI.UnitaryCorollaryDerivatives


