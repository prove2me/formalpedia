-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:06:10.372193+00:00
-- url     : https://prove2.me/theorems/3ad4d746-2c0c-4491-a935-043e34c5fb67
-- title:
--   Exp Second Hermitian Mem Level
-- statement:
--   Definitions and structural lemmas for Exp Second Hermitian Mem Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSmoothness/ExpSecondHermitianMemLevel.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def SmoothG (k r : ℕ) (i : Fin (r + 1)) (c : Mx k r → ℂ) : Prop :=
  ∃ c' : Mx k r → ℂ, ContDiff ℝ ∞ c' ∧ ∀ x ∈ Glev k r i, c x = c' x
end Smooth
section Rd
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
end Rd
section Fold
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
def foldP (k r : ℕ) (i : Fin (r + 1)) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i))) (f : Mx k r → E) : Mx k r → E :=
  (l.map fun x => Top (EH k r) x.1 (posL k r i x.2.1) (posL k r i x.2.2)).foldr (fun T h => T h) f
end Fold
end Formalism.FourierDecayAlt.Q.TPresMain


