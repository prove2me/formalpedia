-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:13:21.746126+00:00
-- url     : https://prove2.me/theorems/694b7c8e-630f-4cfc-bd57-77b6db383722
-- title:
--   Comp RB
-- statement:
--   Definitions and structural lemmas for Comp RB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CompRB.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
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
namespace PI.UnitaryCorollaryDerivatives.CRH
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
def cs (cost : Mat k r → ℕ) (w : List (Bool × Mat k r)) : ℕ := (w.map fun x => cost x.2).sum
def admitted (n : ℕ) (w : List (Bool × Mat k r)) : Prop :=
  ∃ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) ∧ (∀ X ∈ v, unitLie k r X) ∧ u.length + v.length ≤ n ∧
    w = wL u ++ wR v
end PI.UnitaryCorollaryDerivatives.CRH


