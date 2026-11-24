-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PQuasiFiniteSheets
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PQuasiFiniteSheets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:31.681311+00:00
-- url     : https://prove2.me/theorems/eaeff7e4-92f9-4324-81c8-1999b067fe6f
-- title:
--   PQuasi Finite Sheets
-- statement:
--   Definitions and structural lemmas for PQuasi Finite Sheets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PQuasiFiniteSheets.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimePairMeetImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
namespace QuasiFiniteSheets
variable {n d : ℕ}
def HasSheetsOff (S : Set (Fin n → ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (c : MvPolynomial (Fin d) ℂ) : Prop :=
  ∀ y : Fin d → ℂ, eval y c ≠ 0 →
    ∃ (U : Set (Fin d → ℂ)) (N : ℕ) (s : Fin N → (Fin d → ℂ) → Fin n → ℂ),
      IsOpen U ∧ y ∈ U ∧ (∀ j, DifferentiableOn ℂ (s j) U) ∧
      ∀ y' ∈ U, (∀ j, s j y' ∈ {x | x ∈ S ∧ A.mulVec x = y'}) ∧
        Function.Injective (fun j => s j y') ∧
        {x | x ∈ S ∧ A.mulVec x = y'} ⊆ Set.range (fun j => s j y')
end QuasiFiniteSheets
end GroundTheory.Heights₂.Heights


