-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncIdealNeBotDim
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncIdealNeBotDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:08.113825+00:00
-- url     : https://prove2.me/theorems/531655b6-be65-4435-a115-25b86d41b057
-- title:
--   Statements Inc Ideal Ne Bot Dim
-- statement:
--   Definitions and structural lemmas for Statements Inc Ideal Ne Bot Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsIncIdealNeBotDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
def IncIdealNeBotDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsProjPrime Q →
    incIdeal Q k ≠ ⊥ → ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≤ ((k : ℕ) : WithBot ℕ∞)
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


