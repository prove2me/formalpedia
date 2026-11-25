-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartZeroTrdeg
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartZeroTrdeg
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:04:15.262937+00:00
-- url     : https://prove2.me/theorems/15e92744-1f86-4d47-9269-4133fa1d22c6
-- title:
--   Statements Chart Zero Trdeg
-- statement:
--   Definitions and structural lemmas for Statements Chart Zero Trdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsChartZeroTrdeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFormsThroughPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PComponentOfIncIdeal
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
def ChartZeroTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (n d : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsProjPrime Q →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞) →
    ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (y : Fin n → Ω) (j : Fin n),
      (∀ q ∈ Q, aeval y q = 0) → y j ≠ 0 →
        Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => y m * (y j)⁻¹)) ≤ (d : Cardinal)
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


