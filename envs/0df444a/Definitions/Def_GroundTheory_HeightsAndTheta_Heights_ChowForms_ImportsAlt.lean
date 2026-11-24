-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsAlt
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:09.103934+00:00
-- url     : https://prove2.me/theorems/84124a5a-7e61-4d75-bc86-511f54defafe
-- title:
--   Imports Alt
-- statement:
--   Definitions and structural lemmas for Imports Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/ImportsAlt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
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
def AffineChartTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (n d : ℕ) (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (j : Fin n), IsProjPrime P →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞) → X j ∉ P →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹)) =
        ((d : ℕ) : Cardinal)
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


