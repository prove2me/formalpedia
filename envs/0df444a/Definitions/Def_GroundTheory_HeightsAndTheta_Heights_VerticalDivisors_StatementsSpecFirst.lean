-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSpecFirst
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSpecFirst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:12.385992+00:00
-- url     : https://prove2.me/theorems/a49b51b3-608a-4959-b493-3f3ee5bb6ac2
-- title:
--   Statements Spec First
-- statement:
--   Definitions and structural lemmas for Statements Spec First, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/StatementsSpecFirst.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
def SpecFirstNeField.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → specFirst f u ≠ 0
end
end GroundTheory.Heights₂.Heights.Vertical


