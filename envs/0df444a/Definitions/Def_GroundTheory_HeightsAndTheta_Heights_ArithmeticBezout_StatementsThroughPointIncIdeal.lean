-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughPointIncIdeal
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughPointIncIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:09.707922+00:00
-- url     : https://prove2.me/theorems/4a403840-2df3-4aee-b067-549bd2ab439b
-- title:
--   Statements Through Point Inc Ideal
-- statement:
--   Definitions and structural lemmas for Statements Through Point Inc Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsThroughPointIncIdeal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
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
def ThroughPointIncIdeal.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)) (x c : Fin n → AlgebraicClosure F),
    ∑ j, c j * x j = 1 →
    (∀ u : Fin k × Fin n → AlgebraicClosure F, (∀ i, ∑ j, u (i, j) * x j = 0) → u ∈ incidence Q k) →
      ∀ g ∈ incIdeal Q k, aeval (genSubst (k := k) x c) g = 0
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


