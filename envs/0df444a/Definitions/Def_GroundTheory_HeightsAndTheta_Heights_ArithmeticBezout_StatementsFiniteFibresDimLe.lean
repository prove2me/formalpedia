-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:32.540122+00:00
-- url     : https://prove2.me/theorems/6cb2dce4-6814-4534-8780-45b956724c3f
-- title:
--   Statements Finite Fibres Dim Le
-- statement:
--   Definitions and structural lemmas for Statements Finite Fibres Dim Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsFiniteFibresDimLe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
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
def FiniteFibresDimLe.Statement : Prop :=
  ∀ (n d : ℕ) (Q : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), Q.IsPrime →
    (∀ y : Fin d → ℂ, (ComplexSets.fibre Q A y).Finite) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) ≤ ((d : ℕ) : WithBot ℕ∞)
end GroundTheory.Heights₂.Heights


