-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Imports
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:49.840907+00:00
-- url     : https://prove2.me/theorems/a2892878-4331-40b3-85ab-7e50414f5aad
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/Imports.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
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
def ProjPrimeHasPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (W : Ideal (MvPolynomial (Fin n) F)), IsProjPrime W →
    ∃ x : Fin n → AlgebraicClosure F, x ≠ 0 ∧ ∀ q ∈ W, aeval x q = 0
end
end GroundTheory.Heights₂.Heights


