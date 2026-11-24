-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:39.188752+00:00
-- url     : https://prove2.me/theorems/61ef522b-544d-4eb3-b850-f866d8394e4b
-- title:
--   Divided Power Zero Zero Vector
-- statement:
--   Definitions and structural lemmas for Divided Power Zero Zero Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
noncomputable def ldDet : MvPolynomial (Fin 2 × Fin 2) ℤ := X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0)
noncomputable def ldM (w y : ℕ) : Submodule ℤ (MvPolynomial (Fin 2 × Fin 2) ℤ) :=
  Submodule.span ℤ {v | ∃ j, y + j ≤ w ∧ v = ((w - y).choose j : ℤ) • vec2 w y j}
def ldZ (q : ℕ) : Fin (1 + q) := Fin.castAdd q (0 : Fin 1)
noncomputable def ldSv (q w : ℕ) (μ : Fin (1 + q) → ℕ) (S : Finset (Fin (1 + q))) :
    MvPolynomial (Fin (1 + q) × Fin (1 + q)) ℤ :=
  X (ldZ q, ldZ q) ^ (w - ∑ a ∈ S, μ a) * ∏ a ∈ S, X (a, ldZ q) ^ μ a
end Formalism.CohomologicalDescent.LD


