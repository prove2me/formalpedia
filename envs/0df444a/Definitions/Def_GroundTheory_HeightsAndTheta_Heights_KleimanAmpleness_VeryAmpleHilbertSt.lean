-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleHilbertSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleHilbertSt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:08:39.983814+00:00
-- url     : https://prove2.me/theorems/de6499c7-e63a-5da4-9072-ca09cf4808e0
-- title:
--   Very Ample Hilbert St
-- statement:
--   Definitions and structural lemmas for Very Ample Hilbert St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/VeryAmpleHilbertSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open Filter
noncomputable section
universe u w
def VeryAmpleHilbert.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ)
    (Nb : LineBundle k x), IsSubvar x (primeOf (S := k) x) e → IsVeryAmple Nb.toSubSystem →
    (∀ n : ℕ, FiniteDimensional k (Nb.toSubSystem.pow n).secs) ∧
    ∃ P : Polynomial ℚ, P.natDegree ≤ e ∧
      P.coeff e * (e.factorial : ℚ) =
        (interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) : ℚ) ∧
      ∀ᶠ n : ℕ in atTop, (Module.finrank k (Nb.toSubSystem.pow n).secs : ℚ) = P.eval (n : ℚ)
end
end GroundTheory.Heights₂.Heights.Kleiman


