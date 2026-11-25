-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSnapperSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSnapperSt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:23.310871+00:00
-- url     : https://prove2.me/theorems/362ef81e-a0a3-4f3a-967f-277bca97dd90
-- title:
--   Very Ample Snapper St
-- statement:
--   Definitions and structural lemmas for Very Ample Snapper St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/VeryAmpleSnapperSt.lean

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
def VeryAmpleSnapper.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ)
    (Nb : LineBundle k x), IsSubvar x (primeOf (S := k) x) e → IsVeryAmple Nb.toSubSystem →
    (∀ (a : ℕ) (c : ℤ), FiniteDimensional k (twistMul Nb.toSubSystem a c).secs) ∧
    ∃ (Q : MvPolynomial (Fin 2) ℚ) (c₀ : ℤ), Q.totalDegree ≤ e ∧
      (∀ (a : ℕ) (c : ℤ), c₀ ≤ c →
        (Module.finrank k (twistMul Nb.toSubSystem a c).secs : ℚ) = MvPolynomial.eval ![(a : ℚ), (c : ℚ)] Q) ∧
      ∀ᶠ a : ℕ in atTop,
        (Module.finrank k (Nb.toSubSystem.pow a).secs : ℚ) = MvPolynomial.eval ![(a : ℚ), 0] Q
end
end GroundTheory.Heights₂.Heights.Kleiman


