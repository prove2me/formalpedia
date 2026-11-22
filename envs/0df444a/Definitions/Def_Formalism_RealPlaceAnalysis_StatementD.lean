-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_StatementD
-- name    : Formalism_RealPlaceAnalysis_StatementD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:24.347027+00:00
-- url     : https://prove2.me/theorems/350e56f7-1ca7-48cb-b526-833c7c073120
-- title:
--   Statement D
-- statement:
--   Definitions and structural lemmas for Statement D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/StatementD.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.REAL
def rhoS (n : ℕ) : Fin n → ℝ := fun a => ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ)
def OperatorMatrixNormSqBound : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (n : ℕ) (A p t : ℝ)
    (W' : H) (x z : Fin n → H) (R : Fin n → Fin n → H →L[ℂ] H),
    0 < A → 0 ≤ p → 0 ≤ t → p ≤ ‖W'‖ →
    (∀ a, z a = ∑ b, R a b (x b)) → (∀ a b, ‖R a b‖ ≤ 2 * (n : ℝ)) →
    A / 2 * ‖W'‖ ^ 2 ≤ ∑ a, ‖z a‖ ^ 2 →
    ∑ b, ‖x b‖ ^ 2 ≤ t * p →
    p ≤ 8 * (n : ℝ) ^ 4 * t / A
def DomCas : Prop :=
  ∀ (n : ℕ) (lam mu : Fin n → ℝ) (c : Fin n → Fin n → ℝ),
    Antitone lam → Antitone mu → (∀ a b, 0 ≤ c a b) →
    lam - mu = ∑ a, ∑ b, (if a < b then c a b • root a b else 0) →
    nsq (mu + rhoS n) ≤ nsq (lam + rhoS n)
end Formalism.REAL


