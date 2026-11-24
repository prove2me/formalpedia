-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_DSExist
-- name    : Formalism_PeriodIntegrals_DSExist
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:49:15.374858+00:00
-- url     : https://prove2.me/theorems/97481fc1-1a99-49c5-ac11-1bac59595391
-- title:
--   DSExist
-- statement:
--   Definitions and structural lemmas for DSExist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/DSExist.lean

import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
open PI.UpqRep
def DSExist : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ
end PI


