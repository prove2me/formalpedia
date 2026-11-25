-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_FdegScale
-- name    : Formalism_PeriodIntegrals_FdegScale
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:17:53.443084+00:00
-- url     : https://prove2.me/theorems/8037c1eb-433c-4a21-96c8-e04fe258bdcf
-- title:
--   Fdeg Scale
-- statement:
--   Definitions and structural lemmas for Fdeg Scale, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/FdegScale.lean

import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_HCFdeg
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
def FdegScale : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (s : NNReal), 0 < s → ∀ (lam : Fin n → ℝ), IsHCParam lam →
    ∃ d0 : ℝ, 0 < d0 ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (d : ℝ),
      IsDS ε lam σ → IsFdeg ((s : ENNReal) • muG ε) σ d → d = d0
end PI


