-- Prove2me | Definitions.Def_SensitivityCampaign
-- name    : SensitivityCampaign
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-15T17:41:50.528998+00:00
-- url     : https://prove2.me/theorems/03e4f991-3dbc-4939-9604-12c013d52e73
-- title:
--   Asymptotic sensitivity separation exponent
-- statement:
--   An exponent a is achievable if, for every positive epsilon and every integer sensitivity threshold S ≥ 2, there is a total Boolean function f with s(f) ≥ S and bs(f) ≥ s(f)^(a−epsilon). The witnesses may depend on epsilon and S.
-- source:
--   https://github.com/bigospeedrun/site/issues/2

import Mathlib
import Definitions.Def_SensitivitySeparation

namespace SensitivityCampaign

def AchievesExponent (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ S : ℕ, 2 ≤ S →
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      S ≤ OAI.Paper320.sensitivity f ∧
      (OAI.Paper320.sensitivity f : ℝ) ^ (a - ε) ≤
        (OAI.Paper320.blockSensitivity f : ℝ)

end SensitivityCampaign


