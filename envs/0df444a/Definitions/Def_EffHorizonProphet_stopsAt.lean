-- Prove2me | Definitions.Def_EffHorizonProphet_stopsAt
-- name    : EffHorizonProphet_stopsAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:34.49449+00:00
-- url     : https://prove2.me/theorems/da94618a-a3fa-4420-8b3d-2022ce200448
-- title:
--   The event $\tau=i$
-- statement:
--   The rule **stops at** stage $i$ if it accepts stage $i$ and accepts none of the earlier stages. This is the event $\{\tau=i\}$ of Algorithm 1.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Algorithm 1, p.9; Remark 16, p.31

import Mathlib
import Definitions.Def_EffHorizonProphet_Rule_Accepts

namespace EffHorizonProphet

/-- The event `τ = i` for the rule `ρ` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Algorithm 1, p.9; Remark 16, p.31): stage `i` is the
first stage whose acceptance event holds. -/
def stopsAt {n : ℕ} (ρ : Rule) (ω : Fin n → ℝ × unitInterval) (i : Fin n) : Prop :=
  ρ.Accepts (ω i).1 (ω i).2 ∧ ∀ j, j < i → ¬ ρ.Accepts (ω j).1 (ω j).2

end EffHorizonProphet


