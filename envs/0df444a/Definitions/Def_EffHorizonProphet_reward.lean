-- Prove2me | Definitions.Def_EffHorizonProphet_reward
-- name    : EffHorizonProphet_reward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:48.076234+00:00
-- url     : https://prove2.me/theorems/f54d10e5-c924-4a03-9b96-4cf6b80dbab3
-- title:
--   The observed reward $X_i$
-- statement:
--   The **observed reward** at stage $i\in T_s$ is $X_i=\tilde\gamma^{\,s-1}Y_i$, the base reward decayed by the common factor once per elapsed phase. In particular $X_i=Y_i$ in the first phase, also at $\tilde\gamma=0$ (with the convention $0^0=1$).
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.3

import Mathlib
import Definitions.Def_EffHorizonProphet_phaseOf

namespace EffHorizonProphet

/-- The **observed reward** `X_i = γ̃^{s-1} Y_i` for `i ∈ T_s` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 3, p.3).

**Formalization Note** With `0`-based phases the exponent is `phaseOf L i`. Lean's `0 ^ 0 = 1` gives
`Γ_0 = 1` at `γ̃ = 0`, as the page has it. -/
def reward {S : ℕ} (γ : ℝ) (L : Fin S → ℕ) (i : Fin (∑ s, L s))
    (ω : Fin (∑ s, L s) → ℝ × unitInterval) : ℝ :=
  γ ^ (phaseOf L i : ℕ) * (ω i).1

end EffHorizonProphet


