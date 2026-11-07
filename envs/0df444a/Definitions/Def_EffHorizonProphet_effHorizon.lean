-- Prove2me | Definitions.Def_EffHorizonProphet_effHorizon
-- name    : EffHorizonProphet_effHorizon
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:55.925298+00:00
-- url     : https://prove2.me/theorems/5fd03815-78b5-438d-9d9d-4be0bb0662ee
-- title:
--   The effective horizon $B$
-- statement:
--   The **effective horizon** of a profile is
--   $$B=\sum_{s=1}^S n_s\,\tilde\gamma^{\,s-1}.$$
--   At equal phases $n_s=n/S$ it equals $\frac nS\big(1+\sum_{s=1}^{S-1}\tilde\gamma^s\big)=n/a$, with $a$ from (6).
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Remark 4, p.9; A.4, p.29

import Mathlib

namespace EffHorizonProphet

/-- The **effective horizon** `B = ∑_s n_s γ̃^{s-1}` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Remark 4, p.9; A.4, p.29). At
`L = fun _ => m` it is `(n/S)(1 + ∑_{s<S} γ̃^s) = n/a`, with `n = S m` and `a` from (6). -/
noncomputable def effHorizon {S : ℕ} (γ : ℝ) (L : Fin S → ℕ) : ℝ :=
  ∑ s, (L s : ℝ) * γ ^ (s : ℕ)

end EffHorizonProphet


