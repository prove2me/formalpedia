-- Prove2me | Definitions.Def_EffHorizonProphet_optRatio
-- name    : EffHorizonProphet_optRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:09.225207+00:00
-- url     : https://prove2.me/theorems/807abfa6-3355-4d0d-b02d-49841f0a0322
-- title:
--   The optimal single-quantile ratio $U(S,\tilde\gamma)$
-- statement:
--   The **optimal single-quantile ratio** is the common right-hand side of Theorems 1 and 6. With $r=\frac{1-\tilde\gamma}{1-\tilde\gamma^S}$,
--   $$U(S,\tilde\gamma)=\frac{\big(1-\tilde\gamma^S e^{-Sr}\big)\big(1-e^{-r}\big)}{1-\tilde\gamma e^{-r}}\quad(0\le\tilde\gamma<1),\qquad U(S,1)=1-\frac1e.$$
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Theorem 1, p.5; Theorem 6, p.9

import Mathlib

namespace EffHorizonProphet

/-- The **optimal single-quantile ratio**, the right-hand side of Theorem 1 (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.5) and of
Theorem 6 (p.9): `(1 - γ̃^S e^{-S r})(1 - e^{-r}) / (1 - γ̃ e^{-r})` with `r = (1-γ̃)/(1-γ̃^S)` for
`0 ≤ γ̃ < 1`, and `1 - 1/e` for `γ̃ = 1`. -/
noncomputable def optRatio (S : ℕ) (γ : ℝ) : ℝ :=
  if γ = 1 then 1 - Real.exp (-1)
  else (1 - γ ^ S * Real.exp (-((S : ℝ) * ((1 - γ) / (1 - γ ^ S))))) *
      (1 - Real.exp (-((1 - γ) / (1 - γ ^ S)))) /
    (1 - γ * Real.exp (-((1 - γ) / (1 - γ ^ S))))

end EffHorizonProphet


