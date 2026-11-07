-- Prove2me | Definitions.Def_EffHorizonProphet_cGamma
-- name    : EffHorizonProphet_cGamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:12.77009+00:00
-- url     : https://prove2.me/theorems/efdbfbd1-b9de-4ac5-86c8-028b5de9fa45
-- title:
--   The average decay weight $c_{\tilde\gamma}$
-- statement:
--   The **average decay weight** is
--   $$c_{\tilde\gamma}=\frac1S\sum_{s=1}^S\tilde\gamma^{\,s-1},$$
--   with $\tilde\gamma^0=1$ also at $\tilde\gamma=0$. It equals $\frac{1-\tilde\gamma^S}{S(1-\tilde\gamma)}$ for $\tilde\gamma<1$ and $1$ for $\tilde\gamma=1$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (19), p.22

import Mathlib

namespace EffHorizonProphet

/-- The average decay weight `c_γ̃ = (1/S) ∑_{s=1}^S γ̃^{s-1}` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Eq. (19), p.22).

**Formalization Note** `0 ^ 0 = 1` gives `c_0 = 1/S`, which is the value of the closed form on the
page at `γ̃ = 0`. -/
noncomputable def cGamma (S : ℕ) (γ : ℝ) : ℝ :=
  (1 / (S : ℝ)) * ∑ s ∈ Finset.range S, γ ^ s

end EffHorizonProphet


