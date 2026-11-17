-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_normEffHorizon
-- name    : EffHorizonProphet_Supplement_normEffHorizon
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:00:06.812055+00:00
-- url     : https://prove2.me/theorems/4e34b8ea-8de7-4228-ab7a-0118934e6769
-- title:
--   Normalized effective horizon $C_S$
-- statement:
--   The **normalized effective horizon** is
--   $$C_S=\sum_{t=1}^{S}\Gamma_{t-1}\lambda_t,$$
--   the limit of $B_G/n$ when $n_s/n\to\lambda_s$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), A.6, p.35

import Mathlib
import Definitions.Def_EffHorizonProphet_Supplement_cumScale

namespace EffHorizonProphet.Supplement

/-- The **normalized effective horizon** `C_S = ∑_{t=1}^{S} Γ_{t−1} λ_t` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), A.6, p.35), the limit
of `B_G / n`.

**Formalization Note** `0`-based phases: `∑_s cumScale g s · lam s`. -/
noncomputable def normEffHorizon {S : ℕ} (g : ℕ → ℝ) (lam : Fin S → ℝ) : ℝ :=
  ∑ s : Fin S, cumScale g (s : ℕ) * lam s

end EffHorizonProphet.Supplement


