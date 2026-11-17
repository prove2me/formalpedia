-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_cumProp
-- name    : EffHorizonProphet_Supplement_cumProp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:59:37.237387+00:00
-- url     : https://prove2.me/theorems/95bc5fdf-80b5-457d-a97d-1d67a24382ac
-- title:
--   Cumulative phase proportion $\Lambda_{s-1}$
-- statement:
--   For phase proportions $\lambda_1,\dots,\lambda_S$, the **cumulative proportion** before phase $s$ is $\Lambda_{s-1}=\sum_{t=1}^{s-1}\lambda_t$, with $\Lambda_0=0$.
--
--   **Formalization Note** Phases are numbered from $0$; the Lean value at phase $s$ is $\sum_{r<s}\lambda_r$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), A.6, p.35

import Mathlib

namespace EffHorizonProphet.Supplement

/-- The **cumulative phase proportion** `Λ_{s−1} = ∑_{t=1}^{s−1} λ_t`, `Λ_0 = 0` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), A.6, p.35).

**Formalization Note** Phases are `0`-based: `cumProp lam s = ∑_{r < s} lam r` is the paper's
`Λ_{s}` for Lean phase `s`, i.e. `Λ_{s'−1}` for paper phase `s' = s + 1`. -/
def cumProp {S : ℕ} (lam : Fin S → ℝ) (s : Fin S) : ℝ :=
  ∑ r ∈ Finset.Iio s, lam r

end EffHorizonProphet.Supplement


