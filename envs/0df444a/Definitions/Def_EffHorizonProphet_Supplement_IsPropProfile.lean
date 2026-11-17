-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_IsPropProfile
-- name    : EffHorizonProphet_Supplement_IsPropProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:04:01.279574+00:00
-- url     : https://prove2.me/theorems/9737c507-f0d9-402b-984e-f4155167a6a4
-- title:
--   Phase profiles with asymptotic proportions $\lambda$
-- statement:
--   A sequence of phase-length profiles has **asymptotic proportions** $\lambda_1,\dots,\lambda_S$ if the horizon $n=\sum_sn_s$ tends to infinity and $n_s/n\to\lambda_s$ for every phase $s$.
--
--   **Formalization Note** With $\lambda_s=1/S$ it is the published `IsEqualProfile`. The clause $n\to\infty$ is stated separately.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), A.6, p.35

import Mathlib

open Filter Topology

namespace EffHorizonProphet.Supplement

/-- A sequence of phase profiles with **asymptotic phase proportions** `λ` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), A.6, p.35): the
horizon `n = ∑_s n_s` tends to infinity and `n_s / n → λ_s` for every phase `s`.

**Formalization Note** The base mission's `IsEqualProfile` with `1/S` replaced by `lam s`. The
clause `n → ∞` is separate, because constant profiles can have the right shares. -/
def IsPropProfile {S : ℕ} (lam : Fin S → ℝ) (L : ℕ → Fin S → ℕ) : Prop :=
  Tendsto (fun t => ∑ s, L t s) atTop atTop ∧
    ∀ s, Tendsto (fun t => (L t s : ℝ) / ((∑ s', L t s' : ℕ) : ℝ)) atTop (𝓝 (lam s))

end EffHorizonProphet.Supplement


