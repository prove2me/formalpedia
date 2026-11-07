-- Prove2me | Definitions.Def_EffHorizonProphet_IsEqualProfile
-- name    : EffHorizonProphet_IsEqualProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:49.102522+00:00
-- url     : https://prove2.me/theorems/72196d15-68cc-49fc-b83b-dade66945d3e
-- title:
--   Asymptotically equal phase profiles
-- statement:
--   A sequence of phase-length profiles $L_t$ is **asymptotically equal** if the horizon $n_t=\sum_sL_t(s)$ tends to infinity and $L_t(s)/n_t\to1/S$ for each phase $s$. The printed case $n_s=n/S$ is $L_t\equiv t$, along $n=St$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.3

import Mathlib

open Filter Topology

namespace EffHorizonProphet

/-- A sequence of **asymptotically equal phase profiles** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 3, p.3: `n_s = n/S` "(or
asymptotically `n_s/n → 1/S`)"): the horizon tends to infinity and each phase has asymptotic
share `1/S`.

**Formalization Note** `n → ∞` is a separate clause: `L ≡ 1` has the right shares with `n` bounded,
so constant profiles must be excluded. The canonical `L t = fun _ => t` (`n = S t`)
satisfies this (see the sanity file). -/
def IsEqualProfile {S : ℕ} (L : ℕ → Fin S → ℕ) : Prop :=
  Tendsto (fun t => ∑ s, L t s) atTop atTop ∧
    ∀ s, Tendsto (fun t => (L t s : ℝ) / ((∑ s', L t s' : ℕ) : ℝ)) atTop (𝓝 (1 / (S : ℝ)))

end EffHorizonProphet


