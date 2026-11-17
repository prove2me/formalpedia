-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_cumScale
-- name    : EffHorizonProphet_Supplement_cumScale
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:59:17.797802+00:00
-- url     : https://prove2.me/theorems/69031757-e265-48b4-bb28-ab762735d96f
-- title:
--   Cumulative reward scale $\Gamma_s=\prod_{t\le s}\gamma_t$
-- statement:
--   For decay factors $\gamma_1,\gamma_2,\dots$, the **cumulative reward scale** is $\Gamma_0=1$ and $\Gamma_s=\prod_{t=1}^{s}\gamma_t$. Rewards in phase $s$ are $X_i=\Gamma_{s-1}Y_i$.
--
--   **Formalization Note** The decay factors are a sequence $g$ with $g(t)=\gamma_{t+1}$, and $\Gamma_s=\prod_{t<s}g(t)$. With $S$ phases only $g(0),\dots,g(S-2)$ are used.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.3; A.6, p.35

import Mathlib

namespace EffHorizonProphet.Supplement

/-- The **cumulative reward scale** `Γ_{s} = ∏_{t ∈ [s]} γ_t`, `Γ_0 = 1`, of the general
decaying-reward model (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 3, p.3; A.6, p.35).

**Formalization Note** The decay factors are a sequence `g : ℕ → ℝ` with the paper's
`γ_{t+1} = g t`; `cumScale g s = ∏_{t < s} g t` is the paper's `Γ_s`, and the scale of `0`-based
phase `s` (paper phase `s + 1`) is `cumScale g s`. With `S` phases only `g 0, …, g (S − 2)` are
ever used. -/
def cumScale (g : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∏ t ∈ Finset.range s, g t

end EffHorizonProphet.Supplement


