-- Prove2me | Definitions.Def_NonstatNV_Model_perpPolicy
-- name    : NonstatNV_Model_perpPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:03:18.898603+00:00
-- url     : https://prove2.me/theorems/b8290642-b395-47f6-9cb1-759b374b489e
-- title:
--   The Prediction-Error-Robust Policy PERP (Algorithm 4)
-- statement:
--   Fix a horizon $T$, a variation parameter $v$, scaling constants $\kappa,\gamma$, predictions $a_t$ and an argmin selection. Let $n=\lceil\kappa T^{(1-v)/2}\rceil$ and $\hat\mu^{\mathrm{fixed}}_s=\frac1n\sum_{r=s-n}^{s-1}d_r$. The test **fires** at period $s\in\{n+1,\dots,T\}$ when
--
--   $$
--   \sum_{r=n+1}^{s}\big|a_r-\hat\mu^{\mathrm{fixed}}_r\big|\ \ge\ \big(\gamma\sqrt{\log T}+\sqrt\kappa+1\big)\,T^{(3+v)/4}.
--   $$
--
--   **PERP** plays the Prediction Policy ($\hat\mu_t=\mathrm{clamp}(a_t)$) in every period before the first firing period, and the Fixed-Time-Window Policy ($\hat\mu_t=\mathrm{clamp}(\hat\mu^{\mathrm{fixed}}_t)$) from the first firing period on; in both cases $q_t=\mathrm{sel}(\hat\mu_t,b_t,h_t)$. The order at period $t$ uses only $d_1,\dots,d_{t-1}$ and the predictions.
--
--   **Formalization Note** The printed `break` is read as "switch to the Fixed-Time-Window Policy for good", as in the proof of Theorem 2 ("after time $s$ we have $\pi^{PERP}=\pi^{fixed}$", p.50). The test uses the unrounded $a_s$ and $\hat\mu^{\mathrm{fixed}}_s$, as printed; $\log$ is the natural logarithm.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Algorithm 4, p.23; proof of Theorem 2, p.50

import Definitions.Def_NonstatNV_Model_clamp
import Definitions.Def_NonstatNV_windowSize
import Definitions.Def_NonstatNV_windowMean

namespace NonstatNV

open Classical in
/-- The Prediction-Error-Robust Policy PERP (Algorithm 4 of An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, p.23) with inputs `v`, `κ`,
`γ`, horizon `T`, predictions `a` and argmin selection `sel`. With `n = ⌈κT^{(1−v)/2}⌉` and
`μ̂^fixed_s = (1/n) Σ_{r=s−n}^{s−1} d_r`, the test fires at period `s ∈ {n+1, …, T}` when
  `Σ_{r=n+1}^{s} |a_r − μ̂^fixed_r| ≥ (γ √(log T) + √κ + 1) · T^{(3+v)/4}`.
Before the first firing period PERP plays the Prediction Policy (`μ̂_t = a_t` rounded to
`[μmin, μmax]`); from the first firing period `τ` on it plays the Fixed-Time-Window Policy
(`μ̂_t = μ̂^fixed_t` rounded to `[μmin, μmax]`). In both cases `q_t = sel μ̂_t b_t h_t`.

**Formalization Note** The printed `break` is read as "π_t = π^fixed_t from the firing time on", as
in the proof of Theorem 2 (p.50: "after time s we have π^PERP = π^fixed"). The test uses the
unrounded `a_s` and `μ̂^fixed_s`, as printed; the orders use the rounded estimates. The order at
period `t` depends on `d_1, …, d_{t−1}` only. `Real.log` is the natural logarithm. -/
noncomputable def Model.perpPolicy (M : Model) (sel : ℝ → ℝ → ℝ → ℝ) (b h a : ℕ → ℝ) (T : ℕ)
    (v κ γ : ℝ) : ℕ → (ℕ → ℝ) → ℝ :=
  fun t ω =>
    if ∃ s, windowSize T v κ + 1 ≤ s ∧ s ≤ t ∧ s ≤ T ∧
        (γ * Real.sqrt (Real.log T) + Real.sqrt κ + 1) * (T : ℝ) ^ ((3 + v) / 4) ≤
          ∑ r ∈ Finset.Icc (windowSize T v κ + 1) s, |a r - windowMean (windowSize T v κ) r ω|
    then sel (M.clamp (windowMean (windowSize T v κ) t ω)) (b t) (h t)
    else sel (M.clamp (a t)) (b t) (h t)

end NonstatNV


