-- Prove2me | Definitions.Def_RiskDistMDP_DPP_drmInf
-- name    : RiskDistMDP_DPP_drmInf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:48.798931+00:00
-- url     : https://prove2.me/theorems/5757bbde-cab9-41d1-8fa6-8afa378a25a5
-- title:
--   Infinite-horizon dynamic risk measure $\varsigma^{\mathfrak X,\gamma}_{t,x,\infty}$ (2.13)
-- statement:
--   For $\sup_t\|Z_t\|_\infty<\infty$, $\gamma\in[0,1)$ and normalized $(\sigma_{t,x})$, the **infinite-horizon DRM** is
--   $$\varsigma^{\mathfrak X,\gamma}_{0,\infty}(\mathfrak Z):=\lim_{T\to\infty}\varsigma^{\mathfrak X,\gamma}_{0,T}(\mathfrak Z),\qquad \varsigma^{\mathfrak X,\gamma}_{t,x,\infty}(\mathfrak Z):=\lim_{T\to\infty}\varsigma^{\mathfrak X,\gamma}_{t,x,T}(\mathfrak Z),\quad(t,x)\in\mathbb N\times\mathbb X.$$
--   The time-0 value $\varsigma_{0,\infty}(\mathfrak C)$ of the cost process is the objective of the infinite-horizon problem (P).
--
--   **Formalization Note** The limits are `limUnder atTop` in `EReal`, pointwise in $(x,\omega)$. Where the sequence diverges the value is arbitrary; Lemma 2.9 states convergence under the paper's hypotheses.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, (2.13), p. 10

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_drm

set_option autoImplicit false

open MeasureTheory Filter

namespace RiskDistMDP.DPP

/-- The **infinite-horizon DRM** `ς^{𝔛,γ}_{t,x,∞}(ℨ) := lim_{T→∞} ς^{𝔛,γ}_{t,x,T}(ℨ)`,
`(t, x) ∈ ℕ × 𝕏` (arXiv:2203.09612v4, (2.13), p.10).

**Formalization Note** The limit is `limUnder atTop` in `EReal`, pointwise in `(x, ω)`. It is a
junk value where the sequence diverges; Lemma 2.9 (`lemma_2_9`) states convergence for `ℙ`-a.e.
`ω` and every `x` when `sup_t ‖Z_t‖_∞ < ∞`, `γ ∈ [0,1)` and `(σ_{t,x})` is normalized. -/
noncomputable def drmInf {Ω 𝕏 : Type*} [mΩ : MeasurableSpace Ω] (σ : ℕ → 𝕏 → Measure ℝ → EReal)
    (γ : ℝ) (Pr : Measure Ω) [IsFiniteMeasure Pr] (𝒰 : ℕ → MeasurableSpace Ω) (𝔛 : ℕ → Ω → 𝕏)
    (Z : ℕ → Ω → ℝ) (t : ℕ) (x : 𝕏) (ω : Ω) : EReal :=
  limUnder atTop fun T => drm σ γ Pr 𝒰 𝔛 Z T t x ω

/-- The infinite-horizon DRM at time `0`, `ς^{𝔛,γ}_{0,∞}(ℨ) := lim_{T→∞} ς^{𝔛,γ}_{0,T}(ℨ)`
(arXiv:2203.09612v4, (2.13), p.10), as a `limUnder atTop` in `EReal`; Lemma 2.9 states that the
limit exists. -/
noncomputable def drm0Inf {Ω 𝕏 : Type*} [mΩ : MeasurableSpace Ω] (σ0 : Measure ℝ → EReal)
    (σ : ℕ → 𝕏 → Measure ℝ → EReal) (γ : ℝ) (Pr : Measure Ω) [IsFiniteMeasure Pr]
    (𝒰 : ℕ → MeasurableSpace Ω) (𝔛 : ℕ → Ω → 𝕏) (Z : ℕ → Ω → ℝ) : EReal :=
  limUnder atTop fun T => drm0 σ0 σ γ Pr 𝒰 𝔛 Z T

end RiskDistMDP.DPP


