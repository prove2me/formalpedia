-- Prove2me | Definitions.Def_MLLangevin_ConvexA2_Multilevel
-- name    : MLLangevin_ConvexA2_Multilevel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:37.57321+00:00
-- url     : https://prove2.me/theorems/5e0976f0-94e7-4606-b06a-8b491e6ac821
-- title:
--   (7), (8), (H₁)–(H₄), (39)–(40), pp. 6–8, 26 — the multilevel occupation measure 𝒴, its cost, the assumptions (H₁)–(H₄) and the parameters of Theorem 2.1
-- statement:
--   This module defines the multilevel estimator of §2.2 of Egéa and Panloup, its cost, the assumptions $(\mathbf H_1)$–$(\mathbf H_4)$ of §2.3 for the additive Euler scheme, and the parameter formulas of Theorem 2.1.
--
--   Fix a drift $b$, a constant $\sigma$, a start $x_0\in\mathbb R^d$ and a family of $d$-dimensional processes $B^{(0)},B^{(1)},\dots$ (level $r$ is driven by $B^{(r)}$). Let $\gamma_r=\gamma_02^{-r}$, and for $\eta>0$ let $\underline s_\eta=\eta\lfloor s/\eta\rfloor$.
--
--   1. **The multilevel occupation measure** (7): for $R\in\mathbb N$, horizons $T_0,\dots,T_R$, a warm start $\tau$ and $f:\mathbb R^d\to\mathbb R$,
--   $$\mathcal Y(f)=\frac{1}{T_0-\tau}\int_\tau^{T_0}f\big(\bar X^{\gamma_0,x_0,B^{(0)}}_{\underline s_{\gamma_0}}\big)\,ds+\sum_{r=1}^R\frac{1}{T_r-\tau}\int_\tau^{T_r}\Big(f\big(\bar X^{\gamma_r,x_0,B^{(r)}}_{\underline s_{\gamma_{r-1}}}\big)-f\big(\bar X^{\gamma_{r-1},x_0,B^{(r)}}_{\underline s_{\gamma_{r-1}}}\big)\Big)ds .$$
--   Both schemes of level $r$ are driven by the same motion $B^{(r)}$, and the fine scheme is read on the coarse grid.
--   2. **The cost** (p. 6): $\mathcal C(\mathcal Y)=T_0/\gamma_0+\sum_{r=1}^R\big(T_r/\gamma_r+T_r/\gamma_{r-1}\big)$.
--   3. **$(\mathbf H_1)$**: for every level $r$, start $x$, step $\gamma\in(0,\eta_0]$, invariant probability $\pi^\gamma$ of the step-$\gamma$ chain and $n\ge0$: $\big|\mathbb E[f(\bar X^{\gamma,x}_{n\gamma})]-\pi^\gamma(f)\big|\le c_1(x)[f]_1e^{-\alpha n\gamma}$.
--   4. **$(\mathbf H_2)$**: $c_2>0$ and $\sup_{n}\|\bar X^{\gamma,x_0}_{n\gamma}-\bar X^{\gamma/2,x_0}_{n\gamma}\|_2\le c_2\gamma^{\mathfrak a/2}$ for every level and $\gamma\in(0,\eta_0]$.
--   5. **$(\mathbf H_3)$**: $c_3>0$ and $|\pi(f)-\pi^\gamma(f)|\le c_3[f]_1\gamma^\delta$ for every $\gamma\in(0,\eta_0]$ and every invariant probability $\pi^\gamma$.
--   6. **$(\mathbf H_4)$**: $c_4\ge0$ and $\sup_{t\ge0}\big(\|\bar X^{\gamma,x_0}_t-x_0\|_2+\|c_1(\bar X^{\gamma,x_0}_t)\|_2\big)\le c_4$ for every level and $\gamma\in(0,\eta_0]$, over all real times $t$ of the continuous-time scheme.
--   7. **Parameters** (8), (39), (40): $R_\varepsilon=\lceil\delta^{-1}\log_2(r_0\varepsilon^{-1})\rceil$; $T_r=\mathfrak t\varepsilon^{-2}2^{-\frac{1+\mathfrak a}{2}r}$ if $\mathfrak a>1$ and $T_r=\mathfrak t\varepsilon^{-2}R_\varepsilon^22^{-r}$ if $\mathfrak a=1$; $\mathfrak c_{\mathfrak a}=1+\frac32(2^{(\mathfrak a-1)/2}-1)^{-1}$ if $\mathfrak a>1$ and $\frac52$ if $\mathfrak a=1$; $\mathfrak d_{\mathfrak a}=(\mathfrak a-1)^{-2}$ if $\mathfrak a>1$ and $1$ if $\mathfrak a=1$; $\tau_1=(1+\mathfrak a-2\delta)/(\alpha\delta)$; $\tau_2=0\vee\alpha^{-1}\log\big(r_0^{\frac{1+\mathfrak a}{2\delta}}(\mathfrak d_{\mathfrak a}c_4)^{-1}\big)$.
--
--   The estimator and its cost are the object of the mission's goal; $(\mathbf H_1)$–$(\mathbf H_4)$ are the interface between the general complexity theorem of the paper and the strongly convex setting.
--
--   **Formalization Note** Norms $\|\cdot\|_2$ are `eLpNorm · 2 P` in $[0,\infty]$, so an infinite moment is never read as $0$. Time integrals are interval integrals of step functions of $s$. The cost formula is used for every $T_r$; the paper states it for $T_r$ multiples of the steps. In $(\mathbf H_1)$ and $(\mathbf H_3)$, $\pi^\gamma$ ranges over every invariant probability of the chain for which $f$ is integrable, and $(\mathbf H_1)$, $(\mathbf H_2)$, $(\mathbf H_4)$ are required for the motion of every level, as the proof of Theorem 2.1 applies them to each $B^{(r)}$.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, (7) and the cost, §2.2, p. 6; (H₁)–(H₄), §2.3, pp. 6–7; (8) and Theorem 2.1, pp. 7–8; (39)–(40), p. 26

import Mathlib
import Definitions.Def_MLLangevin_ConvexA2_Setting
import Definitions.Def_MLLangevin_ConvexA1_Setting
import Definitions.Def_MLLangevin_General_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MLLangevin.ConvexA2

open EthierKurtz

/-- The multilevel occupation measure (7), p. 6, applied to `f`, with steps `γ_r = γ₀ 2^{−r}`,
horizons `T r`, warm start `τ`, and level `r` driven by the Brownian motion `B r`:
`(T₀ − τ)⁻¹ ∫_τ^{T₀} f(X̄^{γ₀}_{s̲_{γ₀}}) ds + Σ_{r=1}^R (T_r − τ)⁻¹ ∫_τ^{T_r}
(f(X̄^{γ_r}_{s̲_{γ_{r−1}}}) − f(X̄^{γ_{r−1}}_{s̲_{γ_{r−1}}})) ds`. At time `s̲_η = η⌊s/η⌋` the
step-`γ_{r−1}` scheme is at index `⌊s/γ_{r−1}⌋` and the step-`γ_r` scheme at `2⌊s/γ_{r−1}⌋`. -/
noncomputable def estimator {Ω : Type*} {d : ℕ} (b : SDEState d → SDEState d) (σ : ℝ)
    (x₀ : SDEState d) (γ₀ : ℝ) (R : ℕ) (τ : ℝ) (T : ℕ → ℝ) (B : ℕ → ℝ≥0 → Ω → SDEState d)
    (f : SDEState d → ℝ) (ω : Ω) : ℝ :=
  (T 0 - τ)⁻¹ * ∫ s in τ..T 0, f (eulerChain b σ γ₀ x₀ (B 0) ⌊s / γ₀⌋₊ ω)
  + ∑ r ∈ Finset.Icc 1 R, (T r - τ)⁻¹ * ∫ s in τ..T r,
      (f (eulerChain b σ (γ₀ / 2 ^ r) x₀ (B r) (2 * ⌊s / (γ₀ / 2 ^ (r - 1))⌋₊) ω)
        - f (eulerChain b σ (γ₀ / 2 ^ (r - 1)) x₀ (B r) ⌊s / (γ₀ / 2 ^ (r - 1))⌋₊ ω))

/-- The cost of (7), p. 6: `𝒞(𝒴) = T₀/γ₀ + Σ_{r=1}^R (T_r/γ_r + T_r/γ_{r−1})`, `γ_r = γ₀ 2^{−r}`. -/
noncomputable def cost (R : ℕ) (γ₀ : ℝ) (T : ℕ → ℝ) : ℝ :=
  T 0 / γ₀ + ∑ r ∈ Finset.Icc 1 R, (T r / (γ₀ / 2 ^ r) + T r / (γ₀ / 2 ^ (r - 1)))

/-- (H₁), p. 6, for the additive scheme: for every level's motion `B r`, every start `x`,
every `γ ∈ (0, η₀]`, every invariant probability `πγ` of the step-`γ` chain (with `f`
`πγ`-integrable) and every `n`,
`|𝔼[f(X̄^{γ,x}_{nγ})] − πγ(f)| ≤ c₁(x) [f]₁ e^{−α nγ}`. -/
def H1 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) (b : SDEState d → SDEState d)
    (σ : ℝ) (B : ℕ → ℝ≥0 → Ω → SDEState d) (f : SDEState d → ℝ) (α η₀ : ℝ)
    (c₁ : SDEState d → ℝ) : Prop :=
  ∀ (r : ℕ) (x : SDEState d) (γ : ℝ), 0 < γ → γ ≤ η₀ →
    ∀ πγ : Measure (SDEState d), IsProbabilityMeasure πγ → IsInvChain b σ γ πγ →
      Integrable f πγ → ∀ n : ℕ,
        |∫ ω, f (eulerChain b σ γ x (B r) n ω) ∂P - ∫ y, f y ∂πγ|
          ≤ c₁ x * MLLangevin.ConvexA1.lipConst f * Real.exp (-α * (n * γ))

/-- (H₂), p. 7: `c₂ > 0` and for every level's motion `B r`, every `γ ∈ (0, η₀]` and every `n`,
`‖X̄^{γ,x₀}_{nγ} − X̄^{γ/2,x₀}_{nγ}‖₂ ≤ c₂ γ^{𝔞/2}` (both schemes driven by `B r`). -/
def H2 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) (b : SDEState d → SDEState d)
    (σ : ℝ) (B : ℕ → ℝ≥0 → Ω → SDEState d) (x₀ : SDEState d) (η₀ 𝔞 c₂ : ℝ) : Prop :=
  0 < c₂ ∧ ∀ (r : ℕ) (γ : ℝ), 0 < γ → γ ≤ η₀ → ∀ n : ℕ,
    eLpNorm (fun ω => eulerChain b σ γ x₀ (B r) n ω - eulerChain b σ (γ / 2) x₀ (B r) (2 * n) ω)
        2 P ≤ ENNReal.ofReal (c₂ * γ ^ (𝔞 / 2))

/-- (H₃), p. 7: `c₃ > 0` and for every `γ ∈ (0, η₀]` and every invariant probability `πγ` of the
step-`γ` chain (with `f` `πγ`-integrable), `|π(f) − πγ(f)| ≤ c₃ [f]₁ γ^δ`. -/
def H3 {d : ℕ} (b : SDEState d → SDEState d) (σ : ℝ) (f : SDEState d → ℝ)
    (π : Measure (SDEState d)) (η₀ δ c₃ : ℝ) : Prop :=
  0 < c₃ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ η₀ →
    ∀ πγ : Measure (SDEState d), IsProbabilityMeasure πγ → IsInvChain b σ γ πγ →
      Integrable f πγ →
        |∫ y, f y ∂π - ∫ y, f y ∂πγ| ≤ c₃ * MLLangevin.ConvexA1.lipConst f * γ ^ δ

/-- (H₄), p. 7: `c₄ ≥ 0` and for every level's motion `B r`, every `γ ∈ (0, η₀]` and every
`t ≥ 0`, `‖X̄^{γ,x₀}_t − x₀‖₂ + ‖c₁(X̄^{γ,x₀}_t)‖₂ ≤ c₄` (genuine continuous-time scheme). -/
def H4 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) (b : SDEState d → SDEState d)
    (σ : ℝ) (B : ℕ → ℝ≥0 → Ω → SDEState d) (x₀ : SDEState d) (η₀ : ℝ)
    (c₁ : SDEState d → ℝ) (c₄ : ℝ) : Prop :=
  0 ≤ c₄ ∧ ∀ (r : ℕ) (γ : ℝ), 0 < γ → γ ≤ η₀ → ∀ t : ℝ≥0,
    eLpNorm (fun ω => eulerCont b σ γ x₀ (B r) t ω - x₀) 2 P
      + eLpNorm (fun ω => c₁ (eulerCont b σ γ x₀ (B r) t ω)) 2 P ≤ ENNReal.ofReal c₄

/-- `𝔠_𝔞 = 1 + (3/2)(2^{(𝔞−1)/2} − 1)⁻¹` if `𝔞 > 1`, `5/2` if `𝔞 = 1` (Theorem 2.1, p. 8). -/
noncomputable def ca (𝔞 : ℝ) : ℝ :=
  if 1 < 𝔞 then 1 + 3 / 2 * ((2 : ℝ) ^ ((𝔞 - 1) / 2) - 1)⁻¹ else 5 / 2

/-- `τ₁ = (1 + 𝔞 − 2δ)/(αδ)` ((40), p. 26). -/
noncomputable def tau1 (𝔞 δ α : ℝ) : ℝ :=
  (1 + 𝔞 - 2 * δ) / (α * δ)

end MLLangevin.ConvexA2


