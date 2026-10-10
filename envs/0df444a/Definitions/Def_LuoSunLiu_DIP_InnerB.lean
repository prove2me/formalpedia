-- Prove2me | Definitions.Def_LuoSunLiu_DIP_InnerB
-- name    : LuoSunLiu_DIP_InnerB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:14:41.822981+00:00
-- url     : https://prove2.me/theorems/650979eb-2e75-49c1-8d5b-ccc678001e97
-- title:
--   pp. 11–15 — Inner Algorithm B: grid on G(θ̂), candidate prices 𝒮_t, UCB (2), β*_t, pricing PLB ξ_t, ξ*, 𝒜_t
-- statement:
--   This file defines one episode of Inner Algorithm B (Algorithm 3) of Luo, Sun and Liu, together with the perturbed-linear-bandit objects of the single-episode pricing problem.
--
--   Given an estimate $\hat\theta$ and a discretization number $d$, the interval $G(\hat\theta) = [-\|\hat\theta\|_1,\, p_{\max} + \|\hat\theta\|_1]$ is cut into $d$ equal pieces with midpoints
--   $$m_j = -\|\hat\theta\|_1 + \bigl(j - \tfrac12\bigr)\frac{p_{\max} + 2\|\hat\theta\|_1}{d}, \qquad j = 1, \dots, d.$$
--
--   1. The **candidate prices** of covariate $x_t$ are $m_j + x_t^\top\hat\theta$, and the **available arms** are $\mathcal B_t = \{j : m_j + x_t^\top\hat\theta \in (0, p_{\max})\}$.
--   2. With $\mathcal U_{\tau-1,j} = \{s < \tau : j_s = j\}$ (periods of the current episode only), the **UCB (2)** is
--   $$\mathrm{UCB}_\tau(1 - F(m_j)) = \frac{\sum_{s\in\mathcal U_{\tau-1,j}} p_s^2y_s}{\lambda + \sum_{s\in\mathcal U_{\tau-1,j}} p_s^2} + \sqrt{\frac{\beta_\tau}{\lambda + \sum_{s\in\mathcal U_{\tau-1,j}} p_s^2}} .$$
--   3. The confidence parameter
--   $$\beta^*_\tau = p_{\max}^2\Bigl(1 \vee \Bigl(\tfrac{1}{p_{\max}}\sqrt{\lambda d} + \sqrt{2\log(1/\delta) + d\log\tfrac{d\lambda + (\tau-1)p_{\max}^2}{d\lambda}}\Bigr)^2\Bigr).$$
--   4. A **run of Inner Algorithm B** on an episode occupying periods $s_0 + 1, \dots, s_0 + T_0$: at local time $\tau$ (period $t = s_0 + \tau$), the pulled arm $j_t$ is available and the price is $p_t = m_{j_t} + x_t^\top\hat\theta$; if some available arm has not been pulled earlier in the episode, $j_t$ is such an arm; otherwise $j_t$ maximizes $(m_j + x_t^\top\hat\theta)\,\mathrm{UCB}_\tau(1 - F(m_j))$ over the available arms. Every tie-breaking rule is allowed.
--   5. The **pricing PLB** (p. 14): $\xi_t = (1 - F(m_j + x_t^\top\hat\theta - x_t^\top\theta_0))_{j}$, $\xi^* = (1 - F(m_j))_j$, and $\mathcal A_t = \{p\,e_j : p = m_j + x_t^\top\hat\theta,\ j \in \mathcal B_t\}$.
--   6. The **discrete-part regret** $R_{T_0,1} = \sum_{t\le T_0}\bigl(\max_{j\in\mathcal B_t} f_{x_t^\top\theta_0}(m_j + x_t^\top\hat\theta) - f_{x_t^\top\theta_0}(p_t)\bigr)$ and the **cumulative regret** $R_T = \sum_{t \le T} r_t$.
--
--   Inner Algorithm B is the online-pricing half of the DIP policy; the single-episode bounds of Propositions 3–4 are statements about its runs.
--
--   **Formalization Note** Algorithm 3 is read with forced exploration of unpulled available arms, the convention Lemma 2 fixes ("we refer to Algorithms 3 and 5 as the ones mentioned in Lemma 2", p. 17); read literally, (2) gives a finite UCB to an unpulled arm, which is not what the proof of Lemma 2 uses (it sets $0/0 = +\infty$, p. 36). The paper's arm index $j \in \{1, \dots, d\}$ is Lean's `j : Fin d` plus one. The maximum over $\mathcal B_t$ is taken as $0$ when $\mathcal B_t$ is empty; the theorems assume $p_{\max} + 2\|\hat\theta\|_1 < d\,p_{\max}$, which makes $\mathcal B_t$ nonempty. $\lambda > 0$ in every theorem, so the UCB denominators are positive.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, pp. 11–13 (grid, 𝒮_t, ℬ_t, Algorithm 3), p. 14 (ξ_t, ξ*, Q_t, 𝒜_t), p. 15 ((2), β*_t, 𝒰_{t−1,j}), p. 17 (Lemma 2 convention), p. 18 (r_{t,1}, R_{T_0,1})

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_Model

open MeasureTheory

namespace LuoSunLiu.DIP

/-- The grid step `|G(θ̂)| / d = (p_max + 2‖θ̂‖₁) / d` of Algorithm 3 (pp. 11, 13), where
`G(θ̂) = [-‖θ̂‖₁, p_max + ‖θ̂‖₁]`. -/
noncomputable def gridStep {d0 : ℕ} (pmax : ℝ) (θh : Fin d0 → ℝ) (d : ℕ) : ℝ :=
  (pmax + 2 * l1 θh) / d

/-- The midpoint `m_j` of the `j`-th of the `d` equal subintervals of `G(θ̂)` (p. 11). The
paper's index `j ∈ {1, …, d}` is Lean's `j : Fin d` plus one:
`m_{j+1} = -‖θ̂‖₁ + (j + 1/2) · |G(θ̂)|/d`. -/
noncomputable def gridMid {d0 : ℕ} (pmax : ℝ) (θh : Fin d0 → ℝ) (d : ℕ) (j : Fin d) : ℝ :=
  -l1 θh + ((j : ℝ) + 1 / 2) * gridStep pmax θh d

/-- The candidate price `m_j + xᵀθ̂` of arm `j` for covariate `x` (p. 12). -/
noncomputable def gridPrice {d0 : ℕ} (pmax : ℝ) (θh : Fin d0 → ℝ) (d : ℕ) (j : Fin d)
    (x : Fin d0 → ℝ) : ℝ :=
  gridMid pmax θh d j + x ⬝ᵥ θh

/-- The available arm set `ℬ_t = {j ∈ [d] : m_j + x_tᵀθ̂ ∈ (0, p_max)}` (p. 12); the candidate
price set `𝒮_t` is its image under `gridPrice`. -/
noncomputable def avail {d0 : ℕ} (pmax : ℝ) (θh : Fin d0 → ℝ) (d : ℕ) (x : Fin d0 → ℝ) :
    Finset (Fin d) :=
  Finset.univ.filter (fun j => 0 < gridPrice pmax θh d j x ∧ gridPrice pmax θh d j x < pmax)

/-- `𝒰_{τ-1,i} = {s : 1 ≤ s ≤ τ - 1, j_s = i}` (p. 15) for the episode occupying the periods
`s0 + 1, s0 + 2, …` (local time `τ` is period `s0 + τ`): the periods of the current episode before
local time `τ` at which arm `i` was pulled. -/
def pullSet {d : ℕ} (j : ℕ → Fin d) (s0 τ : ℕ) (i : Fin d) : Finset ℕ :=
  (Finset.Ico (s0 + 1) (s0 + τ)).filter (fun s => j s = i)

/-- The UCB (2), p. 15, at local time `τ` of the episode starting after period `s0`:
`UCB_τ(1 - F(m_i)) = ∑_{s ∈ 𝒰} p_s² y_s / (λ + ∑_{s ∈ 𝒰} p_s²) + √(β / (λ + ∑_{s ∈ 𝒰} p_s²))`. -/
noncomputable def ucb {d : ℕ} (lam β : ℝ) (j : ℕ → Fin d) (p y : ℕ → ℝ) (s0 τ : ℕ)
    (i : Fin d) : ℝ :=
  (∑ s ∈ pullSet j s0 τ i, p s ^ 2 * y s) / (lam + ∑ s ∈ pullSet j s0 τ i, p s ^ 2) +
    Real.sqrt (β / (lam + ∑ s ∈ pullSet j s0 τ i, p s ^ 2))

/-- The confidence parameter of Inner Algorithm B (p. 15):
`β*_τ = p²_max (1 ∨ ((1/p_max)√(λd) + √(2 log(1/δ) + d log((dλ + (τ-1) p²_max)/(dλ))))²)`. -/
noncomputable def betaStar (pmax lam : ℝ) (d : ℕ) (δ : ℝ) (τ : ℕ) : ℝ :=
  pmax ^ 2 * max 1 (((1 / pmax) * Real.sqrt (lam * d) +
    Real.sqrt (2 * Real.log (1 / δ) +
      d * Real.log ((d * lam + ((τ : ℝ) - 1) * pmax ^ 2) / (d * lam)))) ^ 2)

/-- One episode of Inner Algorithm B (Algorithm 3, p. 13, with the UCB (2), read as fixed by
Lemma 2, p. 17) on a single sample path, for every tie-breaking rule. The episode occupies the
periods `s0 + 1, …, s0 + T₀`; at local time `τ ∈ [T₀]` (period `t = s0 + τ`) the arm `j_t` is
available and the posted price is `p_t = m_{j_t} + x_tᵀθ̂`; if some available arm has not been
pulled earlier in the episode, `j_t` is such an arm; otherwise `j_t` maximizes
`(m_j + x_tᵀθ̂) · UCB_τ(1 - F(m_j))` over the available arms, with confidence parameter `β τ`. -/
def IsInnerBRun {d0 d : ℕ} (pmax : ℝ) (θh : Fin d0 → ℝ) (lam : ℝ) (β : ℕ → ℝ) (s0 T0 : ℕ)
    (x : ℕ → Fin d0 → ℝ) (j : ℕ → Fin d) (p y : ℕ → ℝ) : Prop :=
  ∀ τ ∈ Finset.Icc 1 T0,
    j (s0 + τ) ∈ avail pmax θh d (x (s0 + τ)) ∧
    p (s0 + τ) = gridPrice pmax θh d (j (s0 + τ)) (x (s0 + τ)) ∧
    ((∃ i ∈ avail pmax θh d (x (s0 + τ)), pullSet j s0 τ i = ∅) →
      pullSet j s0 τ (j (s0 + τ)) = ∅) ∧
    ((∀ i ∈ avail pmax θh d (x (s0 + τ)), (pullSet j s0 τ i).Nonempty) →
      ∀ i ∈ avail pmax θh d (x (s0 + τ)),
        gridPrice pmax θh d i (x (s0 + τ)) * ucb lam (β τ) j p y s0 τ i ≤
          gridPrice pmax θh d (j (s0 + τ)) (x (s0 + τ)) * ucb lam (β τ) j p y s0 τ (j (s0 + τ)))

/-- The linear parameter `ξ_t` of the pricing PLB (p. 14):
`(ξ_t)_j = 1 - F(m_j + x_tᵀθ̂ - x_tᵀθ₀)`. -/
noncomputable def xiPricing {d0 : ℕ} (M : PricingModel d0) (θh : Fin d0 → ℝ) (d : ℕ)
    (x : Fin d0 → ℝ) : Fin d → ℝ :=
  fun j => 1 - M.F (gridMid M.pmax θh d j + x ⬝ᵥ θh - x ⬝ᵥ M.θ0)

/-- The central parameter `ξ* = (1 - F(m_1), …, 1 - F(m_d))` (p. 14). -/
noncomputable def xiStar {d0 : ℕ} (M : PricingModel d0) (θh : Fin d0 → ℝ) (d : ℕ) :
    Fin d → ℝ :=
  fun j => 1 - M.F (gridMid M.pmax θh d j)

/-- The action set `𝒜_t = {Q_t(p) : p ∈ 𝒮_t}` of the pricing PLB (p. 14), where
`Q_t(m_j + x_tᵀθ̂) = (m_j + x_tᵀθ̂) e_j`. -/
noncomputable def pricingActions {d0 : ℕ} (M : PricingModel d0) (θh : Fin d0 → ℝ) (d : ℕ)
    (x : Fin d0 → ℝ) : Finset (Fin d → ℝ) :=
  (avail M.pmax θh d x).image (fun j => Pi.single j (gridPrice M.pmax θh d j x))

/-- `max_{p ∈ 𝒮_t} p(1 - F(p - x_tᵀθ₀))`, the revenue of the discrete best price `p̃*_t`
(p. 17); value `0` if `𝒮_t` is empty. -/
noncomputable def bestGridRevenue {d0 : ℕ} (M : PricingModel d0) (θh : Fin d0 → ℝ) (d : ℕ)
    (x : Fin d0 → ℝ) : ℝ :=
  if h : (avail M.pmax θh d x).Nonempty then
    (avail M.pmax θh d x).sup' h
      (fun j => revenue M.F (x ⬝ᵥ M.θ0) (gridPrice M.pmax θh d j x))
  else 0

/-- The discrete-part regret `R_{T₀,1} = ∑_{t=1}^{T₀} r_{t,1}`, with
`r_{t,1} = p̃*_t(1 - F(p̃*_t - x_tᵀθ₀)) - p_t(1 - F(p_t - x_tᵀθ₀))` (p. 18). -/
noncomputable def discreteRegret {d0 : ℕ} (M : PricingModel d0) (θh : Fin d0 → ℝ) (d : ℕ)
    {Ω : Type*} (x : ℕ → Ω → Fin d0 → ℝ) (p : ℕ → Ω → ℝ) (T0 : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T0,
    (bestGridRevenue M θh d (x t ω) - revenue M.F (x t ω ⬝ᵥ M.θ0) (p t ω))

/-- The cumulative regret `R_T = ∑_{t=1}^T r_t` with `r_t` from (1), p. 7. -/
noncomputable def cumRegret {d0 : ℕ} (M : PricingModel d0) {Ω : Type*}
    (x : ℕ → Ω → Fin d0 → ℝ) (p : ℕ → Ω → ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, perRegret M (x t ω) (p t ω)

end LuoSunLiu.DIP


