-- Prove2me | Definitions.Def_DelayImpulse_Optimal_Model
-- name    : DelayImpulse_Optimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:38.146071+00:00
-- url     : https://prove2.me/theorems/79ea766d-c803-4780-83cf-2346e7b515b7
-- title:
--   §3, pp. 3–4, (3.1), Assumption 3.1 — data, standing hypotheses, delayed impulse strategies, admissible set 𝒜, controlled process L^δ, reward J
-- statement:
--   The model of delayed impulse control with random coefficients.
--
--   **Data.** A finite nonempty set of impulses $U=\{\beta_1,\dots,\beta_p\}\subset\mathbb R^l$, an execution delay $\Delta>0$, a discount rate $r>0$, a fixed intervention cost $k>0$ and a variable cost $\varphi\ge0$ on $U$, so that an impulse $\beta$ costs
--   $$\psi(\beta)=k+\varphi(\beta).$$
--   The uncontrolled system is an $\mathbb R^l$-valued progressively measurable process $L=(L_t)_{t\ge0}$, and the running reward $h(t,\omega,x)$ is $\mathcal P\otimes\mathcal B(\mathbb R^l)$-measurable ($\mathcal P$ the progressive $\sigma$-algebra) with $0\le h(t,\omega,x)\le\gamma$ for all $(t,x)$, $P$-a.s. (Assumption 3.1). These hypotheses, for a filtration $(\mathcal F_t)$, are collected in the predicate *IsStanding*.
--
--   **Strategies.** A strategy $\delta=(\tau_n,\xi_n)_{n\ge0}$ consists of decision times $\tau_n\in[0,+\infty]$ and impulses $\xi_n$. It is *admissible*, $\delta\in\mathcal A$, if every $\tau_n$ is an $(\mathcal F_t)$-stopping time, every $\xi_n$ is $\mathcal F_{\tau_n}$-measurable with values in $U$, and $\tau_{n+1}-\tau_n\ge\Delta$ a.s. The impulse $\xi_n$ decided at $\tau_n$ is executed at $\tau_n+\Delta$, so the controlled process is
--   $$L^\delta_t=L_t+\sum_{n\ge0}\xi_n\,\mathbf 1_{[\tau_n+\Delta\le t]}.$$
--
--   **Reward** (3.1):
--   $$J(\delta)=\mathbb E\Big[\int_0^\infty e^{-rs}h(s,L^\delta_s)\,ds-\sum_{n\ge0}e^{-r(\tau_n+\Delta)}\psi(\xi_n)\Big].$$
--
--   These objects are the model on which the scheme and Theorem 6.1 are stated.
--
--   **Formalization Note** $\mathbb R^l$ is `Fin l → ℝ` and $U$ is a `Finset`. Strategies are indexed from $0$: index $0$ is the paper's first decision $(\tau_1,\xi_1)$ of §3 and $(\tau^*_0,\beta^*_0)$ of §6. Times are in `WithTop ℝ≥0`, and $e^{-r\cdot(+\infty)}=0$ (`disc`). The sums in $L^\delta$ and $J$ are `tsum`s; on the full-measure set where all gaps $\tau_{n+1}-\tau_n\ge\Delta$ hold they have finitely many nonzero terms (for $L^\delta$) or are dominated by $\max_U|\psi|\sum_n e^{-rn\Delta}$ (for $J$). The measurability of $h$ is stated on $[0,t]\times\Omega\times\mathbb R^l$ with $\mathcal B([0,t])\otimes\mathcal F_t\otimes\mathcal B(\mathbb R^l)$ for every $t$.
-- source:
--   Djehiche, Hamadène, Hdhiri & Zaatra, Infinite Horizon Stochastic Impulse Control with Delay and Random Coefficients, arXiv:1904.11924v2, pp. 2–4, §2–§3, (3.1), Assumption 3.1

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting

namespace DelayImpulse.Optimal

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

/-- The data of §3 (pp. 3–4): the finite impulse set `U = {β₁, …, β_p} ⊂ ℝ^l`, the execution
delay `Δ`, the discount factor `r`, the fixed cost `k`, the variable cost `φ` (used on `U`), the
bound `γ` of Assumption 3.1 i), the running reward `h(t, ω, x)` and the uncontrolled process `L`.
`ℝ^l` is `Fin l → ℝ`. The hypotheses on these data are collected in `IsStanding`. -/
structure Data (Ω : Type) (l : ℕ) where
  U : Finset (Fin l → ℝ)
  Δ : ℝ≥0
  r : ℝ
  k : ℝ
  φ : (Fin l → ℝ) → ℝ
  γ : ℝ
  h : ℝ≥0 → Ω → (Fin l → ℝ) → ℝ
  L : ℝ≥0 → Ω → (Fin l → ℝ)

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {l : ℕ}

/-- The intervention cost `ψ(β) = k + φ(β)` (p. 4, ii)). -/
def Data.ψ (D : Data Ω l) (β : Fin l → ℝ) : ℝ := D.k + D.φ β

/-- The discount factor at a time in `[0, +∞]`: `e^{−rt}` for finite `t`, and `e^{−r·(+∞)} = 0`. -/
noncomputable def disc (r : ℝ) : WithTop ℝ≥0 → ℝ
  | ⊤ => 0
  | (t : ℝ≥0) => Real.exp (-r * t)

/-- The standing hypotheses of §2–§3 and Assumption 3.1 (pp. 2–4) for the filtration `𝓕`:
`U` finite (by its type) and nonempty, `Δ > 0`, `r > 0`, `k > 0`, `φ ≥ 0` on `U`, `L`
progressively measurable, `h` measurable for `𝒫 ⊗ ℬ(ℝ^l)` (on `[0, t] × Ω × ℝ^l` it is
`ℬ([0, t]) ⊗ 𝓕_t ⊗ ℬ(ℝ^l)`-measurable for every `t`), and, `P`-a.s., `0 ≤ h(t, ω, x) ≤ γ` for
all `(t, x)`. -/
structure IsStanding (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (D : Data Ω l) : Prop where
  U_nonempty : D.U.Nonempty
  Δ_pos : 0 < D.Δ
  r_pos : 0 < D.r
  k_pos : 0 < D.k
  φ_nonneg : ∀ β ∈ D.U, 0 ≤ D.φ β
  L_prog : IsStronglyProgressive 𝓕 D.L
  h_meas : ∀ t : ℝ≥0,
    @Measurable (Iic t × Ω × (Fin l → ℝ)) ℝ
      (@Prod.instMeasurableSpace (Iic t) (Ω × (Fin l → ℝ)) Subtype.instMeasurableSpace
        (@Prod.instMeasurableSpace Ω (Fin l → ℝ) (𝓕 t) (borel (Fin l → ℝ))))
      (borel ℝ) (fun p => D.h p.1 p.2.1 p.2.2)
  h_bound : ∀ᵐ ω ∂P, ∀ t x, 0 ≤ D.h t ω x ∧ D.h t ω x ≤ D.γ

/-- A strategy of impulse control `δ = (τₙ, ξₙ)`. **Index 0 is the first decision** (§3's
`(τ₁, ξ₁)`, §6's `(τ*₀, β*₀)`). Decision times lie in `[0, +∞]`. -/
structure Strategy (Ω : Type) (l : ℕ) where
  τ : ℕ → Ω → WithTop ℝ≥0
  ξ : ℕ → Ω → Fin l → ℝ

/-- The admissible strategies `𝒜` (pp. 3–4): each `τₙ` is an `𝓕`-stopping time, each `ξₙ` is
`𝓕_{τₙ}`-measurable with values in `U`, and `τₙ₊₁ − τₙ ≥ Δ` `P`-a.s. (so `0 ≤ τ₀ ≤ τ₁ ≤ ⋯`
a.s., since `Δ > 0`). -/
structure IsAdmissible (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (D : Data Ω l)
    (δ : Strategy Ω l) : Prop where
  stop : ∀ n, IsStoppingTime 𝓕 (δ.τ n)
  meas : ∀ n, Measurable[(stop n).measurableSpace] (δ.ξ n)
  mem : ∀ n ω, δ.ξ n ω ∈ D.U
  gap : ∀ n, ∀ᵐ ω ∂P, δ.τ n ω + (D.Δ : WithTop ℝ≥0) ≤ δ.τ (n + 1) ω

/-- The controlled process `L^δ_t = L_t + Σₙ ξₙ 1[τₙ + Δ ≤ t]` (p. 4). -/
noncomputable def ctrl (D : Data Ω l) (δ : Strategy Ω l) (t : ℝ≥0) (ω : Ω) : Fin l → ℝ :=
  D.L t ω + ∑' n, (if δ.τ n ω + (D.Δ : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) then δ.ξ n ω else 0)

/-- The reward (3.1): `J(δ) = E[∫₀^∞ e^{−rs} h(s, L^δ_s) ds − Σₙ e^{−r(τₙ+Δ)} ψ(ξₙ)]`. -/
noncomputable def J (P : Measure Ω) (D : Data Ω l) (δ : Strategy Ω l) : ℝ :=
  ∫ ω, ((∫ s in Ioi (0 : ℝ), Real.exp (-D.r * s) * D.h s.toNNReal ω (ctrl D δ s.toNNReal ω))
        - ∑' n, disc D.r (δ.τ n ω + (D.Δ : WithTop ℝ≥0)) * D.ψ (δ.ξ n ω)) ∂P

end DelayImpulse.Optimal


