-- Prove2me | Definitions.Def_MenuCostPricing_DP
-- name    : MenuCostPricing_DP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:09.656685+00:00
-- url     : https://prove2.me/theorems/432cdd0f-6dfc-4bd1-a2ba-a048781f23e7
-- title:
--   §3.6–§3.7, pp.19–21 — grids $\mathcal D_\omega,\mathcal D_\rho$, rounding, $\mathcal F^i_0(\omega)$, the program $\hat{\mathcal V}$ (9)–(10), $\hat\rho$ (11), visited states (27)
-- statement:
--   With accuracy $\epsilon$, $\delta=\epsilon/(8\varrho_{\max})$, $\alpha=2\delta$, $\beta=\delta$. For a guess $(\Gamma,\hat w,\rho_{\mathrm{single}})$ the grids are
--   $$
--   \mathcal D^t_\omega=\Big\{k\cdot\frac{\delta\hat w_t}{n}:k=0,\dots,\Big\lceil\frac n\delta\Big\rceil\Big\},\qquad \mathcal D_\rho=\Big\{k\cdot\frac{\delta\rho_{\mathrm{single}}}{n}:k=0,\dots,\Big\lceil\frac{n^2}\delta\Big\rceil\Big\},
--   $$
--   with operators rounding down to the nearest grid point. $\mathcal F^i_0(\omega)$ is the set of price vectors $x_i$ of product $i$ with $\omega_t+w^t_{i,x^t_i}\le\hat w_t$ for all $t$ and $x^t_i=x^{t-1}_i$ for $t\notin\Gamma$; $\Delta^i(x_i)$ counts the price changes of $x_i$, and $w|_{x_i}=(w^t_{i,x^t_i})_t$. The approximate program is
--   $$
--   \hat{\mathcal V}(i,\omega,\rho)=\min_{x_i\in\mathcal F^i_0(\omega)}\Big\{v\,\Delta^i(x_i)+\hat{\mathcal V}\big(i+1,\mathcal D_\omega(\omega+w|_{x_i}),\rho-\mathcal D_\rho(\hat{\mathcal R}^i_{2\delta,\delta}(x_i))\big)\Big\}\quad(9)
--   $$
--   ($\infty$ when $\mathcal F^i_0(\omega)=\emptyset$), with $\hat{\mathcal V}(n+1,\omega,\rho)=0$ if $\rho\le0$ and $\omega_t\ge(1-2\delta)\hat w_t$ for all $t$, and $\infty$ otherwise (10). Then
--   $$
--   \hat\rho=\max\{\rho\in\mathcal D_\rho:\hat{\mathcal V}(1,\vec0,\rho)\le B-|\Gamma|f\}\quad(11).
--   $$
--   Following a strategy $x$ from $(1,\vec0,\rho)$ visits the states $\hat\omega^{(i)}=\mathcal D_\omega(\hat\omega^{(i-1)}+w|_{x_{i-1}})$, $\hat\rho^{(i)}=\hat\rho^{(i-1)}-\mathcal D_\rho(\hat{\mathcal R}^{i-1}_{2\delta,\delta}(x_{i-1}))$ (27).
--
--   These are the specifications against which the program's table and path are stated.
--
--   **Formalization Note** Grid states are index vectors: $\omega_t=k_{\omega,t}\cdot\delta\hat w_t/n$, $\rho=k_\rho\cdot\delta\rho_{\mathrm{single}}/n$; rounding down is $\min(K,\lfloor a/\mathrm{step}\rfloor)$, and a zero step gives index $0$. Products are 0-based (`Vhat i` is $\hat{\mathcal V}(i+1,\cdot,\cdot)$, `Vhat n` the base case). Values are in `WithTop ℝ`. The reward index is updated by truncated subtraction, i.e. clamped at $0$; the base case only asks $\rho\le0$. `deltaOf I ε` uses $\min(\epsilon,1)$ in place of $\epsilon$, so $\delta\le1/8$.
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), §3.3, p.15 (δ); §3.5, p.18 (Fⁱ_β(ω), ∆ⁱ, w|ₓᵢ); §3.6, pp.19–20 ((9), (10), Dω, Dρ); §3.7, p.21 ((11)); App. B.9, p.56 ((27))

import Mathlib
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy

namespace MenuCostPricing

variable {n L T : ℕ}

/-- The accuracy parameter `δ = (ϵ/8)·(1/ϱmax)` of §3.3, p.15, computed from `εh = min ε 1`.

**Formalization Note.** For `ε ≤ 1` this is the paper's `δ`; for `ε > 1` the program runs with
accuracy `1`, which keeps `α = 2δ ≤ 1/4` and `β = δ` inside `[0, 1]`, where APX(α, β) is formulated
(p.16). -/
noncomputable def deltaOf (I : Instance n L T) (ε : ℝ) : ℝ := min ε 1 / (8 * I.rhoMax)

/-- The top index `⌈n/δ⌉` of the weight grid `Dᵗω = {k·δŵₜ/n : k = 0, …, ⌈n/δ⌉}` (p.20). -/
noncomputable def KW (n : ℕ) (δ : ℝ) : ℕ := ⌈(n : ℝ) / δ⌉₊

/-- The top index `⌈n²/δ⌉` of the reward grid `Dρ = {k·δρ∗single/n : k = 0, …, ⌈n²/δ⌉}` (p.20). -/
noncomputable def KR (n : ℕ) (δ : ℝ) : ℕ := ⌈(n : ℝ) ^ 2 / δ⌉₊

/-- The step `δŵₜ/n` of the weight grid `Dᵗω` (p.20). -/
noncomputable def stepW (n : ℕ) (δ : ℝ) (ŵ : Fin T → ℝ) (t : Fin T) : ℝ := δ * ŵ t / n

/-- The step `δρ_single/n` of the reward grid `Dρ` (p.20), for a guess `ρ_single` of `ρ∗single`. -/
noncomputable def stepR (n : ℕ) (δ ρs : ℝ) : ℝ := δ * ρs / n

/-- **Rounding down to a grid** `{k·step : k = 0, …, K}` (p.20, "rounds its argument down to the
nearest point"), as the index of the point: the largest `k ≤ K` with `k·step ≤ a`.

**Formalization Note.** For `step > 0` and `a ≥ 0` this is `min K ⌊a/step⌋`. When `step = 0` every
grid point is `0` and the index `0` is returned; for `a < 0` (never used: the rounded quantities are
nonnegative) the index `0` is returned. -/
noncomputable def roundIdx (step : ℝ) (K : ℕ) (a : ℝ) : ℕ :=
  if 0 < step then min K ⌊a / step⌋₊ else 0

/-- Product `i`'s prices `xᵢ = (x t i)_t` under the strategy `x`. -/
def col (x : Strategy n L T) (i : Fin n) : Fin T → Fin L := fun t => x t i

/-- `∆ⁱ(xᵢ) = Σ_{t∈[2,T]} 1[x^{t−1}_{i·} ≠ xᵗ_{i·}]` (p.18), the number of price changes of a single
product's price vector. -/
def DeltaI (xi : Fin T → Fin L) : ℕ :=
  ((laterPeriods T).filter
    (fun t => ∃ h : 1 ≤ t.val, xi (prevPeriod t h) ≠ xi t)).card

/-- The base case (10), p.20, at the grid state `(n + 1, ω, ρ)` (`m = n` products) with weight indices `kω` and reward
index `kρ`: `0` if `ρ ≤ 0` and `ωₜ ≥ (1 − 2δ)·ŵₜ` for all `t`, `∞` (`⊤`) otherwise. -/
noncomputable def VBase (m : ℕ) (ŵ : Fin T → ℝ) (δ ρs : ℝ) (kω : Fin T → ℕ) (kρ : ℕ) : WithTop ℝ := by
  classical
  exact if (kρ : ℝ) * stepR m δ ρs ≤ 0 ∧ ∀ t, (1 - 2 * δ) * ŵ t ≤ (kω t : ℝ) * stepW m δ ŵ t
    then ((0 : ℝ) : WithTop ℝ) else ⊤

namespace Instance

variable (I : Instance n L T)

/-- **The set `Fⁱ₀(ω)`** of p.18 (with `β = 0`, as (9) uses it, p.20), at the grid state whose weight
coordinates have indices `kω`: single-product price vectors `xᵢ` with
`ωₜ + Σ_ℓ wᵗ_{iℓ} xᵗ_{iℓ} ≤ ŵₜ` for all `t` and `xᵗᵢ = x^{t−1}ᵢ` for all `t ∉ Γ`. -/
def F0 (Γ : Finset (Fin T)) (ŵ : Fin T → ℝ) (δ : ℝ) (kω : Fin T → ℕ) (i : Fin n)
    (xi : Fin T → Fin L) : Prop :=
  (∀ t, (kω t : ℝ) * stepW n δ ŵ t + I.w t i (xi t) ≤ ŵ t) ∧
  ∀ t : Fin T, ∀ h : 1 ≤ t.val, t ∉ Γ → xi (prevPeriod t h) = xi t

/-- The weight indices of `Dᵗω(ω + w|xᵢ)` (p.20) after pricing product `i` by `xᵢ` at the state with
weight indices `kω`. -/
noncomputable def wNext (ŵ : Fin T → ℝ) (δ : ℝ) (kω : Fin T → ℕ) (i : Fin n) (xi : Fin T → Fin L) :
    Fin T → ℕ :=
  fun t => roundIdx (stepW n δ ŵ t) (KW n δ) ((kω t : ℝ) * stepW n δ ŵ t + I.w t i (xi t))

/-- The index of `Dρ(R̂ⁱ_{2δ,δ}(xᵢ))` (p.20) in the reward grid of the guess `ρ_single`. -/
noncomputable def kRof (ŵ : Fin T → ℝ) (δ ρs : ℝ) (i : Fin n) (xi : Fin T → Fin L) : ℕ :=
  roundIdx (stepR n δ ρs) (KR n δ) (I.Rhati ŵ δ i xi)

/-- **The approximate dynamic program `V̂`**, equations (9)–(10), p.20, for the guess
`(Γ, ŵ, ρ_single)` and accuracy `δ` (`α = 2δ`, `β = δ`). `Vhat i kω kρ` is `V̂(i + 1, ω, ρ)` at the
grid state with weight indices `kω` (`ωₜ = kω t · δŵₜ/n`) and reward index `kρ`
(`ρ = kρ · δρ_single/n`):
`V̂(i, ω, ρ) = min_{xᵢ∈Fⁱ₀(ω)} {v·∆ⁱ(xᵢ) + V̂(i + 1, Dω(ω + w|xᵢ), ρ − Dρ(R̂ⁱ_{2δ,δ}(xᵢ)))}`,
`∞` when `Fⁱ₀(ω) = ∅`, with base case (10) at `i = n` (the paper's `n + 1`).

**Formalization Note.** Products are 0-based. Values are in `WithTop ℝ` (`⊤` is `∞`). The reward
update `ρ − Dρ(R̂ⁱ(xᵢ))` is taken on indices with truncated subtraction, i.e. it is clamped at `0`
when it would be negative (it is then not in `Dρ`); the base case only asks `ρ ≤ 0`, so the clamp
changes no value the paper's proofs use. -/
noncomputable def Vhat (Γ : Finset (Fin T)) (ŵ : Fin T → ℝ) (δ ρs : ℝ) :
    ℕ → (Fin T → ℕ) → ℕ → WithTop ℝ
  | i, kω, kρ =>
    if h : i < n then by
      classical
      exact (Finset.univ.filter (fun xi => I.F0 Γ ŵ δ kω ⟨i, h⟩ xi)).inf fun xi =>
        ((I.v * DeltaI xi : ℝ) : WithTop ℝ) +
          Vhat Γ ŵ δ ρs (i + 1) (I.wNext ŵ δ kω ⟨i, h⟩ xi) (kρ - I.kRof ŵ δ ρs ⟨i, h⟩ xi)
    else VBase n ŵ δ ρs kω kρ
  termination_by i => n - i

/-- **`ρ̂`, equation (11), p.21**, as a reward-grid index:
`ρ̂ = max{ρ ∈ Dρ : V̂(1, 0⃗, ρ) ≤ B − |Γ|·f}`. It is `⊥` when the set is empty. -/
noncomputable def rhoHat (Γ : Finset (Fin T)) (ŵ : Fin T → ℝ) (δ ρs : ℝ) : WithBot ℕ := by
  classical
  exact ((Finset.range (KR n δ + 1)).filter (fun k =>
    I.Vhat Γ ŵ δ ρs 0 (fun _ => 0) k ≤ ((I.B - Γ.card * I.f : ℝ) : WithTop ℝ))).max

/-- The weight indices `ω̂⁽ⁱ⁾` of the states visited by following the strategy `x` from
`(1, 0⃗, ·)`, equation (27), p.56: `ω̂⁽¹⁾ = 0⃗`, `ω̂⁽ⁱ⁾ = Dω(ω̂⁽ⁱ⁻¹⁾ + w|x_{i−1})` (0-based). -/
noncomputable def pathW (ŵ : Fin T → ℝ) (δ : ℝ) (x : Strategy n L T) : ℕ → (Fin T → ℕ)
  | 0 => fun _ => 0
  | i + 1 => if h : i < n then I.wNext ŵ δ (pathW ŵ δ x i) ⟨i, h⟩ (col x ⟨i, h⟩) else pathW ŵ δ x i

/-- The reward indices `ρ̂⁽ⁱ⁾` of the states visited by following `x` from `(1, 0⃗, ρ)` with `ρ` of
index `k0`, equation (27), p.56: `ρ̂⁽ⁱ⁾ = ρ̂⁽ⁱ⁻¹⁾ − Dρ(R̂^{i−1}_{2δ,δ}(x_{i−1}))`, clamped at `0` as in
`Vhat`. -/
noncomputable def pathR (ŵ : Fin T → ℝ) (δ ρs : ℝ) (k0 : ℕ) (x : Strategy n L T) : ℕ → ℕ
  | 0 => k0
  | i + 1 => if h : i < n then pathR ŵ δ ρs k0 x i - I.kRof ŵ δ ρs ⟨i, h⟩ (col x ⟨i, h⟩)
      else pathR ŵ δ ρs k0 x i

end Instance

end MenuCostPricing


