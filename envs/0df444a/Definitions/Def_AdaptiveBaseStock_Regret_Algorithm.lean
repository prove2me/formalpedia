-- Prove2me | Definitions.Def_AdaptiveBaseStock_Regret_Algorithm
-- name    : AdaptiveBaseStock_Regret_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:30:01.171999+00:00
-- url     : https://prove2.me/theorems/e14dae5a-d288-4ec1-a7be-066d32b8f56a
-- title:
--   Sec. 5.1 — the algorithm Adaptive(α, β), cycle lengths T_k = ⌈k^β⌉, the regret Λ(L) and its parts Λ₁, Λ₂, and ν
-- statement:
--   This file defines the algorithm $\textsc{Adaptive}(\alpha,\beta)$ of Sec. 5.1 and the regret it is measured by.
--
--   **Inputs.** Costs $h, b$, parameters $\alpha, \beta$, bounds $\underline M \le \overline M$ on the optimal base-stock level, a first level $S_1 \in [\underline M, \overline M]$ and an initial inventory vector $X_{(1,1)}$.
--
--   **Cycles.** Time is divided into cycles $k = 1, 2, \dots$; cycle $k$ has length $T_k = \lceil k^\beta \rceil$ and the first $L$ cycles contain $N(L) = \sum_{k=1}^L T_k$ periods. Cycle $k$ uses the order-up-to-$S_k$ policy in every period, starting from the inventory vector $X_{(k,1)}$; $I_{(k,j)}$ and $D_{(k,j)}$ denote the on-hand inventory and the demand of its $j$-th period.
--
--   **Gradient estimate.** In each period of cycle $k$ the algorithm computes
--   $$I'_{(k,j)} = 1 - \sum_{\ell=j-\tau}^{j-1} I'_{(k,\ell)}\, \mathbb I\big[I_{(k,\ell)} \le D_{(k,\ell)}\big], \qquad I'_{(k,j)} = 0 \text{ for } j \le 0,$$
--   and at the end of the cycle sets $H_k = h$ if $I'_{(k,T_k)} = 1$ and $I_{(k,T_k)} > D_{(k,T_k)}$, $H_k = -b$ if $I'_{(k,T_k)} = 1$ and $I_{(k,T_k)} \le D_{(k,T_k)}$, and $H_k = 0$ otherwise.
--
--   **Update.** With $\epsilon_k = (\overline M - \underline M)/(\max\{b,h\}\, k^\alpha)$,
--   $$S_{k+1} = P_{[\underline M, \overline M]}(S_k - \epsilon_k H_k), \qquad P_{[\underline M,\overline M]}(z) = \max\{\underline M, \min\{z, \overline M\}\},$$
--   and the next cycle starts from the inventory vector reached after ordering in the last period of cycle $k$; the inventory is not reset.
--
--   **Regret.** With $S^*$ an optimal base-stock level and $C(I_\infty(\cdot))$ the long-run average cost,
--   $$\Lambda(L) = E\Big[\sum_{k=1}^L \sum_{j=1}^{T_k} C\big(I_{(k,j)}(S_k; X_{(k,1)})\big)\Big] - C(I_\infty(S^*))\, N(L),$$
--   and it splits as $\Lambda = \Lambda_1 + \Lambda_2$ with
--   $$\Lambda_1(L) = \sum_{k=1}^L T_k \big\{E[C(I_\infty(S_k))] - C(I_\infty(S^*))\big\}, \quad \Lambda_2(L) = E\Big[\sum_{k=1}^L \sum_{j=1}^{T_k} \big\{C(I_{(k,j)}) - C(I_\infty(S_k))\big\}\Big].$$
--   Finally $\nu = \max\{1 - \gamma(\underline M)^{2\tau}, F(\overline M), 1/e\}$.
--
--   **Formalization Note** The algorithm runs on one demand path and is applied to $\omega \mapsto (D_n(\omega))_n$. Cycles are numbered from $1$, periods inside a cycle from $0$ (Lean index $j$ is the paper's $j+1$). $I'$ is the recursion the algorithm computes, not a derivative. $H_k$ is $0$ whenever $I'_{(k,T_k)} \ne 1$; by Theorem 1 of the paper $I'$ takes only the values $0$ and $1$.
-- source:
--   Huh, Janakiraman, Muckstadt, Rusmevichientong, An Adaptive Algorithm for Finding the Optimal Base-Stock Policy in Lost Sales Inventory Systems with Censored Demand, working paper, February 8, 2007 (published version: Math. Oper. Res., 2009, DOI 10.1287/moor.1080.0367), Sec. 5.1, pp. 22–24 (algorithm, Λ(L)); Sec. 5.3, p. 25 (Λ₁, Λ₂), p. 26 (ν)

import Mathlib
import Definitions.Def_AdaptiveBaseStock_Regret_Model

namespace AdaptiveBaseStock.Regret

open MeasureTheory

/-- The inputs of `Adaptive(α, β)`: the costs `h, b`, the parameters `α, β`, the bounds
`M̲ = Mlo`, `M̄ = Mhi` of Assumption 1, the first level `S₁` and the initial inventory vector
`X_(1,1) = x₁`. -/
structure AdaptiveParams (τ : ℕ) where
  h : ℝ
  b : ℝ
  α : ℝ
  β : ℝ
  Mlo : ℝ
  Mhi : ℝ
  S₁ : ℝ
  x₁ : InvVec τ

/-- The length `T_k = ⌈k^β⌉` of cycle `k` (cycles are numbered `k = 1, 2, …`). -/
noncomputable def cycleLen (β : ℝ) (k : ℕ) : ℕ := ⌈(k : ℝ) ^ β⌉₊

/-- `N(L) = Σ_{k=1}^L T_k`, the number of periods in the first `L` cycles (`N(0) = 0`). -/
noncomputable def periodsUpTo (β : ℝ) (L : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 L, cycleLen β k

/-- The step size `ϵ_k = (M̄ - M̲) / (max{b, h} · k^α)`. -/
noncomputable def stepSize {τ : ℕ} (p : AdaptiveParams τ) (k : ℕ) : ℝ :=
  (p.Mhi - p.Mlo) / (max p.b p.h * (k : ℝ) ^ p.α)

/-- The projection `P_[M̲, M̄](z) = max{M̲, min{z, M̄}}`. -/
noncomputable def proj {τ : ℕ} (p : AdaptiveParams τ) (z : ℝ) : ℝ := max p.Mlo (min z p.Mhi)

/-- The sample-derivative recursion of the algorithm (p. 23), indexed from `0` within a cycle
(Lean index `i` is the paper's `j = i + 1`): `I'(i) = 1 - Σ_{ℓ = i-τ}^{i-1} I'(ℓ) · 𝕀[I(ℓ) ≤ D(ℓ)]`,
the terms with a negative index being `0` (the paper's `I'_(k,j) = 0` for `j ≤ 0`). Here `I` is
the on-hand inventory and `dem` the demand of each period of the cycle. -/
noncomputable def derivSeq (τ : ℕ) (I dem : ℕ → ℝ) : ℕ → ℝ
  | i => 1 - ∑ ℓ : Fin i,
      if i ≤ ℓ.val + τ then derivSeq τ I dem ℓ.val * (if I ℓ.val ≤ dem ℓ.val then 1 else 0)
      else 0
decreasing_by exact ℓ.isLt

/-- The inventory vectors of one cycle run at the constant level `S` from the cycle's initial
inventory vector `X`, the cycle starting at Lean period `n₀` of the demand path `d`; index `j` is
the `(j+1)`-th period of the cycle. -/
noncomputable def cycleStates {τ : ℕ} (S : ℝ) (X : InvVec τ) (d : ℕ → ℝ) (n₀ : ℕ) :
    ℕ → InvVec τ :=
  run (fun _ => S) X (fun j => d (n₀ + j))

/-- The gradient estimate `H_k(S_k)` of cycle `k` (p. 23), computed from the last period
`T_k` of the cycle: `h` if `I'_(k,T_k) = 1` and `I_(k,T_k) > D_(k,T_k)`, `-b` if `I'_(k,T_k) = 1`
and `I_(k,T_k) ≤ D_(k,T_k)`, and `0` otherwise. -/
noncomputable def gradEst {τ : ℕ} (p : AdaptiveParams τ) (k : ℕ) (S : ℝ) (X : InvVec τ)
    (d : ℕ → ℝ) (n₀ : ℕ) : ℝ :=
  let I : ℕ → ℝ := fun j => (cycleStates S X d n₀ j).2
  let dem : ℕ → ℝ := fun j => d (n₀ + j)
  let last := cycleLen p.β k - 1
  if derivSeq τ I dem last = 1 then (if I last > dem last then p.h else -p.b) else 0

/-- The end-of-cycle update of cycle `k`, which starts at Lean period `n₀` with level `S` and
initial inventory vector `X`: the next level `S_{k+1} = P_[M̲, M̄](S_k - ϵ_k · H_k(S_k))` and the
next cycle's initial inventory vector, the inventory vector after ordering in the last period of
cycle `k` (the state entering the next period of the same dynamics). -/
noncomputable def cycleUpdate {τ : ℕ} (p : AdaptiveParams τ) (k : ℕ) (n₀ : ℕ) (d : ℕ → ℝ)
    (SX : ℝ × InvVec τ) : ℝ × InvVec τ :=
  (proj p (SX.1 - stepSize p k * gradEst p k SX.1 SX.2 d n₀),
    cycleStates SX.1 SX.2 d n₀ (cycleLen p.β k))

/-- The level and initial inventory vector `(S_{n+1}, X_(n+1,1))` of cycle `n + 1` of
`Adaptive(α, β)` along the demand path `d`. -/
noncomputable def cycleState {τ : ℕ} (p : AdaptiveParams τ) (d : ℕ → ℝ) : ℕ → ℝ × InvVec τ
  | 0 => (p.S₁, p.x₁)
  | n + 1 => cycleUpdate p (n + 1) (periodsUpTo p.β n) d (cycleState p d n)

/-- The level `S_k` of cycle `k ≥ 1`. -/
noncomputable def level {τ : ℕ} (p : AdaptiveParams τ) (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  (cycleState p d (k - 1)).1

/-- The on-hand inventory `I_(k,j+1)(S_k; X_(k,1))` in the `(j+1)`-th period of cycle `k ≥ 1`. -/
noncomputable def onHand {τ : ℕ} (p : AdaptiveParams τ) (d : ℕ → ℝ) (k j : ℕ) : ℝ :=
  (cycleStates (cycleState p d (k - 1)).1 (cycleState p d (k - 1)).2 d
    (periodsUpTo p.β (k - 1)) j).2

/-- The L-cycle regret `Λ(L) = E[Σ_{k=1}^L Σ_{j=1}^{T_k} C(I_(k,j)(S_k; X_(k,1)))] - C(I_∞(S*)) · N(L)`
(p. 23), with `C(I_∞(S*))` the long-run average cost of the order-up-to-`S*` policy. -/
noncomputable def regret {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℕ → Ω → ℝ)
    {τ : ℕ} (p : AdaptiveParams τ) (Sstar : ℝ) (L : ℕ) : ℝ :=
  (∫ ω, ∑ k ∈ Finset.Icc 1 L, ∑ j ∈ Finset.range (cycleLen p.β k),
      periodCost P (D 0) p.h p.b (onHand p (fun n => D n ω) k j) ∂P)
    - baseStockCost P D τ p.h p.b Sstar * (periodsUpTo p.β L : ℝ)

/-- `Λ₁(L) = Σ_{k=1}^L T_k · {E[C(I_∞(S_k))] - E[C(I_∞(S*))]}` (p. 25). -/
noncomputable def regretLevel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℕ → Ω → ℝ)
    {τ : ℕ} (p : AdaptiveParams τ) (Sstar : ℝ) (L : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 L, (cycleLen p.β k : ℝ) *
    ((∫ ω, baseStockCost P D τ p.h p.b (level p (fun n => D n ω) k) ∂P)
      - baseStockCost P D τ p.h p.b Sstar)

/-- `Λ₂(L) = E[Σ_{k=1}^L Σ_{j=1}^{T_k} {C(I_(k,j)(S_k; X_(k,1))) - C(I_∞(S_k))}]` (p. 25). -/
noncomputable def regretTransient {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ℕ → Ω → ℝ) {τ : ℕ} (p : AdaptiveParams τ) (L : ℕ) : ℝ :=
  ∫ ω, ∑ k ∈ Finset.Icc 1 L, ∑ j ∈ Finset.range (cycleLen p.β k),
    (periodCost P (D 0) p.h p.b (onHand p (fun n => D n ω) k j)
      - baseStockCost P D τ p.h p.b (level p (fun n => D n ω) k)) ∂P

/-- `ν = max{1 - γ(M̲)^{2τ}, F(M̄), 1/e}` (pp. 24, 26). -/
noncomputable def nu {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D₀ : Ω → ℝ) (τ : ℕ)
    (Mlo Mhi : ℝ) : ℝ :=
  max (1 - gammaLevel P D₀ τ Mlo ^ (2 * τ)) (max (demandCdf P D₀ Mhi) (Real.exp (-1)))

end AdaptiveBaseStock.Regret


