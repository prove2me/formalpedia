-- Prove2me | Definitions.Def_TheoryOfGames_Minimax_MixedStrategy
-- name    : TheoryOfGames_Minimax_MixedStrategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T03:07:15.367653+00:00
-- url     : https://prove2.me/theorems/1747957e-90a8-4d54-8fe5-b5710939c40e
-- title:
--   Mixed strategies, $K(\xi,\eta)$, the good strategies $\bar A$, $\bar B$ and special strict determinateness (17.2–17.8)
-- statement:
--   Consider the normalized zero-sum two-person game $\Gamma$ (14.1.1): player 1 chooses a pure strategy $\tau_1 = 1, \dots, \beta_1$, player 2 chooses $\tau_2 = 1, \dots, \beta_2$, each in ignorance of the other's choice, and player 1 receives $\mathcal H(\tau_1, \tau_2)$ while player 2 receives $-\mathcal H(\tau_1, \tau_2)$. The matrix $\mathcal H$ is arbitrary.
--
--   1. A **mixed strategy** of player 1 is a point $\xi = (\xi_1, \dots, \xi_{\beta_1})$ of the simplex $S_{\beta_1} = \{\xi : \xi_{\tau_1} \ge 0,\ \sum_{\tau_1} \xi_{\tau_1} = 1\}$ (16.2.2, 17.2); likewise $\eta \in S_{\beta_2}$ for player 2. The pure strategy $\tau$ corresponds to the coordinate vector $\delta^{\tau}$, with $\delta^{\tau}_i = 1$ if $i = \tau$ and $0$ otherwise (16.1.3).
--   2. The **expected payoff** (17:2) is the bilinear form
--   $$K(\xi, \eta) = \sum_{\tau_1=1}^{\beta_1} \sum_{\tau_2=1}^{\beta_2} \mathcal H(\tau_1, \tau_2)\, \xi_{\tau_1} \eta_{\tau_2}.$$
--   3. $\operatorname{Min}_\eta K(\xi, \eta)$ is the minimum over $\eta \in S_{\beta_2}$ and $\operatorname{Max}_\xi K(\xi, \eta)$ the maximum over $\xi \in S_{\beta_1}$.
--   4. **Good strategies** (17:B:a), (17:B:b): $\bar A$ is the set of those $\xi \in S_{\beta_1}$ for which $\operatorname{Min}_\eta K(\xi, \eta)$ assumes its maximum value over $S_{\beta_1}$; $\bar B$ is the set of those $\eta \in S_{\beta_2}$ for which $\operatorname{Max}_\xi K(\xi, \eta)$ assumes its minimum value over $S_{\beta_2}$.
--   5. A **saddle point of $K$** is a pair $\xi \in S_{\beta_1}$, $\eta \in S_{\beta_2}$ with $K(\xi', \eta) \le K(\xi, \eta) \le K(\xi, \eta')$ for all $\xi' \in S_{\beta_1}$, $\eta' \in S_{\beta_2}$ (13.4.2 with $x, y, \phi$ replaced by $\xi, \eta, K$).
--   6. With pure strategies only, $v_1 = \operatorname{Max}_{\tau_1} \operatorname{Min}_{\tau_2} \mathcal H(\tau_1, \tau_2)$ and $v_2 = \operatorname{Min}_{\tau_2} \operatorname{Max}_{\tau_1} \mathcal H(\tau_1, \tau_2)$ ((14:A:c), (14:B:c)); the game is **specially strictly determined** if $v_1 = v_2$ (17.5.1).
--
--   These are the objects of the book's solution of every zero-sum two-person game: $\bar A$ and $\bar B$ are the good ways of playing $\Gamma$ for players 1 and 2.
--
--   **Formalization Note** Pure strategies are indexed by `Fin β₁`, `Fin β₂`, i.e. from $0$ rather than $1$, and $S_\beta$ is Mathlib's `stdSimplex ℝ (Fin β)`. $\operatorname{Min}_\eta$ and $\operatorname{Max}_\xi$ are the real `⨅`/`⨆` over the simplex, and $v_1, v_2$ are `⨆`/`⨅` over the finite sets of pure strategies; for $\beta_1, \beta_2 \ge 1$ (every theorem of the mission assumes this, directly or through $\xi \in S_{\beta_1}$) the simplex is nonempty and compact and $K$ is continuous, so these are the book's attained Max and Min. The book defines $\bar A$, $\bar B$ equivalently through $v' = \operatorname{Max}_\xi \operatorname{Min}_\eta K$; here they are defined as maximizers and minimizers directly, so no value is presupposed.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 98, 14.1.1; pp. 101–103, 14.3.1, (14:A:c), 14.3.3, (14:B:c); pp. 131–132, 16.2.2; pp. 149–150, 17.4.1–17.4.2, (17:2); p. 150, 17.5.1; p. 158, (17:B:a), (17:B:b)

import Mathlib

namespace TheoryOfGames.Minimax

/-- The expected payoff (17:2) of the normalized zero-sum two-person game with matrix
`ℋ(τ₁, τ₂)` (14.1.1) when player 1 uses the mixed strategy `ξ` and player 2 uses `η`:
`K(ξ, η) = ∑_{τ₁} ∑_{τ₂} ℋ(τ₁, τ₂) ξ_{τ₁} η_{τ₂}`. Pure strategies are `Fin β₁`, `Fin β₂`
(numbered from `0`); mixed strategies are points of `stdSimplex ℝ (Fin β)`, the book's `S_β`
of 16.2.2. -/
def K {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ) : ℝ :=
  ∑ τ₁, ∑ τ₂, H τ₁ τ₂ * ξ τ₁ * η τ₂

/-- `Min_η K(ξ, η)`, the minimum over `η ∈ S_{β₂}`; for `β₂ ≥ 1` the set `S_{β₂}` is
nonempty and compact and `K(ξ, ·)` is continuous, so this infimum is attained. -/
noncomputable def minK {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (ξ : Fin β₁ → ℝ) : ℝ :=
  ⨅ η : stdSimplex ℝ (Fin β₂), K H ξ η

/-- `Max_ξ K(ξ, η)`, the maximum over `ξ ∈ S_{β₁}`; attained for `β₁ ≥ 1`. -/
noncomputable def maxK {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) (η : Fin β₂ → ℝ) : ℝ :=
  ⨆ ξ : stdSimplex ℝ (Fin β₁), K H ξ η

/-- `Ā` (17:B:a): the set of those `ξ` in `S_{β₁}` for which `Min_η K(ξ, η)` assumes its
maximum value (over `S_{β₁}`). These are the good strategies of player 1. -/
def goodA {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) : Set (Fin β₁ → ℝ) :=
  {ξ | ξ ∈ stdSimplex ℝ (Fin β₁) ∧ ∀ ξ' ∈ stdSimplex ℝ (Fin β₁), minK H ξ' ≤ minK H ξ}

/-- `B̄` (17:B:b): the set of those `η` in `S_{β₂}` for which `Max_ξ K(ξ, η)` assumes its
minimum value (over `S_{β₂}`). These are the good strategies of player 2. -/
def goodB {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) : Set (Fin β₂ → ℝ) :=
  {η | η ∈ stdSimplex ℝ (Fin β₂) ∧ ∀ η' ∈ stdSimplex ℝ (Fin β₂), maxK H η ≤ maxK H η'}

/-- `ξ, η` is a saddle point of `K(ξ, η)` on `S_{β₁} × S_{β₂}` (13.4.2 with `x, y, φ`
replaced by `ξ, η, K`): `K(ξ', η)` assumes its maximum over `S_{β₁}` at `ξ' = ξ` and
`K(ξ, η')` assumes its minimum over `S_{β₂}` at `η' = η`. -/
def IsMixedSaddlePoint {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ)
    (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ) : Prop :=
  ξ ∈ stdSimplex ℝ (Fin β₁) ∧ η ∈ stdSimplex ℝ (Fin β₂) ∧
    (∀ ξ' ∈ stdSimplex ℝ (Fin β₁), K H ξ' η ≤ K H ξ η) ∧
    (∀ η' ∈ stdSimplex ℝ (Fin β₂), K H ξ η ≤ K H ξ η')

/-- The coordinate vector `δ^τ` of 16.1.3 (`δ^τ_i = 1` if `i = τ`, `0` otherwise): the mixed
strategy that plays the pure strategy `τ` with probability one (17.2). -/
def pureVec {β : ℕ} (τ : Fin β) : Fin β → ℝ := fun i => if i = τ then 1 else 0

/-- `v₁ = Max_{τ₁} Min_{τ₂} ℋ(τ₁, τ₂)` (14.3.1, (14:A:c)); for `β₁, β₂ ≥ 1` the finite
supremum and infimum are attained. -/
noncomputable def v₁ {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) : ℝ := ⨆ τ₁, ⨅ τ₂, H τ₁ τ₂

/-- `v₂ = Min_{τ₂} Max_{τ₁} ℋ(τ₁, τ₂)` (14.3.3, (14:B:c)); attained for `β₁, β₂ ≥ 1`. -/
noncomputable def v₂ {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) : ℝ := ⨅ τ₂, ⨆ τ₁, H τ₁ τ₂

/-- The game is *specially strictly determined* (17.5.1) when `v₁ = v₂`. -/
def SpeciallyStrictlyDetermined {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ) : Prop :=
  v₁ H = v₂ H

end TheoryOfGames.Minimax


