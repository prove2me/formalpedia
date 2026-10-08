-- Prove2me | Definitions.Def_PGLandscape_FiniteHorizon_Stages
-- name    : PGLandscape_FiniteHorizon_Stages
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:34.906306+00:00
-- url     : https://prove2.me/theorems/52286d31-8433-4526-afab-7899b1d24732
-- title:
--   Condition 3, Condition 4, Assumption 3 (§5.4, p. 17) and the stage objectives B_h (App. D.2, p. 40) — finite-horizon stage structure and non-stationary policy classes
-- statement:
--   This definition file collects the finite-horizon structure of Bhandari and Russo, §5.4, and the single-period objectives used in the proof of Theorem 3 (App. D.2).
--
--   **Stages.** The state space is split into stages $\mathcal S = \mathcal S_1\cup\cdots\cup\mathcal S_H\cup\mathcal S_{H+1}$, encoded by a measurable stage index $\mathrm{stage}:\mathcal S\to\{1,\dots,H+1\}$ with $\mathcal S_h = \{s:\mathrm{stage}(s)=h\}$. For $s\in\mathcal S_h$ with $h\le H$, $P(\mathcal S_{h+1}\mid s,a)=1$ for every feasible action $a\in\mathcal A_s$. The last stage is a single costless absorbing state, $\mathcal S_{H+1}=\{\tau\}$, with $P(\{\tau\}\mid\tau,a)=1$ and $g(\tau,a)=0$ for every action $a$.
--
--   **Non-stationary parameters.** Each coordinate of $\theta\in\mathbb R^d$ belongs to one of $H$ sub-vectors, $\theta=(\theta_1,\dots,\theta_H)$. For $\theta,\theta'$ and a stage $h$, the block swap $\mathrm{swap}_h(\theta',\theta)$ is $(\theta_1,\dots,\theta'_h,\dots,\theta_H)$, and the block-$h$ section of $\Theta$ through $\theta$ is $\{\mathrm{swap}_h(\theta',\theta):\theta'\in\Theta\}$, i.e. $\Theta_h$ with the other sub-vectors frozen at those of $\theta$.
--
--   **Condition 3.** The stage structure above holds; $\Theta=\Theta_1\times\cdots\times\Theta_H$ is a product set (closed under exchanging one sub-vector between two of its points); and for $s\in\mathcal S_h$, $h\le H$, the action $\pi_\theta(s)$ depends only on $\theta_h$.
--
--   **Condition 4.** For every $\eta\in\{\eta_\pi:\pi\in\Pi_\Theta\}$, the function $\theta\mapsto\mathcal B(\theta\mid\eta,J^*)$ is differentiable at the points of $\Theta$, and the problem $\min_{\theta\in\Theta}\mathcal B(\theta\mid\eta,J^*)$ has no suboptimal stationary points:
--   $$\theta\ \text{stationary for}\ \min_{\bar\theta\in\Theta}\mathcal B(\bar\theta\mid\eta,J^*)\quad\Longrightarrow\quad\mathcal B(\theta\mid\eta,J^*)\le\mathcal B(\theta'\mid\eta,J^*)\ \ \forall\theta'\in\Theta .$$
--
--   **Assumption 3.** For every $\pi\in\Pi_\Theta$, $\eta_\pi\ll\rho$.
--
--   **Stage objectives.** For a stage $h$, a policy $\bar\pi$, a measure $\eta$ and a function $J$,
--   $$\mathcal B_h(\bar\pi\mid\eta,J)=\int_{\mathcal S_h}(T_{\bar\pi}J)(s)\,\eta(ds),$$
--   which for $J=J_\pi$ is $\int_{\mathcal S_h}Q_\pi(s,\bar\pi(s))\,\eta(ds)$, the page's $\mathcal B_h(\bar\theta_h\mid\eta,J_\pi)$ when $\bar\pi=\pi_{\bar\theta}$.
--
--   These objects state Theorem 3: policy gradient on a non-stationary policy class of a finite-horizon problem has no suboptimal stationary points.
--
--   **Formalization Note** Stages and sub-vectors are numbered from $1$, as on the page; $\mathcal S_h$ is measurable. The transition clause of Condition 3 is required for feasible actions $a\in\mathcal A_s$ (as printed); the absorbing-state clause for every action, which also constrains the extension of $g,P$ outside the feasible graph. "$\pi_\theta(s)$ depends only on $\theta_h$" is required for all $\theta\in\mathbb R^d$, since the parameterization is defined on $\mathbb R^d$ and Condition 0 differentiates near $\Theta$. A product set is encoded as closure under single-block swaps, which is equivalent. Footnote 14 (disjoint $\Theta_h$) is notation and not encoded. In Condition 4, the differentiability clause is the premise of Definition 1 (p. 8: stationary points are defined for $f$ continuously differentiable on an open set containing the feasible set), weakened to differentiability at the points of $\Theta$; without it, the notion of stationary point used here (which includes differentiability) would let Condition 4 hold vacuously wherever $\mathcal B(\cdot\mid\eta,J^*)$ is not differentiable. $J^*=J_{\pi^*}$ for an optimal policy $\pi^*$.
-- source:
--   arXiv:1906.01786v3, Condition 3, Condition 4, Assumption 3, §5.4, p. 17; Definition 1, p. 8; App. D.2, single period PI objectives, p. 40

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.FiniteHorizon

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The block swap `swap_h(θ', θ)`: the parameter vector equal to `θ'` on the coordinates of the
`h`-th sub-vector (those `i` with `blk i = h`) and to `θ` on all other coordinates. With
`θ = (θ_1, …, θ_H)` and `θ' = (θ'_1, …, θ'_H)` it is `(θ_1, …, θ'_h, …, θ_H)`. -/
noncomputable def blockSwap {d : ℕ} (blk : Fin d → ℕ) (h : ℕ)
    (θ' θ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => if blk i = h then θ' i else θ i)

/-- The block-`h` section of `Θ` through `θ`, `{(θ_1, …, θ'_h, …, θ_H) : θ' ∈ Θ}`; for a product set
`Θ = Θ_1 × ⋯ × Θ_H` it is `Θ_h`, with the other sub-vectors frozen at those of `θ`. -/
def blockSection {d : ℕ} (blk : Fin d → ℕ) (h : ℕ) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (θ : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∃ θ' ∈ Θ, x = blockSwap blk h θ' θ}

/-- The stage structure of Condition 3 (§5.4, p. 17), with stages numbered `1, …, H + 1`:
1. the state space factors as `S = S_1 ∪ ⋯ ∪ S_{H+1}`, `S_h = {s : stage s = h}`, each `S_h`
   measurable;
2. for `s ∈ S_h` with `h ≤ H`, `P(S_{h+1} | s, a) = 1` for every `a ∈ A_s`;
3. `S_{H+1} = {τ}`, and `τ` is a costless absorbing state: `P({τ} | τ, a) = 1` and `g(τ, a) = 0`
   for every action `a`. -/
def IsStaged (M : PGLandscape.Closure.MDP S A) (H : ℕ) (stage : S → ℕ) (τ : S) : Prop :=
  Measurable stage ∧
  (∀ s, 1 ≤ stage s ∧ stage s ≤ H + 1) ∧
  (∀ s, stage s ≤ H → ∀ a ∈ M.As s, M.P (s, a) {s' | stage s' = stage s + 1} = 1) ∧
  (∀ s, stage s = H + 1 ↔ s = τ) ∧
  (∀ a, M.P (τ, a) {τ} = 1 ∧ M.g (τ, a) = 0)

/-- Condition 3 (§5.4, p. 17): the stage structure `IsStaged`, and, with sub-vectors numbered
`1, …, H`:
4. every coordinate of `θ ∈ ℝ^d` belongs to one of the sub-vectors `θ_1, …, θ_H` (`blk i ∈ {1, …, H}`),
   and `Θ = Θ_1 × ⋯ × Θ_H` is a product set, i.e. closed under exchanging one sub-vector;
5. for `s ∈ S_h` with `h ≤ H`, `π_θ(s)` depends only on the sub-vector `θ_h`. -/
def Condition3 {d : ℕ} (M : PGLandscape.Closure.MDP S A) (H : ℕ) (stage : S → ℕ) (τ : S) (blk : Fin d → ℕ)
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A) : Prop :=
  IsStaged M H stage τ ∧
  (∀ i, 1 ≤ blk i ∧ blk i ≤ H) ∧
  (∀ θ ∈ Θ, ∀ θ' ∈ Θ, ∀ h, blockSwap blk h θ' θ ∈ Θ) ∧
  (∀ θ θ' : EuclideanSpace ℝ (Fin d), ∀ s, stage s ≤ H →
    (∀ i, blk i = stage s → θ i = θ' i) → (πθ θ).1 s = (πθ θ').1 s)

/-- Condition 4 (§5.4, p. 17): for every `η ∈ {η_π : π ∈ Π_Θ}`, the problem
`min_{θ ∈ Θ} B(θ | η, J*)` has no suboptimal stationary points, where `J* = J_{π*}`.
Definition 1 (p. 8) speaks of stationary points of `min_{x ∈ X} f(x)` only for `f` continuously
differentiable on an open set containing `X`; the first clause keeps the part of that premise the
condition needs, differentiability of `θ ↦ B(θ | η, J*)` at every point of `Θ`. -/
def Condition4 {d : ℕ} (M : PGLandscape.Closure.MDP S A) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A) (πstar : PGLandscape.Closure.MPolicy S A) : Prop :=
  ∀ θ₀ ∈ Θ,
    (∀ θ ∈ Θ, DifferentiableAt ℝ
      (fun θbar => PGLandscape.Closure.bellmanObj M (πθ θbar).1 (PGLandscape.Closure.occupancy M (πθ θ₀)) (PGLandscape.Closure.costToGo M πstar)) θ) ∧
    ∀ θ, PGLandscape.Closure.IsStationary
        (fun θbar => PGLandscape.Closure.bellmanObj M (πθ θbar).1 (PGLandscape.Closure.occupancy M (πθ θ₀)) (PGLandscape.Closure.costToGo M πstar)) Θ θ →
      ∀ θ' ∈ Θ, PGLandscape.Closure.bellmanObj M (πθ θ).1 (PGLandscape.Closure.occupancy M (πθ θ₀)) (PGLandscape.Closure.costToGo M πstar) ≤
        PGLandscape.Closure.bellmanObj M (πθ θ').1 (PGLandscape.Closure.occupancy M (πθ θ₀)) (PGLandscape.Closure.costToGo M πstar)

/-- Assumption 3 (§5.4, p. 17): for every `π ∈ Π_Θ`, `η_π` is absolutely continuous with respect
to `ρ`. -/
def Assumption3 {d : ℕ} (M : PGLandscape.Closure.MDP S A) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (πθ : EuclideanSpace ℝ (Fin d) → PGLandscape.Closure.MPolicy S A) : Prop :=
  ∀ θ ∈ Θ, PGLandscape.Closure.occupancy M (πθ θ) ≪ M.ρ

/-- The single period policy iteration objective of stage `h` (App. D.2, p. 40):
`B_h(π̄ | η, J) = ∫_{S_h} (T_π̄ J)(s) η(ds)`. With `J = J_π` the integrand is `Q_π(s, π̄(s))`, and with
`π̄ = π_θ̄` this is the page's `B_h(θ̄_h | η, J_π)`. -/
noncomputable def stageObj (M : PGLandscape.Closure.MDP S A) (stage : S → ℕ) (h : ℕ) (πbar : S → A) (η : Measure S)
    (J : S → ℝ) : ℝ :=
  ∫ s in {s | stage s = h}, PGLandscape.Closure.bellmanPi M πbar J s ∂η

end PGLandscape.FiniteHorizon


