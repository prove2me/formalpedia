-- Prove2me | Definitions.Def_SuttonBartoRL_OffPolicy_LinearGeometry
-- name    : SuttonBartoRL_OffPolicy_LinearGeometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:39:40.317706+00:00
-- url     : https://prove2.me/theorems/4cc4e19f-3d54-4ec8-8745-237de3a54eaf
-- title:
--   Linear value-function geometry — Bellman operator, projection, BE and PBE
-- statement:
--   Fix a finite MDP, a target policy $\pi$, a discount $\gamma$, a weighting $\mu$ of the states, and $d$ features: $\mathbf X$ is the $|\mathcal S|\times d$ matrix whose rows are the feature vectors $\mathbf x(s)^\top$. This file defines the objects of §§11.4–11.7 of Sutton & Barto.
--
--   1. The policy's transition matrix $P_\pi(s,s') = \sum_a \pi(a\mid s)\,p(s'\mid s,a)$, expected reward $r_\pi(s) = \sum_a \pi(a\mid s)\,r(s,a)$, and true value function, defined from expected discounted returns (3.12):
--   $$v_\pi(s) = \sum_{k=0}^\infty \gamma^k\,(P_\pi^k r_\pi)(s).$$
--   2. The **Bellman operator** (11.20): $(B_\pi v)(s) = \sum_a \pi(a\mid s)\sum_{s',r} p(s',r\mid s,a)\,[r + \gamma v(s')]$.
--   3. The $\mu$-norm (11.11) $\|v\|_\mu^2 = \sum_s \mu(s)\,v(s)^2$, the matrix $\mathbf D = \operatorname{diag}(\mu)$, and the linear value function (11.15) $v_{\mathbf w} = \mathbf X\mathbf w$.
--   4. The **projection matrix** (11.13):
--   $$\Pi = \mathbf X\,(\mathbf X^\top \mathbf D \mathbf X)^{-1}\,\mathbf X^\top \mathbf D.$$
--   5. The **Bellman error vector** (11.17) $\bar\delta_{\mathbf w} = B_\pi v_{\mathbf w} - v_{\mathbf w}$, the **mean square Bellman error** (11.19) $\mathrm{BE}(\mathbf w) = \|\bar\delta_{\mathbf w}\|_\mu^2$, and the **mean square projected Bellman error** (11.22) $\mathrm{PBE}(\mathbf w) = \|\Pi\bar\delta_{\mathbf w}\|_\mu^2$.
--   6. For a behavior policy $b$: the importance-sampling ratio $\rho = \pi(a\mid s)/b(a\mid s)$, and the expectation of a function $f$ of one transition when $S_t\sim\mu$, $A_t\sim b(\cdot\mid S_t)$ and $(S_{t+1},R_{t+1})\sim p(\cdot,\cdot\mid S_t,A_t)$:
--   $$\mathbb E[f] = \sum_s \mu(s)\sum_a b(a\mid s)\sum_{s'}\sum_{r} p(s',r\mid s,a)\,f(s,a,s',r).$$
--
--   These are the quantities whose geometry Chapter 11 studies: the PBE is the objective that Gradient-TD methods minimize.
--
--   **Formalization Note** Vectors over states are functions $\mathcal S \to \mathbb R$ and weights are $\mathbb R^d$ as `Fin d → ℝ`. The inverse in $\Pi$ is Mathlib's matrix inverse, which is the zero matrix when $\mathbf X^\top\mathbf D\mathbf X$ is singular; every theorem assumes it invertible, and the book's pseudoinverse substitute is not formalized. The value $v_\pi$ is a real `tsum`, meaningful for $0\le\gamma<1$. The ratio $\rho$ is $0$ where $b(a\mid s) = 0$ (Lean's $x/0 = 0$); theorems that use it assume coverage.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, (3.12) p. 58; (11.11) p. 266; (11.13)–(11.15) p. 268; (11.17), (11.19) p. 268; (11.20), (11.22) p. 269; p. 278

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_MDP

open Matrix

namespace SuttonBartoRL.OffPolicy

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}

/-- The state-transition matrix of the Markov chain induced by `π`:
`P_π(s, s') = Σ_a π(a | s) p(s' | s, a)`. -/
def policyTrans (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) : Matrix S S ℝ :=
  fun s s' => ∑ a, π.prob s a * M.trans s a s'

/-- The expected one-step reward under `π`: `r_π(s) = Σ_a π(a | s) r(s, a)`. -/
def policyReward (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) : S → ℝ :=
  fun s => ∑ a, π.prob s a * M.expReward s a

/-- (3.12), p. 58: the true state-value function of `π`,
`v_π(s) = E_π[Σ_{k=0}^∞ γ^k R_{t+k+1} | S_t = s] = Σ_{k=0}^∞ γ^k (P_π^k r_π)(s)`,
defined from expected returns, not from the Bellman equation. A real `tsum`; the theorems that use
it take `0 ≤ γ < 1`, where the series converges absolutely. -/
noncomputable def stateValue (M : MDP S A) (γ : ℝ) (π : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) : ℝ :=
  ∑' k : ℕ, γ ^ k * ((policyTrans M π ^ k) *ᵥ policyReward M π) s

/-- (11.20), p. 269: the Bellman operator `B_π : ℝ^{|S|} → ℝ^{|S|}`,
`(B_π v)(s) = Σ_a π(a|s) Σ_{s', r} p(s', r | s, a) [r + γ v(s')]`. -/
def bellmanOp (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * (r + γ * v s')

/-- (11.11), p. 266: the squared `µ`-weighted norm `‖v‖²_µ = Σ_{s ∈ S} µ(s) v(s)²`. -/
def muNormSq (μ : S → ℝ) (v : S → ℝ) : ℝ :=
  ∑ s, μ s * v s ^ 2

/-- p. 268: `D`, the `|S| × |S|` diagonal matrix with the `µ(s)` on the diagonal. -/
def Dmat (μ : S → ℝ) : Matrix S S ℝ :=
  diagonal μ

/-- (11.15), p. 268: the linear approximate value function `v_w = Xw`, where `X` is the `|S| × d`
matrix whose rows are the feature vectors `x(s)ᵀ`, so `v_w(s) = x(s)ᵀw`. -/
def vw (X : Matrix S (Fin d) ℝ) (w : Fin d → ℝ) : S → ℝ :=
  X *ᵥ w

/-- (11.13), p. 268: the projection matrix `Π = X (XᵀDX)⁻¹ XᵀD`. `⁻¹` is Mathlib's matrix inverse
(the zero matrix when `XᵀDX` is singular); every theorem assumes `XᵀDX` invertible, and the book's
pseudoinverse case is not formalized. -/
noncomputable def projMatrix (μ : S → ℝ) (X : Matrix S (Fin d) ℝ) : Matrix S S ℝ :=
  X * (Xᵀ * Dmat μ * X)⁻¹ * Xᵀ * Dmat μ

/-- (11.17), p. 268, with p. 269: the Bellman error vector of the linear value function `v_w`,
`δ̄_w(s) = (Σ_a π(a|s) Σ_{s', r} p(s', r | s, a)[r + γ v_w(s')]) − v_w(s)`, i.e. `δ̄_w = B_π v_w − v_w`. -/
def bellmanError (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (X : Matrix S (Fin d) ℝ)
    (w : Fin d → ℝ) : S → ℝ :=
  bellmanOp M π γ (vw X w) - vw X w

/-- (11.19), p. 268: the mean square Bellman error `BE(w) = ‖δ̄_w‖²_µ`. -/
def BE (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (μ : S → ℝ) (X : Matrix S (Fin d) ℝ)
    (w : Fin d → ℝ) : ℝ :=
  muNormSq μ (bellmanError M π γ X w)

/-- (11.22), p. 269: the mean square projected Bellman error `PBE(w) = ‖Π δ̄_w‖²_µ`. -/
noncomputable def PBE (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (γ : ℝ) (μ : S → ℝ)
    (X : Matrix S (Fin d) ℝ) (w : Fin d → ℝ) : ℝ :=
  muNormSq μ (projMatrix μ X *ᵥ bellmanError M π γ X w)

/-- p. 278: the importance-sampling ratio of one step, `ρ = π(a|s) / b(a|s)` (5.3), for target
policy `π` and behavior policy `b`. Lean's `x / 0 = 0` makes it `0` where `b(a|s) = 0`; the theorems
assume coverage (`π(a|s) > 0 → b(a|s) > 0`, p. 103), so such pairs also have `π(a|s) = 0`. -/
noncomputable def isRatio (π b : SuttonBartoRL.FiniteMDP.Policy S A) (s : S) (a : A) : ℝ :=
  π.prob s a / b.prob s a

/-- p. 278: the expectation `E[f(S_t, A_t, S_{t+1}, R_{t+1})]` of a vector- or matrix-valued
function of one transition when `S_t ∼ µ` ("the distribution of states visited under the behavior
policy"), `A_t ∼ b(· | S_t)` and `(S_{t+1}, R_{t+1}) ∼ p(·, · | S_t, A_t)`:
`Σ_s µ(s) Σ_a b(a|s) Σ_{s'} Σ_{r ∈ R} p(s', r | s, a) f(s, a, s', r)`. -/
def behaviorExp {E : Type} [AddCommMonoid E] [Module ℝ E] (M : MDP S A) (b : SuttonBartoRL.FiniteMDP.Policy S A)
    (μ : S → ℝ) (f : S → A → S → ℝ → E) : E :=
  ∑ s, μ s • ∑ a, b.prob s a • ∑ s', ∑ r ∈ M.R, M.p s a s' r • f s a s' r

end SuttonBartoRL.OffPolicy


