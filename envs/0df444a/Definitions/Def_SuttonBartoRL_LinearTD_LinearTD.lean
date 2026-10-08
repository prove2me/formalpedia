-- Prove2me | Definitions.Def_SuttonBartoRL_LinearTD_LinearTD
-- name    : SuttonBartoRL_LinearTD_LinearTD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:27:36.636196+00:00
-- url     : https://prove2.me/theorems/e07e2deb-30ae-4505-b895-d077b31877e4
-- title:
--   Linear value approximation, the mean square value error, and the $\mathbf A$, $\mathbf b$ and TD fixed point of linear TD(0)
-- statement:
--   This file defines the objects of Sections 9.2, 9.4 and 9.8 of Sutton and Barto's *Reinforcement Learning: An Introduction*. Throughout, $\mathcal S$ is a finite state set, $d$ a number of features, and $\mathbf X$ an $|\mathcal S| \times d$ real matrix whose row $\mathbf x(s) \in \mathbb R^d$ is the **feature vector** of state $s$.
--
--   1. The **linear approximate value** (9.8): $\hat v(s, \mathbf w) = \mathbf w^\top \mathbf x(s) = \sum_{i=1}^d w_i x_i(s)$ for a weight vector $\mathbf w \in \mathbb R^d$.
--   2. The **mean square value error** (9.1) for a state weighting $\mu$ and a target value function $v$:
--   $$\mathrm{VE}(\mathbf w) = \sum_{s \in \mathcal S} \mu(s)\,\big[v(s) - \hat v(s, \mathbf w)\big]^2 .$$
--   3. A **stationary distribution** $\mu$ of a matrix $P$: $\mu(s) \ge 0$, $\sum_s \mu(s) = 1$ and $\mu^\top P = \mu^\top$.
--   4. **Positive definiteness** in the book's sense (p. 206): a real square matrix $M$, not necessarily symmetric, with $y^\top M y > 0$ for every real vector $y \ne 0$.
--   5. The **key matrix** $\mathbf D(\mathbf I - \gamma \mathbf P)$, where $\mathbf D$ is the diagonal matrix with the $\mu(s)$ on its diagonal.
--   6. One **linear semi-gradient TD(0) update** (9.9) from weight vector $\mathbf w$ on the transition $S_t = s$, $R_{t+1} = r$, $S_{t+1} = s'$, with step size $\alpha$:
--   $$\mathbf w + \alpha\big(r + \gamma\,\mathbf w^\top \mathbf x(s') - \mathbf w^\top \mathbf x(s)\big)\,\mathbf x(s).$$
--   7. The vector $\mathbf b = \mathbb E[R_{t+1}\mathbf x_t]$ and the matrix $\mathbf A = \mathbb E[\mathbf x_t(\mathbf x_t - \gamma \mathbf x_{t+1})^\top]$ of (9.11), computed in steady state for a finite MDP, a policy $\pi$ and a state distribution $\mu$ (so $S_t \sim \mu$, $A_t \sim \pi(\cdot \mid S_t)$, $(S_{t+1}, R_{t+1}) \sim p(\cdot, \cdot \mid S_t, A_t)$):
--   $$\mathbf b = \sum_s \mu(s) \sum_a \pi(a \mid s) \sum_{s', r} p(s', r \mid s, a)\, r\, \mathbf x(s), \qquad \mathbf A = \sum_s \mu(s) \sum_a \pi(a \mid s) \sum_{s', r} p(s', r \mid s, a)\, \mathbf x(s)\big(\mathbf x(s) - \gamma \mathbf x(s')\big)^\top .$$
--   8. The **TD fixed point** (9.12): $\mathbf w_{\mathrm{TD}} = \mathbf A^{-1}\mathbf b$.
--   9. The **LSTD estimate** (9.20) built from a sequence of feature vectors $\mathbf x_0, \mathbf x_1, \dots$: $\hat{\mathbf A}_t = \sum_{k=0}^{t-1} \mathbf x_k(\mathbf x_k - \gamma \mathbf x_{k+1})^\top + \varepsilon \mathbf I$, so that $\hat{\mathbf A}_0 = \varepsilon \mathbf I$.
--
--   These are the objects about which the box "Proof of Convergence of Linear TD(0)" and the error bound (9.14) speak.
--
--   **Formalization Note** Positive definiteness is not Mathlib's `Matrix.PosDef`, which requires a symmetric (Hermitian) matrix; the key matrix and $\mathbf A$ are not symmetric. The TD fixed point uses Mathlib's matrix inverse, which is the zero matrix for a singular matrix; the theorems of the mission prove that $\mathbf A$ is invertible under the book's hypotheses before using $\mathbf w_{\mathrm{TD}}$. $\mathbf A$ and $\mathbf b$ are defined as the book's expectations (9.11), not from the matrix form $\mathbf X^\top \mathbf D(\mathbf I - \gamma \mathbf P)\mathbf X$, which is a theorem.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (9.1), p. 199; Eqs. (9.8)–(9.9), p. 205; Eqs. (9.11)–(9.12) and box "Proof of Convergence of Linear TD(0)", pp. 206–207; Eq. (9.20), p. 228

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP

open Matrix

namespace SuttonBartoRL.LinearTD

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}

/-- (9.8), p. 205: the linear approximate value `v̂(s, w) = wᵀx(s) = Σ_i w_i x_i(s)`. The features are
the rows of the `|S| × d` matrix `X`, `x(s) = X s` (p. 207: "X is the |S| × d matrix with x(s) as
its rows"). -/
def vhat (X : Matrix S (Fin d) ℝ) (w : Fin d → ℝ) (s : S) : ℝ :=
  w ⬝ᵥ X s

/-- (9.1), p. 199: the mean square value error
`VE(w) = Σ_{s ∈ S} µ(s) [v(s) − v̂(s, w)]²` of the weight vector `w`, for a state weighting `µ` and
a target value function `v` (in the theorems, `v = v_π`, the true value function). -/
def VE (μ : S → ℝ) (v : S → ℝ) (X : Matrix S (Fin d) ℝ) (w : Fin d → ℝ) : ℝ :=
  ∑ s, μ s * (v s - vhat X w s) ^ 2

/-- p. 199 and p. 207: `µ` is a stationary distribution of the row-stochastic matrix `P`:
`µ(s) ≥ 0`, `Σ_s µ(s) = 1`, and `µᵀP = µᵀ` (equivalently `µ = Pᵀµ`). -/
def IsStationaryDist (P : Matrix S S ℝ) (μ : S → ℝ) : Prop :=
  (∀ s, 0 ≤ μ s) ∧ ∑ s, μ s = 1 ∧ vecMul μ P = μ

/-- p. 206: a real square matrix `M`, not necessarily symmetric, is *positive definite* in the
book's sense, `yᵀMy > 0` for every real vector `y ≠ 0`. (Not Mathlib's `Matrix.PosDef`, which also
requires `M` to be symmetric.) -/
def IsPosDefNonsym {n : Type} [Fintype n] (M : Matrix n n ℝ) : Prop :=
  ∀ y : n → ℝ, y ≠ 0 → 0 < y ⬝ᵥ (M *ᵥ y)

/-- p. 207: the "key matrix" `D(I − γP)`, where `D = diag(µ)`. -/
def keyMatrix (μ : S → ℝ) (P : Matrix S S ℝ) (γ : ℝ) : Matrix S S ℝ :=
  diagonal μ * (1 - γ • P)

/-- (9.9), p. 205: one linear semi-gradient TD(0) update from weight vector `w` on the transition
`S_t = s`, `R_{t+1} = r`, `S_{t+1} = s'`, with step size `α`:
`w + α (r + γ wᵀx(s') − wᵀx(s)) x(s)`. -/
def tdUpdate (X : Matrix S (Fin d) ℝ) (γ α : ℝ) (w : Fin d → ℝ) (s : S) (r : ℝ) (s' : S) :
    Fin d → ℝ :=
  w + (α * (r + γ * (w ⬝ᵥ X s') - w ⬝ᵥ X s)) • X s

/-- (9.11), p. 206: `b = E[R_{t+1} x_t] ∈ ℝ^d` in steady state, with `S_t ∼ µ`, `A_t ∼ π(·|S_t)` and
`(S_{t+1}, R_{t+1}) ∼ p(·, · | S_t, A_t)`:
`b = Σ_s µ(s) Σ_a π(a|s) Σ_{s', r} p(s', r | s, a) r x(s)`. -/
def tdB (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (X : Matrix S (Fin d) ℝ) : Fin d → ℝ :=
  ∑ s, μ s • ∑ a, π.prob s a • ∑ s', ∑ r ∈ M.R, (M.p s a s' r * r) • X s

/-- (9.11), p. 206, and the first line of the box on p. 206: `A = E[x_t (x_t − γ x_{t+1})ᵀ] ∈ ℝ^{d×d}`
in steady state, `A = Σ_s µ(s) Σ_a π(a|s) Σ_{s', r} p(s', r | s, a) x(s)(x(s) − γ x(s'))ᵀ`. -/
def tdA (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (X : Matrix S (Fin d) ℝ) (γ : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ s, μ s • ∑ a, π.prob s a • ∑ s', ∑ r ∈ M.R, M.p s a s' r • vecMulVec (X s) (X s - γ • X s')

/-- (9.12), p. 206: the TD fixed point `w_TD = A⁻¹ b`. `⁻¹` is Mathlib's matrix inverse, which is
`0` for a singular matrix; the theorems prove that `A` is invertible under the book's hypotheses. -/
noncomputable def tdFixedPoint (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ)
    (X : Matrix S (Fin d) ℝ) (γ : ℝ) : Fin d → ℝ :=
  (tdA M π μ X γ)⁻¹ *ᵥ tdB M π μ X

/-- (9.20), p. 228: the LSTD estimate `Â_t = Σ_{k=0}^{t−1} x_k (x_k − γ x_{k+1})ᵀ + εI` built from a
sequence of feature vectors `x_0, x_1, …` (so `Â_0 = εI`). -/
def lstdA (γ ε : ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ k ∈ Finset.range t, vecMulVec (x k) (x k - γ • x (k + 1)) + ε • (1 : Matrix (Fin d) (Fin d) ℝ)

end SuttonBartoRL.LinearTD


