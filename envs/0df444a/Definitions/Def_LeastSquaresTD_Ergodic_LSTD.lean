-- Prove2me | Definitions.Def_LeastSquaresTD_Ergodic_LSTD
-- name    : LeastSquaresTD_Ergodic_LSTD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:01:21.350465+00:00
-- url     : https://prove2.me/theorems/41740e9c-5ba0-4142-838f-a3a04377acb3
-- title:
--   Eq. (11) and Figure 3 — the Markov path law, visit counts, the LS TD estimate and Lemma 5's matrix
-- statement:
--   This file defines the on-line process of Figure 3 and the LS TD estimate (11) of Bradtke and Barto.
--
--   1. A vector $\nu$ on $X$ is a **probability vector** if $\nu_x\ge0$ and $\sum_x\nu_x=1$.
--   2. A process $Z_0,Z_1,\dots$ of $X$-valued random variables on a probability space $(\Omega,\mu)$ is a **Markov chain with initial law $\nu$ and transition matrix $P$** if every event $\{Z_t=x\}$ is measurable and, for every $n$ and states $x_0,\dots,x_n$,
--   $$\mu\{Z_0=x_0,\dots,Z_n=x_n\}=\nu_{x_0}\,P(x_0,x_1)\cdots P(x_{n-1},x_n).$$
--   3. Along a path $z=(z_0,z_1,\dots)$, the **visit count** $N_t(x)=\#\{k<t: z_k=x\}$ counts the visits to $x$ among the first $t$ states, and the **transition count** $N_t(x,y)=\#\{k<t: z_k=x,\ z_{k+1}=y\}$ counts the transitions $x\to y$ among the first $t$ transitions.
--   4. With features $\phi_x\in\mathbb R^m$, rewards $R$ and discount $\gamma$, the **LS TD estimate** after $t$ transitions is
--   $$\theta_t=\Big[\frac1t\sum_{k=0}^{t-1}\phi_{z_k}\big(\phi_{z_k}-\gamma\phi_{z_{k+1}}\big)'\Big]^{-1}\Big[\frac1t\sum_{k=0}^{t-1}\phi_{z_k}\,R(z_k,z_{k+1})\Big].$$
--   5. For weights $\pi$ on $X$, with $\Pi=\operatorname{diag}(\pi)$, **Lemma 5's matrix and vector** are $\Phi'\Pi(I-\gamma P)\Phi$ and $\Phi'\Pi\bar r$.
--
--   The estimate is the instrumental-variable least-squares solution of the consistency condition (9); Theorem 2 concerns its behaviour as $t\to\infty$ along the path of the chain.
--
--   **Formalization Note** The paper writes (11) with $k=1,\dots,t$ and $\phi_{k+1}$; Figure 3 starts at $x_0$ and performs the transition $x_t\to x_{t+1}$ before using (11), so the estimate after $t$ transitions uses $k=0,\dots,t-1$. This index shift does not affect the limit. The factors $1/t$ are kept as printed (at $t=0$ both brackets are $0$). When the matrix is singular, Lean's matrix inverse returns the zero matrix; the paper says only that "$\theta_t$ is not well defined when $t$ is small since the matrix is not invertible", and a junk value at finitely many times does not affect convergence. No regularization $\varepsilon I$ and no pseudo-inverse are used. The Markov law is a hypothesis on an arbitrary probability space (it is satisfiable, by the Ionescu-Tulcea theorem).
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), p. 42, Eq. (11); p. 43, Figure 3 and Lemma 5

import Mathlib
import Definitions.Def_LeastSquaresTD_Ergodic_Chain

namespace LeastSquaresTD.Ergodic

open MeasureTheory Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A probability vector on the finite state set (an initial law). -/
def IsProbVec (ν : X → ℝ) : Prop :=
  (∀ x, 0 ≤ ν x) ∧ ∑ x, ν x = 1

/-- The process `Z₀, Z₁, …` on the probability space `(Ω, μ)` is a Markov chain with initial law
`ν` and transition matrix `C.P` (Figure 3, p. 43, line 4): every event `{Zₜ = x}` is measurable
and for every `n` and states `x₀, …, xₙ`,
`μ{Z₀ = x₀, …, Zₙ = xₙ} = ν(x₀) P(x₀,x₁) ⋯ P(x_{n-1},xₙ)`. -/
def IsMarkovLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (C : Chain X) (ν : X → ℝ)
    (Z : ℕ → Ω → X) : Prop :=
  (∀ (n : ℕ) (x : X), MeasurableSet {ω | Z n ω = x}) ∧
  ∀ (n : ℕ) (xs : Fin (n + 1) → X),
    μ {ω | ∀ i : Fin (n + 1), Z (i : ℕ) ω = xs i} =
      ENNReal.ofReal (ν (xs 0) * ∏ i : Fin n, C.P (xs i.castSucc) (xs i.succ))

/-- The number of visits `#{k < t : z k = x}` of the path `z` to `x` among its first `t` states. -/
def visitCount (z : ℕ → X) (x : X) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun k => z k = x)).card

/-- The number of observed transitions `x → y` among the first `t` transitions of the path:
`#{k < t : z k = x ∧ z (k+1) = y}`. -/
def pairCount (z : ℕ → X) (x y : X) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun k => z k = x ∧ z (k + 1) = y)).card

/-- The matrix of (11), p. 42, over the first `t` observed transitions `z 0 → z 1 → ⋯ → z t`:
`(1/t) ∑_{k<t} φ_{z k} (φ_{z k} − γ φ_{z (k+1)})'`. -/
noncomputable def lstdA {m : ℕ} (φ : X → Fin m → ℝ) (γ : ℝ) (t : ℕ) (z : ℕ → X) :
    Matrix (Fin m) (Fin m) ℝ :=
  (1 / (t : ℝ)) • ∑ k ∈ Finset.range t,
    Matrix.vecMulVec (φ (z k)) (φ (z k) - γ • φ (z (k + 1)))

/-- The vector of (11), p. 42: `(1/t) ∑_{k<t} φ_{z k} r_k` with `r_k = R(z k, z (k+1))`. -/
noncomputable def lstdB {m : ℕ} (φ : X → Fin m → ℝ) (R : X → X → ℝ) (t : ℕ) (z : ℕ → X) :
    Fin m → ℝ :=
  (1 / (t : ℝ)) • ∑ k ∈ Finset.range t, R (z k) (z (k + 1)) • φ (z k)

/-- The LS TD estimate (11), p. 42: `θₜ = [lstdA]⁻¹ [lstdB]`. Lean's `⁻¹` is the zero matrix
when `lstdA` is singular (the paper: "θₜ is not well defined when t is small"). -/
noncomputable def lstdTheta {m : ℕ} (φ : X → Fin m → ℝ) (R : X → X → ℝ) (γ : ℝ) (t : ℕ)
    (z : ℕ → X) : Fin m → ℝ :=
  (lstdA φ γ t z)⁻¹ *ᵥ lstdB φ R t z

/-- Lemma 5's matrix `Φ'Π(I − γP)Φ` (p. 43), `Π = diag(π)`. -/
noncomputable def lemma5Matrix (C : Chain X) {m : ℕ} (φ : X → Fin m → ℝ) (π : X → ℝ) (γ : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  (featureMatrix φ)ᵀ * Matrix.diagonal π * (1 - γ • C.P) * featureMatrix φ

/-- Lemma 5's vector `Φ'Π r̄` (p. 43). -/
noncomputable def lemma5Vector (C : Chain X) (R : X → X → ℝ) {m : ℕ} (φ : X → Fin m → ℝ)
    (π : X → ℝ) : Fin m → ℝ :=
  ((featureMatrix φ)ᵀ * Matrix.diagonal π) *ᵥ C.rbar R

end LeastSquaresTD.Ergodic


