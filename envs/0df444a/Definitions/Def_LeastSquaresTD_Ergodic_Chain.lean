-- Prove2me | Definitions.Def_LeastSquaresTD_Ergodic_Chain
-- name    : LeastSquaresTD_Ergodic_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:36:43.560698+00:00
-- url     : https://prove2.me/theorems/29dd5f13-c6d2-422f-8ef3-6c3a7e250b09
-- title:
--   §2 and Table 1 — a finite Markov chain with transition rewards, ergodicity, invariant distributions, expected reward, value function and feature matrix
-- statement:
--   This file fixes the model of Bradtke and Barto's analysis of LS TD: a fixed policy has been absorbed into the dynamics, so the object is a **finite Markov chain with transition rewards**.
--
--   1. A **chain** on a finite state set $X$ is a transition matrix $P$ with $P(x,y)\ge 0$ and $\sum_{y\in X}P(x,y)=1$ for every $x$.
--   2. The chain is **ergodic** (in the sense of Kemeny and Snell) when every state can be reached from every state: for all $x,y\in X$ there is $n\ge 0$ with $(P^n)(x,y)>0$. Periodic chains are allowed.
--   3. A vector $\pi$ is an **invariant (steady-state) distribution** of $P$ when $\pi_x\ge 0$, $\sum_x \pi_x=1$ and $\pi P=\pi$.
--   4. Given the reward $R(x,y)$ of a transition $x\to y$, the **expected immediate reward** out of $x$ is
--   $$\bar r_x=\sum_{y\in X}P(x,y)\,R(x,y).$$
--   5. For a discount factor $\gamma$, the **value function** is the expected discounted return $V(x)=E\{\sum_{k\ge0}\gamma^k r_k\mid x_0=x\}$, written as the series of expected rewards
--   $$V(x)=\sum_{k=0}^{\infty}\gamma^k\,(P^k\bar r)(x).$$
--   6. Given feature vectors $\phi_x\in\mathbb R^m$, the **feature matrix** $\Phi$ is the $|X|\times m$ matrix whose $x$-th row is $\phi_x$.
--
--   These are the objects in which Theorem 2 and Lemma 5 of the paper are stated.
--
--   **Formalization Note** The paper's "ergodic" is formalized as irreducibility, without aperiodicity (Kemeny–Snell's aperiodic case is called "regular"). $V$ is defined by the series, using $E\{r_k\mid x_0=x\}=(P^k\bar r)(x)$ (Markov property); it is never defined as $(I-\gamma P)^{-1}\bar r$. Lean's infinite sum is $0$ for a divergent series, so every theorem that uses $V$ also asserts that the series converges.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), pp. 34–35, §2 and Table 1; p. 43 (ergodic chain, invariant distribution π, matrix Φ)

import Mathlib

namespace LeastSquaresTD.Ergodic

open Matrix

/-- A finite Markov chain with transition matrix `P` (§2, p. 35: "by a Markov chain we always
mean a finite-state Markov chain"): a row-stochastic matrix on the finite state set `X`. -/
structure Chain (X : Type*) [Fintype X] where
  P : Matrix X X ℝ
  nonneg : ∀ x y, 0 ≤ P x y
  row_sum : ∀ x, ∑ y, P x y = 1

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Kemeny and Snell's *ergodic* chain (cited on p. 43): every state can be reached from every
state, i.e. the chain is irreducible. Periodic chains are allowed (the aperiodic case is
Kemeny–Snell's "regular" chain). -/
def Chain.IsErgodic (C : Chain X) : Prop :=
  ∀ x y : X, ∃ n : ℕ, 0 < (C.P ^ n) x y

/-- `π` is an invariant (steady-state) distribution of `P` (p. 43): a probability vector with
`π P = π`. -/
def Chain.IsStationary (C : Chain X) (π : X → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧ ∑ x, π x = 1 ∧ Matrix.vecMul π C.P = π

/-- Table 1, p. 35: the expected immediate reward `r̄ₓ = ∑_y P(x,y) R(x,y)` for a transition
out of state `x`, where `R(x,y)` is the reward of the transition `x → y`. -/
def Chain.rbar (C : Chain X) (R : X → X → ℝ) (x : X) : ℝ :=
  ∑ y, C.P x y * R x y

/-- The value function (p. 34), `V(x) = E{∑_k γ^k r_k | x₀ = x}`, written as the series of
expected rewards: by the Markov property `E{r_k | x₀ = x} = (P^k r̄)(x)`. Lean's `tsum` is `0`
for a divergent series, so every theorem using `value` also asserts summability. -/
noncomputable def Chain.value (C : Chain X) (R : X → X → ℝ) (γ : ℝ) (x : X) : ℝ :=
  ∑' k : ℕ, γ ^ k * ((C.P ^ k) *ᵥ C.rbar R) x

/-- The feature matrix `Φ` (p. 43): its `x`-th row is the feature vector `φₓ ∈ ℝ^m`. -/
def featureMatrix {m : ℕ} (φ : X → Fin m → ℝ) : Matrix X (Fin m) ℝ :=
  Matrix.of fun x i => φ x i

end LeastSquaresTD.Ergodic


