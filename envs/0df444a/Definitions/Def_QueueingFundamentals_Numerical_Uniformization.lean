-- Prove2me | Definitions.Def_QueueingFundamentals_Numerical_Uniformization
-- name    : QueueingFundamentals_Numerical_Uniformization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T20:04:31.756987+00:00
-- url     : https://prove2.me/theorems/e74185b7-c322-40e8-b7ee-198a513c8cff
-- title:
--   Generators, the uniformized matrix $\tilde P = Q/\Lambda + I$, and the randomization sum
-- statement:
--   Consider a continuous-time Markov chain $X(t)$ on the finite state space $\{0,1,\dots,N\}$ with **infinitesimal generator** $Q=(q_{ij})$: the off-diagonal entries $q_{ij}$ ($i\ne j$) are nonnegative transition rates and the diagonal entries are $-q_i$, where
--
--   $$q_i=\sum_{j\ne i} q_{ij},\qquad i=0,1,\dots,N.$$
--
--   This file introduces the objects of the randomization (uniformization) technique of §8.1.2.2:
--
--   1. the predicate that $Q$ is such a generator, and the **exit rate** $q_i=-q_{ii}$ of state $i$;
--   2. for a constant $\Lambda$, the **uniformized matrix** $\tilde P=Q/\Lambda+I$;
--   3. the Poisson probabilities $e^{-\Lambda t}(\Lambda t)^k/k!$, $k=0,1,2,\dots$;
--   4. probability vectors (nonnegative entries summing to one) and stochastic matrices (nonnegative entries, every row summing to one);
--   5. the **forward equations**: a function $p:[0,\infty)\to\mathbb R^{N+1}$ solves them with initial vector $p(0)$ when $p'(t)=p(t)Q$ for all $t\ge 0$, the row vector $p(t)=(p_0(t),\dots,p_N(t))$ being the transient state-probability vector $p_n(t)=\Pr\{X(t)=n\}$;
--   6. the vectors $\phi^{(k)}=p(0)\tilde P^{(k)}$, the distribution of the uniformized chain $Y_k$ after $k$ transitions, where $\tilde P^{(k)}=\tilde P^k$;
--   7. the truncated randomization sum
--   $$\sum_{k=0}^{T}\phi^{(k)}\,\frac{e^{-\Lambda t}(\Lambda t)^k}{k!}.$$
--
--   These are the notions in terms of which Eqs. (8.7)–(8.14) are stated.
--
--   **Formalization Note** States are `Fin (N+1)`. Row vectors are functions `Fin (N+1) → ℝ` and the product $p\,Q$ is `vecMul`. The derivative in the forward equations is one-sided (within $[0,\infty)$), so the equations say nothing about negative times. $\Lambda$ is a free parameter here; the theorems require $\Lambda>0$ and $\Lambda\ge q_i$ for all $i$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.381–384, §8.1.2.2 (generator p.384 with q_i = Σ_{j≠i} q_ij; Λ p.382; P̃ = Q/Λ + I p.383; φ^(k) and Eqs. (8.11), (8.13)–(8.14) p.384)

import Mathlib

open Matrix

namespace QueueingFundamentals.Numerical

/-- `Q` is the infinitesimal generator of a continuous-time Markov chain on the states
`0, 1, …, N` (Gross et al., §8.1.2.2, p.384): every off-diagonal entry `q_ij` (`i ≠ j`) is
nonnegative and every diagonal entry is `−q_i`, where `q_i = ∑_{j ≠ i} q_ij`. -/
def IsGenerator {N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : Prop :=
  (∀ i j, i ≠ j → 0 ≤ Q i j) ∧ ∀ i, Q i i = -∑ j ∈ Finset.univ.erase i, Q i j

/-- The total rate `q_i = −Q i i` out of state `i` (the diagonal of `Q` is `−q_i`, p.382, p.384). -/
def exitRate {N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (i : Fin (N + 1)) : ℝ :=
  -Q i i

/-- The uniformized (randomized) transition matrix `P̃ = Q/Λ + I` (p.383, Eq. (8.13)). -/
noncomputable def uniformizedMatrix {N : ℕ} (Λ : ℝ) (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Λ⁻¹ • Q + 1

/-- The Poisson probability `e^{−Λt} (Λt)^k / k!` that a Poisson process of rate `Λ` has
exactly `k` occurrences in `[0, t]` (the weights in (8.8)–(8.14)). -/
noncomputable def poissonWeight (Λ t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-(Λ * t)) * (Λ * t) ^ k / (k.factorial : ℝ)

/-- A probability vector on the states `0, …, N`: nonnegative entries summing to one. -/
def IsProbVec {N : ℕ} (p : Fin (N + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- A stochastic matrix: nonnegative entries, every row summing to one. -/
def IsStochastic {N : ℕ} (P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- `p : [0, ∞) → ℝ^{N+1}` solves the forward (Kolmogorov) equations `p′(t) = p(t) Q`
(p.381) for `t ≥ 0`, with initial vector `p(0) = p₀`. The row vector `p(t)` is the transient
state-probability vector `p_n(t) = Pr{X(t) = n}`. The derivative at `t = 0` is one-sided. -/
def SolvesForward {N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p₀ : Fin (N + 1) → ℝ)
    (p : ℝ → Fin (N + 1) → ℝ) : Prop :=
  p 0 = p₀ ∧ ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt p (p t ᵥ* Q) (Set.Ici 0) t

/-- `φ^{(k)} = p(0) P̃^{(k)}`, the state distribution of the uniformized chain `Y_k` after `k`
occurrences of the Poisson(`Λ`) process (p.384). -/
noncomputable def phi {N : ℕ} (Λ : ℝ) (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (p₀ : Fin (N + 1) → ℝ) (k : ℕ) : Fin (N + 1) → ℝ :=
  p₀ ᵥ* (uniformizedMatrix Λ Q ^ k)

/-- The truncated randomization sum `∑_{k=0}^{T} φ^{(k)} e^{−Λt}(Λt)^k/k!` of (8.11) and (8.14),
truncated at `T = T(t, ε)`. -/
noncomputable def truncatedSolution {N : ℕ} (Λ : ℝ) (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (p₀ : Fin (N + 1) → ℝ) (t : ℝ) (T : ℕ) : Fin (N + 1) → ℝ :=
  ∑ k ∈ Finset.range (T + 1), poissonWeight Λ t k • phi Λ Q p₀ k

end QueueingFundamentals.Numerical


