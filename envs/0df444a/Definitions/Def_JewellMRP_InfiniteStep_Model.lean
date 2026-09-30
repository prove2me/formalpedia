-- Prove2me | Definitions.Def_JewellMRP_InfiniteStep_Model
-- name    : JewellMRP_InfiniteStep_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:28:07.091991+00:00
-- url     : https://prove2.me/theorems/c49a3615-3982-4a9a-953c-2623e5967b22
-- title:
--   Fixed-policy infinite-step model: ergodic chain, stationary vector, $\Pi$, gain, fundamental matrix, $n$-step return and bias
-- statement:
--   This file fixes the objects of the infinite-step, undiscounted Markov-renewal model under one stationary policy (Jewell, *Markov-Renewal Programming II*, 1963). Let $S$ be a finite set of states.
--
--   1. **Ergodic chain.** A real matrix $P = (p_{ij})_{i,j \in S}$ is *ergodic* if it is row-stochastic ($p_{ij} \ge 0$ and $\sum_j p_{ij} = 1$ for every $i$) and irreducible (the directed graph with an edge $i \to j$ whenever $p_{ij} > 0$ is strongly connected). Periodic chains are allowed.
--   2. **Stationary vector.** A vector $\pi \in \mathbb R^S$ is a *stationary probability vector* of $P$ if $\pi_i \ge 0$, $\sum_i \pi_i = 1$ and $\pi P = \pi$.
--   3. **The matrix $\Pi$.** Given $\pi$, $\Pi$ is the $S \times S$ matrix every row of which is $\pi$, i.e. $\Pi_{ij} = \pi_j$.
--   4. **Gain.** For a reward vector $\rho$, the system gain is $G = \sum_i \pi_i \rho_i$ (A 6).
--   5. **Fundamental matrix.** $Z = (I - P + \Pi)^{-1}$ (A 7).
--   6. **$n$-step return.** For one-step expected rewards $\rho \in \mathbb R^S$ and terminal rewards $V(0) \in \mathbb R^S$, the expected return of the fixed policy after $n$ transitions is defined by the recursion (I 16) without the maximum,
--   $$V(0) = V(0), \qquad V_i(n) = \rho_i + \sum_{j} p_{ij} V_j(n-1), \quad n \ge 1.$$
--   7. **Bias.** $W_i(n) = V_i(n) - G n$ with $G = \sum_i \pi_i\rho_i$.
--   8. **Cesàro mean.** For a sequence $f(1), f(2), \dots$ in a real vector space, $\frac1n \sum_{m=1}^n f(m)$.
--
--   These objects are shared by every statement of the mission; the theorems relate them.
--
--   **Formalization Note** States are an arbitrary finite type with decidable equality; the theorems add `Nonempty`. Mathlib's matrix inverse returns $0$ on a singular matrix, so every statement involving $Z$ also asserts, or relies on a milestone asserting, that $I - P + \Pi$ is invertible. Irreducibility is Mathlib's `Matrix.IsIrreducible` (nonnegative entries and positive-length strong connectivity of the positive-entry graph), which for a nonempty row-stochastic matrix is the usual notion. The Cesàro mean at $n = 0$ is $0$, which is irrelevant for limits. The paper's $\rho_i$ is the integral expression (I 17); only the vector $\rho$ enters these results, and every real vector arises from some reward structure, so $\rho$ is taken as an arbitrary real vector.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), p. 951, assumption 2 and Eq. (I 16); p. 952, Eqs. (A 6), (A 7); p. 966, Appendix A

import Mathlib

namespace JewellMRP.InfiniteStep

open Matrix

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Assumption 2 (p. 951): the embedded chain of the fixed stationary policy is ergodic, i.e.
`P` is a row-stochastic matrix (nonnegative entries, every row sums to one) that is
irreducible. Periodic chains are allowed. -/
def IsErgodic (P : Matrix S S ℝ) : Prop :=
  P ∈ Matrix.rowStochastic ℝ S ∧ P.IsIrreducible

/-- `π` is a stationary probability vector of `P`: nonnegative, summing to one, and `π P = π`. -/
def IsStationary (P : Matrix S S ℝ) (π : S → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1 ∧ π ᵥ* P = π

/-- The matrix `Π` every row of which is the row vector `π`: `Π i j = π j`. -/
def limitMatrix (π : S → ℝ) : Matrix S S ℝ :=
  Matrix.of fun _ j => π j

/-- The system gain `G = ∑ i, π i * ρ i` (A 6). -/
def gain (π ρ : S → ℝ) : ℝ :=
  ∑ i, π i * ρ i

/-- The fundamental matrix `Z = (I - P + Π)⁻¹` (A 7). (Mathlib's `⁻¹` returns `0` on a singular
matrix; every statement using `Z` comes with, or is preceded by, the invertibility of
`I - P + Π`.) -/
noncomputable def fundamentalMatrix (P : Matrix S S ℝ) (π : S → ℝ) : Matrix S S ℝ :=
  (1 - P + limitMatrix π)⁻¹

/-- The `n`-step expected return (I 16) under a fixed stationary policy:
`V(0)` is the terminal reward vector and `V(n) = ρ + P V(n-1)` for `n ≥ 1`. -/
def stepReturn (P : Matrix S S ℝ) (ρ V0 : S → ℝ) : ℕ → S → ℝ
  | 0 => V0
  | n + 1 => ρ + P *ᵥ stepReturn P ρ V0 n

/-- The bias vector after `n` steps, `W_i(n) = V_i(n) - G n`, with `G = gain π ρ`. -/
def biasSeq (P : Matrix S S ℝ) (π ρ V0 : S → ℝ) (n : ℕ) : S → ℝ :=
  stepReturn P ρ V0 n - fun _ => gain π ρ * (n : ℝ)

/-- The Cesàro mean `(1/n) ∑_{m=1}^{n} f(m)` of a sequence `f` in a real vector space
(it equals `0` at `n = 0`). -/
noncomputable def cesaroMean {E : Type*} [AddCommGroup E] [Module ℝ E] (f : ℕ → E) (n : ℕ) : E :=
  (n : ℝ)⁻¹ • ∑ m ∈ Finset.Icc 1 n, f m

end JewellMRP.InfiniteStep


