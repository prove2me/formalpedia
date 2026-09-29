-- Prove2me | Definitions.Def_MarkovChain
-- name    : MarkovChain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-12T18:57:49.157905+00:00
-- url     : https://prove2.me/theorems/2b2077a3-0dc2-46b5-b82e-b2970241a4da
-- title:
--   Finite Markov chains: stationary distributions, total variation, Doeblin minorization
-- statement:
--   Mathlib knows what a row-stochastic matrix is — `Matrix.rowStochastic` is the submonoid of matrices with nonnegative entries and row sums $1$, together with basic API (entries are at most $1$, the set is convex, permutation matrices belong to it, it is closed under products). What Mathlib carries no trace of is the *probabilistic* theory built on that object: there is no stationary distribution, no total variation distance, no minorization condition, and no convergence theorem. This bundle supplies the vocabulary for that theory over a finite state space.
--
--   Two deliberate choices keep the development free of duplication. A **distribution** on the state space is a point of `stdSimplex ℝ n`, so no new predicate is introduced for "probability vector" and the compactness of the simplex is available for free. The **transition operator on distributions** is Mathlib's `vecMul`: the chain acts on the right, $\mu \mapsto \mu M$, so that the $k$-step transition matrix is literally `M ^ k`, and the Chapman–Kolmogorov identity $\mu M^{j+k} = (\mu M^{j})M^{k}$ is `pow_add` together with `vecMul_vecMul` — nothing to define and nothing to prove.
--
--   * **`IsStationary M π`** — $\pi$ is a probability vector with $\pi M = \pi$. Equilibria of the chain.
--
--   * **`tvDist μ ν`** — the **total variation distance** $\tfrac12\sum_i |\mu_i - \nu_i|$. This is the standard metric in which finite chains converge: on distributions it equals $\sup_A |\mu(A) - \nu(A)|$ and takes values in $[0,1]$. It is defined on arbitrary vectors, not only distributions, so that the triangle inequality and the metric axioms hold unconditionally.
--
--   * **`IsDoeblin M ε ν`** — **Doeblin's minorization condition**: there are a distribution $\nu$ and a constant $\varepsilon > 0$ with $M_{ij} \ge \varepsilon\,\nu_j$ for all states. Informally, from every starting state the chain has probability at least $\varepsilon$ of being redistributed according to the *same* measure $\nu$ in one step, which is what forbids the state space from splitting into non-communicating pieces or from cycling. It is the hypothesis under which the transition operator is a strict contraction for `tvDist`, and every matrix with positive entries satisfies it.
--
--   * **`IsReversible M π`** — **detailed balance**, $\pi_i M_{ij} = \pi_j M_{ji}$. Reversible chains are those whose stationary distribution can be read off without solving a linear system, and they are the ones that arise in practice (random walks on weighted graphs, Metropolis chains).
--
--   * **`unif n`** — the uniform distribution on the state space.
--
--   The only constraint on the state space is that it be a `Fintype` with decidable equality, as `Matrix.rowStochastic` already requires; no nonemptiness is assumed in the definitions, since the theorems that need it derive it from the existence of a distribution.
-- source:
--   D. A. Levin, Y. Peres, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Chapter 1 (stationary distributions, reversibility) and Chapter 4 (total variation distance, convergence to equilibrium). Row-stochastic matrices themselves are Mathlib's `Matrix.rowStochastic`.

import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite Markov chains: stationary distributions and convergence to equilibrium

Mathlib knows what a row-stochastic matrix is
(`Matrix.rowStochastic`: nonnegative entries, row sums `1`, a submonoid of
`Matrix n n R`), but it carries no probabilistic theory on top of it: there is
no notion of a stationary distribution, no total variation distance, no
minorization condition and no convergence theorem.  This bundle supplies the
vocabulary for that theory over a finite state space.

A **distribution** on the state space `n` is a point of `stdSimplex ℝ n`; no
new definition is introduced for it, and the transition operator on
distributions is Mathlib's `vecMul`, so that the `k`-step transition matrix is
literally `M ^ k` and the Chapman–Kolmogorov identity is `vecMul_vecMul`.

* `IsStationary M π` — `π` is a distribution fixed by the chain.
* `tvDist μ ν` — total variation distance, `½ ∑ |μ i - ν i|`, the standard
  metric in which finite chains converge.
* `IsDoeblin M ε ν` — Doeblin's minorization condition: every row of `M`
  dominates `ε` times one fixed distribution `ν`.  It is the hypothesis under
  which the transition operator is a strict contraction for `tvDist`, and it
  holds for every matrix with positive entries.
* `IsReversible M π` — detailed balance.
* `unif n` — the uniform distribution.
-/

namespace MarkovChain

open Finset Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `π` is a **stationary distribution** of the chain with transition matrix
`M`: a probability vector with `π M = π`.  The transition operator acts on
distributions on the right, so `k` steps is `π ᵥ* M ^ k`. -/
def IsStationary (M : Matrix n n ℝ) (π : n → ℝ) : Prop :=
  π ∈ stdSimplex ℝ n ∧ π ᵥ* M = π

/-- The **total variation distance** between two vectors,
`‖μ - ν‖₁ / 2`.  On distributions it agrees with
`sup_{A} |μ(A) - ν(A)|` and takes values in `[0,1]`. -/
noncomputable def tvDist (μ ν : n → ℝ) : ℝ :=
  (∑ i, |μ i - ν i|) / 2

/-- **Doeblin's minorization condition**: there is a distribution `ν` and a
constant `ε > 0` with `M i j ≥ ε ν j` for all states `i, j` — from every
starting state the chain has probability at least `ε` of being distributed
according to `ν` after one step.  This is the standard sufficient condition
for a unique stationary distribution and geometric convergence to it. -/
def IsDoeblin (M : Matrix n n ℝ) (ε : ℝ) (ν : n → ℝ) : Prop :=
  0 < ε ∧ ν ∈ stdSimplex ℝ n ∧ ∀ i j, ε * ν j ≤ M i j

/-- **Detailed balance** (reversibility) of `M` with respect to `π`:
`π i M i j = π j M j i` for all states.  Reversible chains are the ones for
which a stationary distribution can be read off without solving a linear
system. -/
def IsReversible (M : Matrix n n ℝ) (π : n → ℝ) : Prop :=
  ∀ i j, π i * M i j = π j * M j i

/-- The uniform distribution on a finite state space. -/
noncomputable def unif (n : Type*) [Fintype n] : n → ℝ :=
  fun _ => ((Fintype.card n : ℝ))⁻¹

end MarkovChain


