-- Prove2me | Definitions.Def_FosterQueues_MG1_Model
-- name    : FosterQueues_MG1_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:04:08.754762+00:00
-- url     : https://prove2.me/theorems/f0978f44-b04d-4485-a397-8380b9066838
-- title:
--   The M/G/1 matrix of §3, ρ = Σ n kₙ in [0, ∞], recurrence, transience and mean first-passage times
-- statement:
--   This file fixes the objects of Foster's treatment of the queueing system M/G/1 (Foster 1953, §3, p. 358). It builds on the published vocabulary of discrete-parameter Markov chains on the states $\{0,1,2,\dots\}$: a transition matrix $P=[p_{ij}]$ with nonnegative entries and rows summing to one, its first-passage probabilities $f_{ij}^{(n)}$ and its return probabilities $f_{jj}=\sum_{n\ge1}f_{jj}^{(n)}$.
--
--   1. **The M/G/1 matrix.** Given a sequence $k_0,k_1,k_2,\dots$, the M/G/1 matrix is
--   $$
--   [p_{ij}] = \begin{bmatrix} k_0 & k_1 & k_2 & \cdots \\ k_0 & k_1 & k_2 & \cdots \\ 0 & k_0 & k_1 & \cdots \\ 0 & 0 & k_0 & \cdots \\ \vdots & \vdots & \vdots & \end{bmatrix},
--   $$
--   that is, $p_{0j}=k_j$, and for $i\ge1$, $p_{ij}=k_{j-i+1}$ when $j\ge i-1$ and $p_{ij}=0$ otherwise. Rows $0$ and $1$ coincide.
--   2. **The traffic intensity.** $\rho=\sum_{n=1}^{\infty}n k_n$, taken in $[0,\infty]$, so that $\rho=\infty$ when the series diverges.
--   3. **Recurrence and transience of the system.** The system is *recurrent* if every state $j$ has $f_{jj}=1$, and *transient* if every state $j$ has $f_{jj}<1$.
--   4. **Mean first-passage times.** $\mu_{ij}=\sum_{n\ge1}n f_{ij}^{(n)}\in[0,\infty]$, the mean time to go from state $i$ to state $j$ (for $i=j$, the mean recurrence time).
--
--   These are the notions in which Foster's classification of the M/G/1 imbedded chain and the general criteria of his §2 are stated.
--
--   **Formalization Note** The matrix is a plain function of the sequence $k$; theorems about the M/G/1 system quantify over a transition matrix $P$ whose entries equal it. Both $\rho$ and $\mu_{ij}$ are extended nonnegative reals, so an infinite mean is representable rather than collapsing to $0$. "Ergodic" (recurrent-nonnull) is the published notion of positive recurrence (every state has $f_{jj}=1$ and finite mean recurrence time) and is not redefined here. Recurrence and transience are defined state by state over all states; for an irreducible chain they are complementary (class solidarity), which is a theorem, not part of the definition. The sum defining $\mu_{ij}$ is the mean first-passage time only when passage from $i$ to $j$ is certain ($f_{ij}=1$), as it is in an irreducible ergodic system, the only setting in which the paper uses $\mu_{ij}$; for a defective passage the sum is finite and is not the (infinite) mean.
-- source:
--   Foster (Ann. Math. Statist. 24, 1953), §1, p. 355 (recurrent/transient/ergodic) and §3, p. 358 (the matrix and ρ, the mean first-passage times μ_{ij})

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain

open scoped ENNReal
open QueueingFundamentals.Foundations

namespace FosterQueues.MG1

/-- The entries of the M/G/1 matrix of Foster (1953), §3, p. 358:
row `0` is `k₀ k₁ k₂ ⋯`, and for `i ≥ 1` row `i` is `k_{j-i+1}` in column `j ≥ i - 1` and `0` to the
left of it (so rows `0` and `1` coincide). States are indexed from `0`, as in the paper. The natural
subtraction `j + 1 - i` is only evaluated when `i ≤ j + 1`. -/
def mg1Matrix (k : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i = 0 then k j else if i ≤ j + 1 then k (j + 1 - i) else 0

/-- `ρ = ∑_{n ≥ 1} n kₙ` (§3, p. 358), valued in `[0, ∞]` so that a divergent series gives `ρ = ∞`.
The `n = 0` term vanishes. -/
noncomputable def rho (k : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (k n)

/-- The system is recurrent (Feller's "persistent"): every state is returned to with probability
one, `f_jj = 1` for all `j`. -/
def IsRecurrent (P : TransitionMatrix) : Prop :=
  ∀ j : ℕ, P.returnProb j = 1

/-- The system is transient: every state is returned to with probability less than one,
`f_jj < 1` for all `j`. -/
def IsTransient (P : TransitionMatrix) : Prop :=
  ∀ j : ℕ, P.returnProb j < 1

/-- The mean first-passage time `μ_ij = ∑_{n ≥ 1} n f_ij^(n)` from state `i` to state `j`,
valued in `[0, ∞]`; for `i = j` it is the mean recurrence time `m_jj`. -/
noncomputable def meanFirstPassage (P : TransitionMatrix) (i j : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (P.firstPassage n i j)

end FosterQueues.MG1


