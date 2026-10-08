-- Prove2me | Definitions.Def_FosterQueues_GIM1_Model
-- name    : FosterQueues_GIM1_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:39:33.666612+00:00
-- url     : https://prove2.me/theorems/456fc521-d8f8-4200-910a-af040317f22b
-- title:
--   The GI/M/1 matrix of Foster §4 and ρ through ρ⁻¹ = Σ n aₙ in [0, ∞]
-- statement:
--   This file fixes the objects of §4 of Foster (1953), the imbedded Markov chain of the queueing system GI/M/1, on top of the published vocabulary of Markov chains on the states $\{0,1,2,\dots\}$ (transition matrices, first-passage probabilities, return probabilities).
--
--   1. **The GI/M/1 matrix.** Let $a = (a_n)_{n\ge 0}$ be a sequence of real numbers and put $\alpha_i = \sum_{j \ge i+1} a_j$. The associated matrix $[p_{ij}]$, with rows and columns indexed by $i, j = 0, 1, 2, \dots$, is
--   $$
--   [p_{ij}] = \begin{bmatrix} \alpha_0 & a_0 & 0 & 0 & \cdots \\ \alpha_1 & a_1 & a_0 & 0 & \cdots \\ \alpha_2 & a_2 & a_1 & a_0 & \cdots \\ \vdots & \vdots & \vdots & \vdots & \end{bmatrix},
--   $$
--   that is, $p_{i0} = \alpha_i$, $p_{ij} = a_{i+1-j}$ for $1 \le j \le i+1$, and $p_{ij} = 0$ for $j > i+1$. When every $a_n \ge 0$ and $\sum_n a_n = 1$, each row sums to $1$.
--
--   2. **The parameter $\rho$.** It is defined through its inverse,
--   $$
--   \rho^{-1} = \sum_{n=1}^{\infty} n\, a_n \in [0, \infty],
--   $$
--   and $\rho$ is the inverse of this quantity in $[0,\infty]$, with the conventions $\infty^{-1} = 0$ and $0^{-1} = \infty$. In particular an infinite mean $\sum n a_n = \infty$ gives $\rho = 0$.
--
--   Recurrence and transience of the system (the system is *recurrent* when every return probability $f_{jj}$ equals $1$, recurrent-null and recurrent-nonnull alike, and *transient* when every $f_{jj} < 1$) are not defined here: they are the shared definitions `FosterQueues.MG1.IsRecurrent` and `FosterQueues.MG1.IsTransient`, which this file imports.
--
--   These are the objects in terms of which Foster's classification of the GI/M/1 chain is stated: the system is ergodic if and only if $\rho < 1$, and recurrent if and only if $\rho \le 1$.
--
--   **Formalization Note** The matrix is a plain function of the sequence $a$; a theorem about it quantifies over transition matrices whose entries equal it. The column-0 entries are the tails $\alpha_i = \sum_{m \ge 0} a_{i+1+m}$ exactly as on the page (a real `tsum`, which is the tail whenever $a$ is summable). $\rho^{-1}$ and $\rho$ are extended nonnegative reals, never a real sum or a real inverse; the $n = 0$ term of the sum vanishes, so it is written from $n = 0$.
-- source:
--   Foster (Ann. Math. Statist. 24, 1953), §4, p. 359 (matrix, α_i, ρ⁻¹ ≡ Σ₁^∞ n aₙ)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_FosterQueues_MG1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

namespace FosterQueues.GIM1

/-- The transition matrix of the GI/M/1 imbedded chain (Foster 1953, §4, p. 359):
`p_{i0} = α_i = ∑_{j ≥ i+1} a_j`, `p_{ij} = a_{i+1-j}` for `1 ≤ j ≤ i + 1`, and `p_{ij} = 0` for
`j > i + 1`. States are indexed from `0`. -/
noncomputable def gim1Matrix (a : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if j = 0 then ∑' m : ℕ, a (i + 1 + m)
  else if j ≤ i + 1 then a (i + 1 - j) else 0

/-- `ρ⁻¹ = ∑_{n ≥ 1} n a_n` (§4, p. 359), as an extended nonnegative real (it may be `∞`). The
`n = 0` term vanishes, so the sum may start at `0`. -/
noncomputable def rhoInv (a : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (a n)

/-- The traffic parameter `ρ` of the GI/M/1 system, defined through its inverse:
`ρ = (∑_{n ≥ 1} n a_n)⁻¹` in `[0, ∞]` (`∞⁻¹ = 0`, `0⁻¹ = ∞`). -/
noncomputable def rho (a : ℕ → ℝ) : ℝ≥0∞ :=
  (rhoInv a)⁻¹

end FosterQueues.GIM1


